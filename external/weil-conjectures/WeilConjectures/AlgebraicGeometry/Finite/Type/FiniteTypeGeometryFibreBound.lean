/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties

/-!
# Finite-type ambient geometry and a uniform geometric-fibre dimension bound

Source: Stacks Project, Morphisms, Tag 0A3V, with the affine polynomial-presentation
refinement described in the DAG node (blueprint: lem-cbc-compactification-geometry-fibre-bound).
The refinement also uses Algebra Tags 00FN, 00KE and 00P3, Schemes Tag 01IJ,
and `MvPolynomial.ringKrullDim_of_isNoetherianRing`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem affine_dimension_bound {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (d : ℕ) (hd : topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞) := by
  let := f.appTop.hom.toAlgebra
  have hφ : Algebra.FiniteType Γ(Y, ⊤) Γ(X, ⊤) :=
    HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType).mp inferInstance
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hφ
  have heq (Z : Scheme.{u}) [IsAffine Z] :
      topologicalKrullDim Z = ringKrullDim Γ(Z, ⊤) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ Z.isoSpec.hom.homeomorph.isHomeomorph]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  rw [heq] at hd
  refine ⟨d + n, ?_⟩
  rw [heq]
  refine (ringKrullDim_le_of_surjective q.toRingHom hq).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
  calc
    ringKrullDim Γ(Y, ⊤) + (Nat.card (Fin n) : WithBot ℕ∞) ≤
        (d : WithBot ℕ∞) + n := by simpa [add_comm] using add_le_add_right hd n
    _ = ((d + n : ℕ) : WithBot ℕ∞) := by simp

private theorem finiteType_source_dimension_bound
    {T Y : Scheme.{u}} (p : T ⟶ Y) [LocallyOfFiniteType p]
    [CompactSpace T] [IsLocallyNoetherian Y]
    (hYDim : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞) := by
  classical
  obtain ⟨d, hd⟩ := hYDim
  have hlocal (x : T) : ∃ (U : T.Opens) (n : ℕ),
      x ∈ U ∧ topologicalKrullDim U ≤ (n : WithBot ℕ∞) := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hxV (p ⁻¹ᵁ V).isOpen
    let U : T.Opens := U
    let V : Y.Opens := V
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    have hdV : topologicalKrullDim V.toScheme ≤ (d : WithBot ℕ∞) :=
      (topologicalKrullDim_subspace_le Y V).trans hd
    obtain ⟨n, hn⟩ := affine_dimension_bound (p.resLE V U hUV) d hdV
    exact ⟨U, n, hxU, hn⟩
  choose U n hmem hdim using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set T)) (fun x ↦ (U x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hmem x⟩)
  refine ⟨s.sup n, topologicalKrullDim_le_of_iSup_eq_top
    (fun x : s ↦ U x) ?_ _ ?_⟩
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩
  · intro x
    exact (hdim x).trans (by exact_mod_cast Finset.le_sup (f := n) x.2)

/-- A finite-type morphism over a scheme with a finite Noetherian affine cover and finite
Krull dimension has the same source finiteness properties, a uniform dimension bound on all
geometric fibres, and preserves invertibility of integers in local rings.

Source: Stacks Project, Morphisms, Tag 0A3V and its affine-generator refinement; Algebra
Tags 00FN, 00KE and 00P3; Schemes Tag 01IJ
(blueprint: lem-cbc-compactification-geometry-fibre-bound).

Proof:
1. The finite Noetherian affine cover makes Y Noetherian. Finite type makes T locally
   Noetherian and quasi-compact. A finite affine subcover of T has Noetherian rings.
2. Around each point of T choose affine opens U and V with U contained in p⁻¹(V).
   The coordinate algebra of U is a quotient of a polynomial ring in finitely many
   variables over the Noetherian coordinate ring of V. The latter has dimension at
   most dim Y, by open-subspace monotonicity and the affine spectrum comparison.
   The polynomial dimension theorem and the quotient inequality give a natural
   dimension bound for U. Take a finite subcover, the maximum of its bounds, and
   apply the open-cover dimension lemma to bound dim T. An empty subcover has bound zero.
3. For any field-valued point, `topologicalKrullDim_pullback_le` bounds the pullback
   dimension by dim T. It factors the point through its residue field, uses dimension
   preservation under field extension, and compares the residue-field fibre with its
   underlying subspace of T. Thus the bound from step 2 works for every geometric fibre.
4. The stalk map of p takes an inverse of an integer to an inverse of that integer.
   The source cover, dimension bound and stalk assertion include the empty source. -/
theorem finiteType_noetherianCover_dimension_geometricFibres
    {T Y : Scheme.{u}} (p : T ⟶ Y) [LocallyOfFiniteType p] [QuasiCompact p]
    (hYCover : ∃ (n : ℕ) (U : Fin n → Y.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(Y, (U i).1))
    (hYDim : ∃ d : ℕ, topologicalKrullDim Y ≤ (d : WithBot ℕ∞)) :
    (∃ (n : ℕ) (U : Fin n → T.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(T, (U i).1)) ∧
    (∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞)) ∧
    (∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (h : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (↑(pullback p h) : Type u) ≤ (e : WithBot ℕ∞)) ∧
    ∀ N : ℤ, (∀ y : Y, IsUnit (N : Y.presheaf.stalk y)) →
      ∀ t : T, IsUnit (N : T.presheaf.stalk t) := by
  classical
  obtain ⟨n, U, hU, hUN⟩ := hYCover
  have : IsNoetherian Y := (isNoetherian_iff_of_finite_iSup_eq_top hU).mpr hUN
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace p
  have hTCover : ∃ (n : ℕ) (U : Fin n → T.affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(T, (U i).1) := by
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun V : T.affineOpens ↦ (V : Set T)) (fun V ↦ V.1.isOpen) fun x _ ↦ by
        obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
          T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩
    let e := s.equivFin
    refine ⟨s.card, fun i ↦ (e.symm i).1, ?_, ?_⟩
    · refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e ⟨V, hV⟩, by simpa using hxV⟩
    · intro i
      exact IsLocallyNoetherian.component_noetherian _
  obtain ⟨d, hd⟩ := finiteType_source_dimension_bound p hYDim
  refine ⟨hTCover, ⟨d, hd⟩, ⟨d, ?_⟩, ?_⟩
  · intro Ω _ _ h
    exact (topologicalKrullDim_pullback_le p h).trans hd
  · intro N hN t
    simpa using (hN (p t)).map (p.stalkMap t).hom

end AlgebraicGeometry
