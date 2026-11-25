/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.PositiveTensorFamily
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor sections and affine nonvanishing loci

Source: Stacks Project, Varieties Lemma 09NC, proof, invoking Properties Lemma 01PV
(blueprint: lem-sc-tensor-section-affine-open).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

private theorem nonvanishing_iff_residueValue_ne_zero {X : Scheme.{u}}
    (M : X.Modules) (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus M s ↔ residueValue s x trivial ≠ 0 := by
  have hz : residueValue s x trivial = 0 ↔
      M.presheaf.germ ⊤ x trivial s ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x)) := by
    change (1 : IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗ₜ[X.presheaf.stalk x]
      M.presheaf.germ ⊤ x trivial s = 0 ↔ _
    rw [← (TensorProduct.quotTensorEquivQuotSMul
      ↑(M.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).map_eq_zero_iff]
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  exact not_congr hz.symm

private theorem tmul_ne_zero_iff {K A B : Type u} [Field K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] (a : A) (b : B) :
    a ⊗ₜ[K] b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro ha
      exact h (by simp [ha])
    · intro hb
      exact h (by simp [hb])
  · rintro ⟨ha, hb⟩
    have hA : LinearIndependent K (fun _ : Unit ↦ a) :=
      (linearIndependent_unique_iff).2 ha
    have hB : LinearIndependent K (fun _ : Unit ↦ b) :=
      (linearIndependent_unique_iff).2 hb
    exact (hA.tmul_of_flat_left hB).ne_zero ((), ())

set_option backward.isDefEq.respectTransparency false in
private theorem nonvanishing_tmul {X : Scheme.{u}} (M N : X.Modules)
    [M.IsInvertible] [N.IsInvertible] (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) :
    nonvanishingLocus (M ⊗ N) (tmulSection s t) =
      nonvanishingLocus M s ∩ nonvanishingLocus N t := by
  ext x
  rw [Set.mem_inter_iff, nonvanishing_iff_residueValue_ne_zero,
    nonvanishing_iff_residueValue_ne_zero, nonvanishing_iff_residueValue_ne_zero]
  obtain ⟨e, he⟩ := (invertible_pullback_tensor (𝟙 X)).2.2.2.2.2.2.2 M N x
  have hinj : Function.Injective e.hom :=
    (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have hz : e.hom.hom (residueValue (tmulSection s t) x trivial) = 0 ↔
      residueValue (tmulSection s t) x trivial = 0 := map_eq_zero_iff e.hom.hom hinj
  refine (not_congr hz).symm.trans ?_
  rw [he ⊤ trivial s t]
  exact tmul_ne_zero_iff _ _

private theorem positiveTensorFamily_invertible {X : Scheme.{u}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) [∀ i, (L i).IsInvertible] :
    (positiveTensorFamily n L).IsInvertible := by
  induction n with
  | zero => exact inferInstanceAs (L 0).IsInvertible
  | succ n ih =>
    have := ih (fun i ↦ L i.castSucc)
    change (positiveTensorFamily n (fun i ↦ L i.castSucc) ⊗ L (Fin.last (n + 1))).IsInvertible
    exact (invertible_pullback_tensor (𝟙 X)).2.1 _ _

private theorem positiveTensorFamily_locus {X : Scheme.{u}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) [∀ i, (L i).IsInvertible]
    (t : (i : Fin (n + 1)) → (L i).sections) :
    nonvanishingLocus (positiveTensorFamily n L)
        ((positiveTensorFamilySection n L t).val (Opposite.op ⊤)) =
      ⋂ i, nonvanishingLocus (L i) ((t i).val (Opposite.op ⊤)) := by
  induction n with
  | zero =>
    ext x
    simp [positiveTensorFamily, positiveTensorFamilySection]
  | succ n ih =>
    have := positiveTensorFamily_invertible n (fun i ↦ L i.castSucc)
    change nonvanishingLocus
      (positiveTensorFamily n (fun i ↦ L i.castSucc) ⊗ L (Fin.last (n + 1)))
      (tmulSection
        ((positiveTensorFamilySection n (fun i ↦ L i.castSucc)
          (fun i ↦ t i.castSucc)).val (Opposite.op ⊤))
        ((t (Fin.last (n + 1))).val (Opposite.op ⊤))) = _
    rw [nonvanishing_tmul, ih]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h, hlast⟩ i
      exact Fin.lastCases hlast h i
    · intro h
      exact ⟨fun i ↦ h i.castSucc, h (Fin.last (n + 1))⟩

private theorem affine_finite_intersection {X : Scheme.{u}} {ι : Type*}
    (L : ι → X.Modules) [∀ i, (L i).IsInvertible]
    (t : (i : ι) → (L i).sections) (U : X.Opens) (hU : IsAffineOpen U)
    (a : Finset ι) :
    ∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X,
      x ∈ V ↔ x ∈ U ∧ ∀ i ∈ a, x ∈ nonvanishingLocus (L i)
        ((t i).val (Opposite.op ⊤)) := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    exact ⟨U, hU, fun x ↦ by simp⟩
  | @insert i a hi ih =>
    obtain ⟨W, hW, heq⟩ := ih
    obtain ⟨V, hV, hloc⟩ :=
      (affine_cap_section_open X (L i) ((t i).val (Opposite.op ⊤)) W hW).1
    refine ⟨V, hV, fun x ↦ ?_⟩
    change ∀ x : X, x ∈ V ↔ x ∈ W ∧ x ∈ nonvanishingLocus (L i)
      ((t i).val (Opposite.op ⊤)) at hloc
    rw [hloc x, heq x]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    tauto

/-- The tensor section `τ = t₀ ⊗ ⋯ ⊗ tₙ` of a nonempty finite family of invertible modules
(the landed left-associated `positiveTensorFamily` with its section
`positiveTensorFamilySection`, def-sc-positive-tensor-family; `n` means `n + 1` factors)
has nonvanishing locus equal to the intersection of the factor loci. If one factor locus is
affine, so is this intersection.

Source: Stacks Project, Varieties Lemma 09NC, proof, invoking Properties Lemma 01PV
(blueprint: lem-sc-tensor-section-affine-open).

Proof:
1. The quotient-tensor equivalence identifies a zero residue-field value with a germ
   in the maximal ideal times the stalk module, so a nonzero value is precisely
   membership in the nonvanishing locus. By `lem-weil-pbc-invertible-pullback-tensor`,
   each tensor product is invertible and its fibre section is the pure tensor of the
   factor values. Singleton nonzero vector families are linearly independent, and
   tensoring them preserves linear independence over a field. Thus a pure tensor is
   nonzero exactly when both factors are nonzero. Induction on the number of factors
   gives the equality.
2. If the `j`-th factor locus is affine, start with that affine open and intersect
   successively with every remaining factor locus. At each step apply
   `lem-sc-affine-cap-section-open` to the invertible factor and its section.
   The resulting affine open is the tensor section locus by step 1.
-/
theorem tensor_section_affine_open {X : Scheme.{u}} (n : ℕ)
    (L : Fin (n + 1) → X.Modules) [∀ i, (L i).IsInvertible]
    (t : (i : Fin (n + 1)) → (L i).sections) :
    (nonvanishingLocus (positiveTensorFamily n L)
        ((positiveTensorFamilySection n L t).val (Opposite.op ⊤)) =
      ⋂ i, nonvanishingLocus (L i) ((t i).val (Opposite.op ⊤))) ∧
    ((∃ j : Fin (n + 1), ∃ U : X.Opens, IsAffineOpen U ∧
        (U : Set X) = nonvanishingLocus (L j) ((t j).val (Opposite.op ⊤))) →
      ∃ U : X.Opens, IsAffineOpen U ∧
        (U : Set X) = nonvanishingLocus (positiveTensorFamily n L)
          ((positiveTensorFamilySection n L t).val (Opposite.op ⊤))) := by
  classical
  have hloc := positiveTensorFamily_locus n L t
  refine ⟨hloc, ?_⟩
  rintro ⟨j, U, hU, hset⟩
  obtain ⟨V, hV, hVset⟩ := affine_finite_intersection L t U hU Finset.univ
  refine ⟨V, hV, ?_⟩
  rw [hloc]
  ext x
  simp only [Set.mem_iInter]
  refine (hVset x).trans ?_
  simp only [Finset.mem_univ, forall_const]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨show x ∈ (U : Set X) from hset.symm ▸ h j, h⟩

end AlgebraicGeometry.Scheme.Modules
