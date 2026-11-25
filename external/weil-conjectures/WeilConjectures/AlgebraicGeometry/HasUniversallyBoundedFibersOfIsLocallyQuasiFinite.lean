/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
import Mathlib.Algebra.Module.SpanRankOperations
import WeilConjectures.AlgebraicGeometry.BoundsFiberDegreesComp
import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverDegreeSum
import WeilConjectures.AlgebraicGeometry.ImmersionFiberDegreeOne
import WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAffineOpenInFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite

/-!
# Universally bounded fibres from a quasi-compact source

Source: Stacks Project, Morphisms, Lemma Tag 03JA and Definition Tag 03J4
(blueprint: lem-weil-pbc-lqf-qc-source-bounded-fibres).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The generator bound in the last paragraph of Stacks Tag 03JA. -/
private theorem finite_spec_bound {Z : Scheme.{u}} {R : CommRingCat.{u}}
    (g : Z ⟶ Spec R) [IsFinite g] : HasUniversallyBoundedFibers g := by
  classical
  let A := Γ(Z, ⊤)
  let := g.ΓAlgebra
  have : Module.Finite R A := by
    rw [← RingHom.finite_algebraMap]
    change (((Scheme.ΓSpecIso R).inv ≫ g.appTop).hom).Finite
    rw [CommRingCat.hom_comp, RingHom.finite_respectsIso.cancel_left_isIso]
    exact g.finite_appTop
  refine ⟨(⊤ : Submodule R A).spanFinrank, fun y ↦ ⟨inferInstance, ?_⟩⟩
  let := (g.fiberToSpecResidueField y).ΓAlgebra
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec R).fromSpecResidueField y)
  let := φ.hom.toAlgebra
  have : IsAffine Z := isAffine_of_isAffineHom g
  obtain ⟨e⟩ := nonempty_algEquiv_tensorProduct_Γ_of_isPullback
    (iX := g) (iY := g.fiberToSpecResidueField y) φ
    (by rw [hφ]; exact IsPullback.of_hasPullback g ((Spec R).fromSpecResidueField y))
  change Module.finrank ((Spec R).residueField y) Γ(g.fiber y, ⊤) ≤ _
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_eq_spanFinrank_of_free]
  have h := (Module.Finite.fg_top (R := R) (M := A)).spanFinrank_baseChange_le
    (A := (Spec R).residueField y)
  simpa only [Submodule.baseChange_top] using h

/-- Transport the finite affine case along the target's affine-chart isomorphism. -/
private theorem finite_affine_bound {Z V : Scheme.{u}} [IsAffine V]
    (g : Z ⟶ V) [IsFinite g] : HasUniversallyBoundedFibers g := by
  have h := finite_spec_bound (g ≫ V.isoSpec.hom)
  have h' := hasUniversallyBoundedFibers_comp (g ≫ V.isoSpec.hom) V.isoSpec.inv h
    (immersion_fiber_degree_one V.isoSpec.inv).2.2
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'

/-- Pull the cover back to each fibre, then apply the degree-sum estimate of Tag 03JA. -/
private theorem bounds_of_open_cover {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : ℕ) (U : Fin m → X.Opens) (n : Fin m → ℕ)
    (hcover : ⨆ i, U i = ⊤)
    (hbound : ∀ i, BoundsFiberDegrees ((U i).ι ≫ f) (n i)) :
    BoundsFiberDegrees f (∑ i, n i) := by
  intro y
  let W (i : Fin m) := f.fiberι y ⁻¹ᵁ U i
  have hW : ⨆ i, W i = ⊤ := by
    change ⨆ i, f.fiberι y ⁻¹ᵁ U i = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcover]
    simp
  have H (i : Fin m) := (isPullback_morphismRestrict (f.fiberι y) (U i)).paste_vert
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))
  have he (i : Fin m) :
      (W i).ι ≫ f.fiberToSpecResidueField y =
        (H i).isoPullback.hom ≫ ((U i).ι ≫ f).fiberToSpecResidueField y :=
    (H i).isoPullback_hom_snd.symm
  apply finite_open_cover_degree_sum (f.fiberToSpecResidueField y) m W n hW
  · intro i
    rw [he]
    let := (hbound i y).1
    infer_instance
  · intro i
    have hrank := finrankΓ_eq_of_iso ((W i).ι ≫ f.fiberToSpecResidueField y)
      (((U i).ι ≫ f).fiberToSpecResidueField y) (H i).isoPullback (Iso.refl _) (by
        simpa using (he i).symm)
    rw [hrank]
    exact (hbound i y).2

/-- A locally quasi-finite morphism whose source is quasi-compact has a single nonnegative
bound on the degrees of all its finite scheme-theoretic fibres.
Source: Stacks Project, Morphisms, Lemma Tag 03JA and Definition Tag 03J4
(blueprint: lem-weil-pbc-lqf-qc-source-bounded-fibres).

Proof outline, following the six steps of the node:
1. Choose a finite affine open cover `Uᵢ` of `X` and affine opens `Vᵢ` of `Y` with
   `f(Uᵢ) ⊆ Vᵢ`, using quasi-compactness and `lem-weil-pbc-affine-opens-basis`.
2. Each restriction `Uᵢ → Vᵢ` is locally quasi-finite by
   `lem-weil-pbc-lqf-restriction-to-opens`. It is affine, hence quasi-compact by
   `lem-weil-pbc-affine-morphism-permanence`, and therefore quasi-finite by
   `pqf-lem-qf-locqf-qc`.
3. For a finite morphism `Z → Spec A`, its section ring `B` is a finite `A`-module.
   The affine pullback section isomorphism identifies each fibre's section algebra with
   `κ(y) ⊗[A] B`. Mathlib's `Submodule.FG.spanFinrank_baseChange_le` bounds its dimension
   by the minimal number of generators of `B`. Transport this bound along the target's
   affine-chart isomorphism to handle any finite morphism with affine target.
4. Factor each quasi-finite affine restriction as an open immersion into a finite affine
   scheme over `Vᵢ`, by `lem-weil-pbc-quasi-finite-affine-open-in-finite`. Use
   `lem-weil-pbc-immersion-fibre-degree-one` and
   `lem-weil-pbc-composition-fibre-degree-bound` to bound the restriction. Compose once
   more with the open immersion `Vᵢ → Y` to bound `Uᵢ → Y` without changing residue fields.
5. Pull the open cover back along `f.fiberι y`. The resulting opens cover the fibre.
   Paste `isPullback_morphismRestrict` with the square defining the fibre to identify
   each open, over `Spec κ(y)`, with the fibre of `Uᵢ → Y`. The pullback isomorphism
   preserves finiteness and `finrankΓ`.
6. Apply `lem-weil-pbc-finite-open-cover-degree-sum` to obtain finiteness of the fibre and
   the bound `∑ nᵢ`. This also handles the empty cover. The sum therefore witnesses
   `HasUniversallyBoundedFibers` as defined in `def-weil-pbc-fibre-degree-bound`. -/
theorem hasUniversallyBoundedFibers_of_isLocallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (hf : IsLocallyQuasiFinite f) : HasUniversallyBoundedFibers f := by
  classical
  have hx (x : X) : ∃ (U : X.Opens) (V : Y.Opens),
      IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := Y) (x := f x) (U := ⊤) (by trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := x) (U := f ⁻¹ᵁ V) hxV
    exact ⟨U, V, hU, hV, hxU, hUV⟩
  choose U V hU hV hxU hUV using hx
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let e := s.equivFin.symm
  let W (i : Fin s.card) := U (e i)
  have hW : ⨆ i, W i = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨j, hjs, hxj⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨s.equivFin ⟨j, hjs⟩, by simpa [W, e] using hxj⟩
  have hb (i : Fin s.card) : HasUniversallyBoundedFibers ((W i).ι ≫ f) := by
    let x := (e i).val
    have : IsAffine (U x).toScheme := hU x
    have : IsAffine (V x).toScheme := hV x
    let g := f.resLE (V x) (U x) (hUV x)
    have hq : IsQuasiFinite g :=
      (isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact g).mpr
        ⟨isLocallyQuasiFinite_resLE f hf (U x) (V x) (hUV x), inferInstance⟩
    obtain ⟨Z, j, π, _, hj, hπ, hfac⟩ :=
      exists_isOpenImmersion_isFinite_of_isQuasiFinite_affine g hq
    let := hj
    let := hπ
    have hg : HasUniversallyBoundedFibers g := by
      rw [hfac]
      exact hasUniversallyBoundedFibers_comp j π
        (immersion_fiber_degree_one j).2.2 (finite_affine_bound π)
    have h := hasUniversallyBoundedFibers_comp g (V x).ι hg
      (immersion_fiber_degree_one (V x).ι).2.2
    simpa only [g, resLE_comp_ι] using h
  choose n hn using hb
  exact ⟨∑ i, n i, bounds_of_open_cover f s.card W n hW hn⟩

end AlgebraicGeometry.Scheme.Hom
