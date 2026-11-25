/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The existence part of the valuative criterion is local at the target

Mathlib identifies `AlgebraicGeometry.ValuativeCriterion.Existence` with the universal
version of `SpecializingMap`, which is local at the target; we record the resulting
`IsZariskiLocalAtTarget` instance.

We also prove an affineness criterion for opens of universally closed schemes,
`AlgebraicGeometry.IsAffineOpen.of_universallyClosed`, by checking the valuative criterion for
the canonical map `U ⟶ Spec Γ(X, U)`.

Finally, every specialization `y' ⤳ y` in a scheme is the image of the specialization in
`Spec A` for a valuation ring `A` whose fraction field is the algebraic closure of `κ(y')`
(`AlgebraicGeometry.Scheme.exists_valuationSubring_of_specializes`).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

instance : IsZariskiLocalAtTarget ValuativeCriterion.Existence := by
  rw [ValuativeCriterion.Existence.eq]
  refine universally_isZariskiLocalAtTarget _ ?_
  intro X Y f ι U hU H
  exact IsZariskiLocalAtTarget.of_iSup_eq_top U hU H

/-- **An affineness criterion for opens of universally closed schemes.** Let `f : X ⟶ S` be
universally closed with `S` affine, let `D j` be finitely many affine opens covering `X`, and let
`U` be an open of `X` with `U ⊓ D j = D(a j)` for functions `a j` on `D j`. If there are
functions `g j` on `U` with `D(g j) ⊆ D j` and `g j * a j = 1` on `U ⊓ D j`, then `U` is affine.

The canonical map `U ⟶ Spec Γ(X, U)` satisfies the existence part of the valuative criterion:
the lift `Spec R ⟶ X` given by the valuative criterion for `f` sends the closed point into some
`D j`, hence lands in `D j`, and there `a j` becomes a unit, its inverse being the image of
`g j`; so it lands in `U`. Being quasi-compact, `U ⟶ Spec Γ(X, U)` is universally closed, and
it is dominant, hence surjective. As the `D(g j)` cover `U`, the `g j` then generate the unit
ideal of `Γ(X, U)`, and `D(g j) = D(a j)` is affine. -/
theorem IsAffineOpen.of_universallyClosed {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f]
    [IsAffine S] {ι : Type*} [Finite ι] (D : ι → X.Opens) (hD : ∀ j, IsAffineOpen (D j))
    (hcov : ⨆ j, D j = ⊤) (U : X.Opens) (a : ∀ j, Γ(X, D j))
    (ha : ∀ j, U ⊓ D j = X.basicOpen (a j)) (g : ι → Γ(X, U))
    (hg : ∀ j, X.basicOpen (g j) ≤ D j)
    (hag : ∀ j, X.presheaf.map (homOfLE inf_le_right : U ⊓ D j ⟶ D j).op (a j) *
      X.presheaf.map (homOfLE inf_le_left : U ⊓ D j ⟶ U).op (g j) = 1) :
    IsAffineOpen U := by
  classical
  have hUg (j : ι) : U ⊓ D j ≤ X.basicOpen (g j) := by
    have h := X.basicOpen_res (g j) (homOfLE inf_le_left : U ⊓ D j ⟶ U).op
    rw [Scheme.basicOpen_of_isUnit _
      (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans (hag j)))] at h
    rw [h]
    exact inf_le_right
  have hgD (j : ι) : X.basicOpen (g j) = U ⊓ D j :=
    le_antisymm (le_inf (X.basicOpen_le _) (hg j)) (hUg j)
  -- `U` is quasi-compact, being covered by the finitely many quasi-compact `D(a j)`.
  have hUcov : (U : Set X) = ⋃ j, (X.basicOpen (a j) : Set X) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov ▸ trivial : x ∈ ⨆ j, D j)
      exact Set.mem_iUnion.mpr ⟨j, by rw [← ha j]; exact ⟨hx, hj⟩⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      rw [← ha j] at hj
      exact hj.1
  have : CompactSpace U := by
    have h : IsCompact (U : Set X) := by
      rw [hUcov]
      exact isCompact_iUnion fun j ↦ ((hD j).basicOpen _).isCompact
    exact isCompact_iff_compactSpace.mp h
  have hf : ValuativeCriterion.Existence f := by
    have h := ‹UniversallyClosed f›
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  -- The structure morphism of `Spec Γ(X, U)` over `S`.
  let ψ : Spec Γ(X, U) ⟶ S :=
    Spec.map (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op) ≫ Spec.map f.appTop ≫ inv S.toSpecΓ
  have hψ : U.toSpecΓ ≫ ψ = U.ι ≫ f := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Scheme.toSpecΓ_naturality_assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have memU (x : U.toScheme) : U.ι x ∈ U := by
    change U.ι x ∈ (U : Set X)
    rw [← Scheme.Opens.range_ι U]
    exact ⟨x, rfl⟩
  have capp {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (x : Γ(C, ⊤)) :
      (p ≫ q).appTop x = p.appTop (q.appTop x) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  have nat {R T : CommRingCat.{u}} (φ : R ⟶ T) (x : R) :
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso T).inv (φ x) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) x).symm
  have hφ : ValuativeCriterion.Existence U.toSpecΓ := by
    rintro ⟨O, K, i₁, i₂, w⟩
    let ρ : Spec (.of K) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
    -- `ρ` is injective on global sections.
    have hρ : Function.Injective ρ.appTop := by
      have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O K))
      have h' : ρ.appTop = (Scheme.ΓSpecIso (.of O)).hom ≫
          CommRingCat.ofHom (algebraMap O K) ≫ (Scheme.ΓSpecIso (.of K)).inv := by
        rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]
      rw [h']
      exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).injective.comp
        (IsFractionRing.injective O K)).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of O)).hom).injective
    -- Lift along `f`.
    let Sq : ValuativeCommSq f := ⟨O, K, i₁ ≫ U.ι, i₂ ≫ ψ, ⟨by
      rw [Category.assoc, ← hψ, ← Category.assoc, w.w, Category.assoc]⟩⟩
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hf Sq).exists_lift
    change ρ ≫ l = i₁ ≫ U.ι at hl₁
    -- The closed point lands in some `D j`, hence so does all of `Spec O`.
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcov ▸ trivial : l (IsLocalRing.closedPoint O) ∈ ⨆ j, D j)
    have hlD : Set.range l ⊆ Set.range (D j).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint p).map l.continuous).mem_open (D j).isOpen hj
    let lj : Spec (.of O) ⟶ D j := IsOpenImmersion.lift (D j).ι l hlD
    have hlj : lj ≫ (D j).ι = l := IsOpenImmersion.lift_fac _ _ _
    -- The point of `Spec K` lands in `W = U ⊓ D j`.
    let W : X.Opens := U ⊓ D j
    have hκ : Set.range (i₁ ≫ U.ι) ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      refine ⟨by rw [Scheme.Hom.comp_apply]; exact memU _, ?_⟩
      rw [← hl₁, Scheme.Hom.comp_apply, ← hlj, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    let κ : Spec (.of K) ⟶ W := IsOpenImmersion.lift W.ι (i₁ ≫ U.ι) hκ
    have hκ₁ : κ ≫ X.homOfLE inf_le_left = i₁ := by
      rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι]
      exact IsOpenImmersion.lift_fac _ _ _
    have hκ₂ : κ ≫ X.homOfLE inf_le_right = ρ ≫ lj := by
      rw [← cancel_mono (D j).ι, Category.assoc, Scheme.homOfLE_ι, Category.assoc, hlj, hl₁]
      exact IsOpenImmersion.lift_fac _ _ _
    let n : Spec (.of K) ⟶ Spec Γ(X, W) := κ ≫ W.toSpecΓ
    let m : Spec (.of O) ⟶ Spec Γ(X, D j) := lj ≫ (D j).toSpecΓ
    have hm : ρ ≫ m = n ≫ Spec.map (X.presheaf.map (homOfLE inf_le_right : W ⟶ D j).op) := by
      simp only [m, n, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
      rw [← Category.assoc κ, hκ₂, Category.assoc]
    have hi₂ : ρ ≫ i₂ = n ≫ Spec.map (X.presheaf.map (homOfLE inf_le_left : W ⟶ U).op) := by
      simp only [n, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map]
      rw [← w.w, ← Category.assoc, hκ₁]
    -- The image of `a j` in `Γ(Spec O)` is a unit, with inverse the image of `g j`.
    have hunit : IsUnit (m.appTop ((Scheme.ΓSpecIso _).inv (a j))) := by
      refine IsUnit.of_mul_eq_one (i₂.appTop ((Scheme.ΓSpecIso _).inv (g j))) (hρ ?_)
      have e1 := congrArg (fun h ↦ h.appTop ((Scheme.ΓSpecIso _).inv (a j))) hm
      have e2 := congrArg (fun h ↦ h.appTop ((Scheme.ΓSpecIso _).inv (g j))) hi₂
      simp only [capp, nat] at e1 e2
      rw [map_mul, map_one, e1, e2, ← map_mul, ← map_mul, hag j, map_one, map_one]
    -- Hence `l` lands in `D(a j) ⊆ U`.
    have hlU : Set.range l ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      have hp : p ∈ m ⁻¹ᵁ (Spec Γ(X, D j)).basicOpen ((Scheme.ΓSpecIso _).inv (a j)) := by
        rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hunit]
        trivial
      rw [basicOpen_eq_of_affine] at hp
      change lj p ∈ (D j).toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (a j) at hp
      rw [Scheme.Opens.toSpecΓ_preimage_basicOpen] at hp
      have : l p ∈ X.basicOpen (a j) := by
        rw [← hlj, Scheme.Hom.comp_apply]
        exact hp
      rw [← ha j] at this
      exact this.1
    let l' : Spec (.of O) ⟶ U := IsOpenImmersion.lift U.ι l hlU
    have hl' : l' ≫ U.ι = l := IsOpenImmersion.lift_fac _ _ _
    have hl'₁ : ρ ≫ l' = i₁ := by
      rw [← cancel_mono U.ι, Category.assoc, hl', hl₁]
    refine ⟨⟨⟨l', hl'₁, ext_of_isAffine ?_⟩⟩⟩
    ext z
    apply hρ
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, ← Category.assoc, hl'₁, w.w]
  have : QuasiCompact U.toSpecΓ := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have : UniversallyClosed U.toSpecΓ := .of_valuativeCriterion _ hφ
  have : IsDominant U.toSpecΓ := by
    rw [Scheme.Opens.toSpecΓ]
    infer_instance
  have : Surjective U.toSpecΓ :=
    surjective_of_isDominant_of_isClosed_range _ U.toSpecΓ.isClosedMap.isClosed_range
  refine isAffineOpen_of_isAffineOpen_basicOpen U (Set.range g) ?_ ?_
  · by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨y, hy⟩ := U.toSpecΓ.surjective ⟨m, hm.isPrime⟩
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hcov ▸ trivial : U.ι y ∈ ⨆ j, D j)
    have hyU : U.ι y ∈ U := memU y
    have h1 : y ∈ U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (g j) := by
      rw [Scheme.Opens.toSpecΓ_preimage_basicOpen]
      exact hUg j ⟨hyU, hj⟩
    change U.toSpecΓ y ∈ PrimeSpectrum.basicOpen (g j) at h1
    rw [hy] at h1
    exact h1 (hle (Ideal.subset_span ⟨j, rfl⟩))
  · rintro _ ⟨j, rfl⟩
    rw [hgD, ha]
    exact (hD j).basicOpen _

section Specialization

open IsLocalRing

/-- **A specialization comes from a valuation ring.** If `y' ⤳ y` in a scheme `Y`, there are a
valuation ring `A` with fraction field the algebraic closure `Ω` of `κ(y')` and a morphism
`ρ : Spec A ⟶ Y` sending the closed point to `y` and whose restriction to `Spec Ω` is
`Spec Ω ⟶ Spec κ(y') ⟶ Y`. -/
lemma Scheme.exists_valuationSubring_of_specializes {Y : Scheme.{u}} {y' y : Y} (h : y' ⤳ y) :
    ∃ (A : ValuationSubring (AlgebraicClosure (Y.residueField y'))) (ρ : Spec (.of A) ⟶ Y),
      ρ (closedPoint A) = y ∧
      Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure (Y.residueField y')))) ≫ ρ =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y')
          (AlgebraicClosure (Y.residueField y')))) ≫ Y.fromSpecResidueField y' := by
  let φ : Y.presheaf.stalk y ⟶ .of (AlgebraicClosure (Y.residueField y')) :=
    Y.presheaf.stalkSpecializes h ≫ Y.residue y' ≫
      CommRingCat.ofHom (algebraMap (Y.residueField y') (AlgebraicClosure (Y.residueField y')))
  obtain ⟨A, hA, hA_local⟩ := IsLocalRing.exists_factor_valuationRing φ.hom
  let ψ : Y.presheaf.stalk y ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  refine ⟨A, Spec.map ψ ≫ Y.fromSpecStalk y, ?_, ?_⟩
  · have : Spec.map ψ (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
      IsLocalRing.comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
    rw [Scheme.Hom.comp_apply, this, Y.fromSpecStalk_closedPoint]
  · rw [Scheme.fromSpecResidueField, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl

end Specialization

end AlgebraicGeometry
