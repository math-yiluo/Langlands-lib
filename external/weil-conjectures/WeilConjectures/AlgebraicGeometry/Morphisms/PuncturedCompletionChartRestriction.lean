/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # Restriction to a punctured principal chart

## References

* Stacks Project, Tag 05ER, the natural comparison map on sections
* Stacks Project, Tag 05ER, the natural comparison Psi
* Tag 0BLH, affine charts
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The inverse image of a principal chart under the punctured comparison is the
original principal chart, and the induced map on matching sections is restriction
of their first projection. -/
theorem exists_matching_chart_restriction
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : A) :
    let V := (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    let P := pullback.fst
      (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop
    let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
    letI : Algebra A Γ(Y, V) :=
      ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp aY).toAlgebra
    letI : Algebra A Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) :=
      ((ψ.comp ρ).comp D.baseMap.hom).toAlgebra
    ∃ c : Γ(Y, V) ≃ₗ[A] Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤),
      ∀ z : D.matchingRing,
        ψ (ρ z) = c (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P z)) := by
  classical
  dsimp only
  let V := (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f
  let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)
  let T := D.puncturedMap ⁻¹ᵁ W
  have hT : T = V := by
    dsimp only [T, W, V]
    rw [← Hom.comp_preimage, D.puncturedMap_over, ← Hom.comp_preimage]
  let H : Γ(Y, V) ≅ Γ(T.toScheme, ⊤) :=
    Y.presheaf.mapIso (eqToIso hT).op ≪≫ T.topIso.symm
  let P := pullback.fst
    (pullback.fst q (completionSpecMap A ∣_ U)).appTop D.toCompleted.appTop
  have hP : (ΓSpecIso D.matchingRing).inv ≫ D.fromPunctured.appTop = P := by
    dsimp only [fromPunctured]
    rw [Hom.comp_appTop, toSpecΓ_appTop, ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have hp : D.puncturedMap ≫ (D.modelMap ⁻¹ᵁ U).ι = D.fromPunctured := by
    simp only [puncturedMap, Category.assoc, pullbackRestrictIsoRestrict_hom_ι,
      pullback.lift_fst]
  have hn : ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop) ≫
      (D.puncturedMap ∣_ W).appTop = P ≫ T.ι.appTop := by
    have hm : (D.puncturedMap ∣_ W) ≫ W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι =
        T.ι ≫ D.fromPunctured := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hp]
    erw [Category.assoc, ← Hom.comp_appTop, hm, Hom.comp_appTop,
      ← Category.assoc, hP]
  have ht : T.ι.appTop =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ H.hom := by
    dsimp only [H]
    simp only [Opens.ι_appTop, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Opens.topIso_inv, ← Functor.map_comp, ← Category.assoc]
    rfl
  let ρ := ((ΓSpecIso D.matchingRing).inv ≫
    (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
  let ψ := (D.puncturedMap ∣_ W).appTop.hom
  let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
  let res := (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom
  let : Algebra A Γ(Y, V) := (res.comp aY).toAlgebra
  let : Algebra A Γ(T.toScheme, ⊤) := ((ψ.comp ρ).comp D.baseMap.hom).toAlgebra
  have hz (z : D.matchingRing) : ψ (ρ z) = H.hom (res (P z)) := by
    have hh := hn
    rw [ht] at hh
    exact ConcreteCategory.congr_hom hh z
  have hbase : D.baseMap ≫ P = CommRingCat.ofHom aY := by
    simp only [baseMap, P, Category.assoc, pullback.lift_fst]
    rfl
  let c : Γ(Y, V) ≃ₗ[A] Γ(T.toScheme, ⊤) :=
    { H.commRingCatIsoToRingEquiv.toAddEquiv with
      map_smul' := fun a x ↦ by
        change H.hom (res (aY a) * x) = ψ (ρ (D.baseMap.hom a)) * H.hom x
        have hb : P (D.baseMap.hom a) = aY a := ConcreteCategory.congr_hom hbase a
        rw [map_mul, hz, hb] }
  exact ⟨c, hz⟩


end AlgebraicGeometry.Scheme.CompletionGluingData
