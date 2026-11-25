/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationColimitTransport
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationHomology
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationMate
/-! # Integral localization commutes with bounded qcqs derived pushforward -/

@[expose] public section

universe u v
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The unit of `LY ⊣ UY` followed by the pushed mate of a comparison `κ : H ⋙ UY ≅ UX ⋙ G` is
`G` applied to the unit of `LX ⊣ UX`. -/
theorem mate_unit_comap
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    (adjX : LX ⊣ UX) (adjY : LY ⊣ UY) {G : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ UY ≅ UX ⋙ G) (K : A) :
    adjY.unit.app (G.obj K) ≫
        (UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) ≫
          κ.hom.app (LX.obj K)) = G.map (adjX.unit.app K) := by
  have h := unit_mateEquiv_symm adjX adjY (TwoSquare.mk _ _ _ _ κ.inv) K
  change G.map (adjX.unit.app K) ≫ κ.inv.app (LX.obj K) =
    adjY.unit.app (G.obj K) ≫
      UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) at h
  have hh := congrArg (fun z ↦ z ≫ κ.hom.app (LX.obj K)) h.symm
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  exact hh.trans (Category.comp_id (G.map (adjX.unit.app K)))

/-- The zeroth legs of the localization-unit cocones of `adjY` at `G K` and of `G` applied to
that of `adjX` at `K` agree after a comparison `g` that is compatible with the units. -/
theorem localization_comparison_zero (ℓ : ℕ)
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    [UX.Additive] [UY.Additive] (adjX : LX ⊣ UX) (adjY : LY ⊣ UY)
    (G : A ⥤ C) [G.Additive] (K : A)
    [IsIso (ℓ • 𝟙 (LX.obj K))] [IsIso (ℓ • 𝟙 (LY.obj (G.obj K)))]
    (g : UY.obj (LY.obj (G.obj K)) ⟶ G.obj (UX.obj (LX.obj K)))
    (hg : adjY.unit.app (G.obj K) ≫ g = G.map (adjX.unit.app K)) :
    (scalarLocalizationUnitCocone ℓ adjY (G.obj K)).ι.app 0 ≫ g =
      ((Cocone.precompose (Mod.smulSequenceCompIso G K ℓ).inv).obj
        (G.mapCocone (scalarLocalizationUnitCocone ℓ adjX K))).ι.app 0 := by
  simp only [scalarLocalizationUnitCocone, Functor.comp_obj, Functor.const_obj_obj, pow_zero,
    End.one_asHom, CategoryTheory.Functor.map_id, Category.comp_id, Mod.smulSequenceCompIso,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Cocone.precompose_obj_pt, Functor.mapCocone_pt,
    Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app]
  change adjY.unit.app (G.obj K) ≫ g = 𝟙 _ ≫ G.map (adjX.unit.app K)
  exact hg.trans (Category.id_comp (G.map (adjX.unit.app K))).symm

private noncomputable def isColimit_mapCocone_precompose_whisker
    {I J A B C : Type*} [Category I] [Category J]
    [Category A] [Category B] [Category C]
    (p : I ⥤ J) {F : J ⥤ A} (G : A ⥤ B) (H : B ⥤ C)
    {F' : J ⥤ B} (σ : F ⋙ G ≅ F') (c : Cocone F)
    (hc : IsColimit ((G ⋙ H).mapCocone (c.whisker p))) :
    IsColimit (H.mapCocone
      (((Cocone.precompose σ.inv).obj (G.mapCocone c)).whisker p)) := by
  let e := Functor.isoWhiskerRight (Functor.isoWhiskerLeft p σ) H
  refine (IsColimit.precomposeHomEquiv e _) ?_
  apply hc.ofIsoColimit
  refine Cocone.ext (Iso.refl _) ?_
  intro j
  change H.map (G.map (c.ι.app (p.obj j))) ≫ 𝟙 _ =
    H.map (σ.hom.app (p.obj j)) ≫
      H.map (σ.inv.app (p.obj j) ≫ G.map (c.ι.app (p.obj j)))
  rw [Category.comp_id, ← H.map_comp, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

private theorem localization_mate_isIso (ℓ : ℕ)
    {A B C D T : Type*} [Category A] [Category B] [Category C] [Category D] [Category T]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    [UX.Additive] [UY.Additive] [UY.ReflectsIsomorphisms]
    (adjX : LX ⊣ UX) (adjY : LY ⊣ UY)
    {G : A ⥤ C} [G.Additive] {H : B ⥤ D} (κ : H ⋙ UY ≅ UX ⋙ G) (K : A)
    [IsIso (ℓ • 𝟙 (LX.obj K))] [IsIso (ℓ • 𝟙 (LY.obj (G.obj K)))]
    (P : ℤ → C ⥤ T)
    (hdetect : ∀ {M N : C} (z : M ⟶ N), (∀ q, IsIso ((P q).map z)) → IsIso z)
    (hX : ∀ q, Nonempty (IsColimit ((G ⋙ P q).mapCocone
      ((scalarLocalizationUnitCocone ℓ adjX K).whisker
        (ULift.orderIso : ULift.{v} ℕ ≃o ℕ).equivalence.functor))))
    (hY : ∀ q, Nonempty (IsColimit ((P q).mapCocone
      ((scalarLocalizationUnitCocone ℓ adjY (G.obj K)).whisker
        (ULift.orderIso : ULift.{v} ℕ ≃o ℕ).equivalence.functor)))) :
    IsIso ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) := by
  let β := (Adjunction.pushHomOfComapIso adjX adjY κ).app K
  let cX := scalarLocalizationUnitCocone ℓ adjX K
  let cY := scalarLocalizationUnitCocone ℓ adjY (G.obj K)
  let σ := Mod.smulSequenceCompIso G K ℓ
  let d := (Cocone.precompose σ.inv).obj (G.mapCocone cX)
  let g : cY.pt ⟶ d.pt := UY.map β ≫ κ.hom.app (LX.obj K)
  have : IsIso (ℓ • 𝟙 d.pt) := by
    have h : IsIso (G.map (UX.map (ℓ • 𝟙 (LX.obj K)))) := inferInstance
    change IsIso (ℓ • 𝟙 (G.obj (UX.obj (LX.obj K))))
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using h
  have hzero : cY.ι.app 0 ≫ g = d.ι.app 0 :=
    localization_comparison_zero ℓ adjX adjY G K g (mate_unit_comap adjX adjY κ K)
  have : IsIso g := hdetect g fun q ↦ by
    obtain ⟨hc⟩ := hY q
    obtain ⟨hd⟩ := hX q
    exact integralLocalization_cocone_map_isIso ℓ cY d g hzero (P q) hc
      (isColimit_mapCocone_precompose_whisker
        (ULift.orderIso : ULift.{v} ℕ ≃o ℕ).equivalence.functor G (P q) σ cX hd)
  have : IsIso (UY.map β) := by
    have heq : UY.map β = g ≫ κ.inv.app (LX.obj K) := by
      simp only [g, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id (UY.map β)).symm
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso β UY

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private lemma rightDerived_isGE
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (K : DerivedCategory C) (n : ℤ) (hK : K.IsGE n) :
    (F.rightDerivedFunctor.obj K).IsGE n := by
  let K' : DerivedCategory.Plus C := ⟨K, ⟨n, hK⟩⟩
  have hK' : K'.IsGE n := (K'.isGE_ι_obj_iff n).1 hK
  refine (DerivedCategory.isGE_iff _ n).2 fun q hq ↦ ?_
  exact (F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE K' n hq).of_iso
    ((DerivedCategory.homologyFunctor D q).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app K')).symm

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The specified scalar-extension/pushforward mate is invertible on integral bounded
constructible complexes for a qcqs map.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2.
(blueprint: lem-weil-pbc-continuous-integral-push-comparison).

Proof in words. Express the restricted regular E coefficient module as the sequential
colimit O --ℓ--> O --ℓ--> ..., with nth map a ↦ a/ℓⁿ. The compact-test localization
calculation and exact monoidal inverse image identify this colimit on every scheme.
Tensoring a complex with this coefficient module is therefore its localization telescope.
Exactness of filtered colimits and integralScalarExtension_exact identify derived scalar
extension with this termwise operation. Choose a good truncation of a representative of K
below its lower cohomological bound. Every term of its telescope has this same lower bound.
Apply condensed_qcqs_pushforward_continuity in every cohomological degree. It makes the
natural map from the telescope of Rf_*K to Rf_* of the telescope an isomorphism in every
degree. The map so obtained is the specified derivedPushHom: both are adjoint to the
restriction-of-scalars/pushforward comparison, and on the nth localization leg they are
induced by the same unit and division by ℓⁿ. Homology detects isomorphisms in the derived
category, and the exact faithful restriction functor reflects isomorphisms. No proper base
change theorem or completed pushforward is used. The zero complex and empty schemes give
the same zero-object comparison. -/
theorem integralScalarPushHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (K : integralConstructible ℓ E X) :
    IsIso ((derivedPushHom (integralScalarMap ℓ E) f).app K.obj) := by
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) := inferInstance
  let : Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) := inferInstance
  let a := integralScalarMap ℓ E
  let G := (lowerStar (integralCoeff ℓ E) f).rightDerivedFunctor
  let U := (Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap a Y)).mapDerivedCategory
  let LX := (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor
  let adjX := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let adjY := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)
  let κ := derivedComapLowerStarIso a f
  have : G.IsRightAdjoint :=
    (derivedUpperStarLowerStarAdjunction (integralCoeff ℓ E) f).isRightAdjoint
  have : PreservesBinaryBiproducts G :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : G.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have hK : DerivedCategory.TStructure.t.plus K.obj := K.property.1.1
  have hGK : DerivedCategory.TStructure.t.plus (G.obj K.obj) := by
    obtain ⟨n, hn⟩ := hK
    have : K.obj.IsGE n := hn
    exact ⟨n, rightDerived_isGE (lowerStar (integralCoeff ℓ E) f) K.obj n hn⟩
  have := derived_nsmul_isIso ℓ E X (LX.obj K.obj)
  have := derived_nsmul_isIso ℓ E Y
    ((Mod.extendScalars (coefficientMap a Y)).leftDerivedFunctor.obj (G.obj K.obj))
  have hU : U.ReflectsIsomorphisms := by
    let V := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (coefficientMap a Y)
    have : V.ReflectsIsomorphisms := by
      refine ⟨fun {M N} z hz ↦ ?_⟩
      have : IsIso z.hom := by
        change IsIso ((Mod.forget _).map (V.map z))
        infer_instance
      have : IsIso ((Mod.forget _).map z) := by
        change IsIso z.hom
        infer_instance
      exact isIso_of_reflects_iso z (Mod.forget _)
    refine ⟨fun z _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro q
    have : IsIso (V.map ((DerivedCategory.homologyFunctor _ q).map z)) :=
      (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso q) z).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ V
  apply localization_mate_isIso ℓ adjX adjY κ K.obj (DerivedCategory.homologyFunctor _)
  · intro M N z hz
    rw [DerivedCategory.isIso_iff]
    intro q
    exact hz q
  · exact integralLocalization_push_homology_isColimit ℓ E f K.obj hK
  · exact integralLocalization_homology_isColimit ℓ E Y (G.obj K.obj) hGK

end

end AlgebraicGeometry.ProEtale.CondensedRing
