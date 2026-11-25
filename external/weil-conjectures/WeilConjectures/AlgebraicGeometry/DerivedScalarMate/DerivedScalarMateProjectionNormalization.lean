/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarPullbackTensorNormalization

/-! # Projection normalization of the scalar mate

Source: Stacks Project, Tags 03EL, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-derived-scalar-projection-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

/-- The normalized scalar mate restricts to the specified projection arrow.
Source: Stacks 03EL, 06YY, 07A4, 07A6; steps 2--3 of the scalar-mate argument
(blueprint: lem-sfb-derived-scalar-projection-normalization).
Proof: resolve the input and the coefficient by flat K-flat complexes. The ordinary
scalar/pullback comparison and the tensor/pullback comparison send a pure tensor
s tensor x to pullback(x) tensor pullback(s). The normalized scalar adjunction fixes
the inverse mate to be this comparison. Tensor generation proves equality of chain
maps, and resolving localization proves it for every derived input. Apply the
adjunction-compatible restriction/direct-image comparison to the adjunct of beta.
Naturality of the normalized tensor identification at the geometric counit changes
this adjunct to the pullback tensor comparison followed by counit tensor identity.
This is the defining adjunct of the projection arrow. Injectivity of the geometric
adjunction bijection gives the displayed equation with exactly sourceIso and targetIso.
Resolving the coefficient is valid without its flatness because the first factor is
K-flat; no projection-formula invertibility is used. -/
theorem scalarMate_projection_normalization
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A)) :
    (∀ K : DerivedCategory (proEtaleRingModules Z (inverseRing f A)),
      (sourceIso f a t).inv.app K ≫
        (restriction a).mapDerivedCategory.map ((beta f a).app K) ≫
        (targetIso f a z).hom.app K =
      proEtaleProjectionFormulaMate f A (inverseRing f A) (Iso.refl _) t z K
        (DerivedCategory.Q.obj (coefficientComplex a))) := by
  intro K
  let U := pull f A
  let R := push f A
  let E := proEtaleRingDerivedExtension a
  let F := proEtaleRingDerivedExtension (inverseMap f a)
  let rT := (restriction a).mapDerivedCategory
  let rZ := (restriction (inverseMap f a)).mapDerivedCategory
  let b := proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  let d := restrictionPush f a
  let eT := derivedTensorIso a t
  let eZ := derivedTensorIso (inverseMap f a) z ≪≫
    (Functor.curryObj z.tensor).flip.mapIso (derivedCoefficientPullback f a).symm
  let μ := proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z
  let q := (scalarPullback f a).hom.app (R.obj K) ≫ F.map ((adjunction f A).counit.app K)
  have hq : (adjunction f B).homEquiv _ _ q = (beta f a).app K := by
    apply ((adjunction f B).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact (mateEquiv_counit (adjunction f A) (adjunction f B)
      (scalarPullback f a).hom K).symm
  have hr := (proEtaleRingSheafChangeAdjunction f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).2.2 (E.obj (R.obj K)) (F.obj K) q
  change (adjunction f A).homEquiv _ _
      (b.inv.app (E.obj (R.obj K)) ≫ rZ.map q) =
    rT.map ((adjunction f B).homEquiv _ _ q) ≫ d.hom.app (F.obj K) at hr
  rw [hq] at hr
  have hr' : ((adjunction f A).homEquiv _ _).symm
      (rT.map ((beta f a).app K) ≫ d.hom.app (F.obj K)) =
      b.inv.app (E.obj (R.obj K)) ≫ rZ.map ((scalarPullback f a).hom.app (R.obj K)) ≫
        (F ⋙ rZ).map ((adjunction f A).counit.app K) := by
    rw [← hr]
    calc
      _ = b.inv.app (E.obj (R.obj K)) ≫ rZ.map q :=
        ((adjunction f A).homEquiv _ _).symm_apply_apply _
      _ = _ := by simp only [q, Functor.map_comp, Functor.comp_map]
  have hn := eZ.hom.naturality ((adjunction f A).counit.app K)
  have hμ := scalarPullback_tensor_normalization f a t z (R.obj K)
  change b.inv.app (E.obj (R.obj K)) ≫
      rZ.map ((scalarPullback f a).hom.app (R.obj K)) ≫ eZ.hom.app (U.obj (R.obj K)) =
      U.map (eT.hom.app (R.obj K)) ≫ μ.hom.app
        (R.obj K, DerivedCategory.Q.obj (coefficientComplex a)) at hμ
  have hs : (sourceIso f a t).inv.app K = eT.inv.app (R.obj K) := by
    simp only [sourceIso, Iso.trans_inv, NatTrans.comp_app,
      Functor.associator_inv_app, Category.comp_id]
    rfl
  have ht : (targetIso f a z).hom.app K =
      d.hom.app (F.obj K) ≫ R.map (eZ.hom.app K) := by
    simp only [targetIso, eZ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.map_comp, Category.id_comp]
    rfl
  rw [hs, ht]
  change eT.inv.app (R.obj K) ≫ rT.map ((beta f a).app K) ≫
    (d.hom.app (F.obj K) ≫ R.map (eZ.hom.app K)) = _
  apply ((adjunction f A).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
  erw [hr']
  change (F ⋙ rZ).map ((adjunction f A).counit.app K) ≫ eZ.hom.app K =
    eZ.hom.app (U.obj (R.obj K)) ≫
      z.tensor.map (Prod.mkHom ((adjunction f A).counit.app K) (𝟙 _)) at hn
  rw [Category.assoc, Category.assoc, hn, reassoc_of% hμ]
  change U.map (eT.inv.app (R.obj K)) ≫
    U.map (eT.hom.app (R.obj K)) ≫ μ.hom.app
      (R.obj K, DerivedCategory.Q.obj (coefficientComplex a)) ≫
    z.tensor.map (Prod.mkHom ((adjunction f A).counit.app K) (𝟙 _)) = _
  rw [← U.map_comp_assoc, eT.inv_hom_id_app, U.map_id, Category.id_comp]
  symm
  unfold proEtaleProjectionFormulaMate derivedProjectionFormulaMate
  erw [Adjunction.homEquiv_symm_rightAdjointProjectionMap_app_app]
  change (μ.hom.app (R.obj K, DerivedCategory.Q.obj (coefficientComplex a)) ≫ 𝟙 _) ≫
    z.tensor.map (Prod.mkHom ((adjunction f A).counit.app K) (𝟙 _)) = _
  rw [Category.comp_id]

end AlgebraicGeometry.Scheme.DerivedScalarMate
