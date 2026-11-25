/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCocycle
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCocycle
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory

/-! # Derived coherence of the normalized ordinary derived square

The normalized derived ordinary square satisfies the cocycle equation with the derived
ordinary balancing and the ambient PBC associator, on every object of the derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace WeilConjectures.FdIntegralScalarForward

section Abstract

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Natural transformations agreeing on the image of an essentially surjective functor agree. -/
theorem app_eq_of_essSurj {C : Type u₁} {D : Type u₂} {A : Type u₃} [Category.{v₁} C]
    [Category.{v₂} D] [Category.{v₃} A] (Q : C ⥤ D) [Q.EssSurj] {F G : D ⥤ A}
    (α β : F ⟶ G) (h : ∀ P, α.app (Q.obj P) = β.app (Q.obj P)) (Y : D) :
    α.app Y = β.app Y := by
  let i := Q.objObjPreimageIso Y
  have hα := α.naturality i.hom
  have hβ := β.naturality i.hom
  rw [h] at hα
  rw [← cancel_epi (F.map i.hom), hα, hβ]

end Abstract

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u})

set_option hygiene false in
local notation "𝒪 " h:max => integralOrdinaryScalar l (pbcFiniteField.{u} l Ω _)
  (pbcFiniteField.{u} l Ω _) (pbcFiniteFieldInclusion l Ω h) T

set_option hygiene false in
local notation "𝓉 " E:max => fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T

set_option hygiene false in
local notation "𝒳 " h:max => pbcExtend (pbcCompletedScalarMap l Ω T h)

/-- The derived ordinary coefficient square normalized by the counit on representatives. -/
private def eD {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h) :
    integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
        (pbcFiniteFieldInclusion l Ω h) T ⋙
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω L) ≅
    integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
      pbcAmbientScalarExtension l Ω T h :=
  (FdIntegralOrdinaryScalarModel.ordinaryTransportSquare l Ω T h o).choose

private theorem eD_fac {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    (eD l Ω T h o).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((𝓉 E).mapHomologicalComplex (.up ℤ)).obj P) =
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((𝒪 h).mapDerivedCategoryFactors.hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        (((𝒪 h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T h o).hom.app P) :=
  (FdIntegralOrdinaryScalarModel.ordinaryTransportSquare l Ω T h o).choose_spec.2 P

private theorem eD_heh {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (o : FdOrdinaryScalarTransport l Ω T h)
    (P : CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) T) ℤ) :
    (eD l Ω T h o).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P) ≫
      (pbcCounitNT (pbcCompletedScalarMap l Ω T h)).app
        (((𝓉 E).mapHomologicalComplex (.up ℤ)).obj P) =
    (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((𝒪 h).mapDerivedCategoryFactors.hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        (((𝒪 h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T h o).hom.app P) := by
  rw [pbcCounitNT_app]
  exact eD_fac l Ω T h o P

section Abstract

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇

theorem cocycle_of_essSurj {C : Type u₇} {DE : Type u₁} {DL : Type u₂} {DM : Type u₃}
    {EE : Type u₄} {EL : Type u₅} {EM : Type u₆} [Category.{v₇} C] [Category.{v₁} DE]
    [Category.{v₂} DL] [Category.{v₃} DM] [Category.{v₄} EE] [Category.{v₅} EL]
    [Category.{v₆} EM] (Q : C ⥤ DE) [Q.EssSurj]
    (Oh : DE ⥤ DL) (Ok : DL ⥤ DM) (Ohk : DE ⥤ DM)
    (TE : DE ⥤ EE) (TL : DL ⥤ EL) (TM : DM ⥤ EM)
    (Xh : EE ⥤ EL) (Xk : EL ⥤ EM) (Xhk : EE ⥤ EM)
    (eh : Oh ⋙ TL ≅ TE ⋙ Xh) (ek : Ok ⋙ TM ≅ TL ⋙ Xk) (ehk : Ohk ⋙ TM ≅ TE ⋙ Xhk)
    (Oc : Oh ⋙ Ok ≅ Ohk) (A : Xh ⋙ Xk ≅ Xhk)
    (h : ∀ P, TM.map (Oc.hom.app (Q.obj P)) ≫ ehk.hom.app (Q.obj P) =
      ek.hom.app (Oh.obj (Q.obj P)) ≫ Xk.map (eh.hom.app (Q.obj P)) ≫
        A.hom.app (TE.obj (Q.obj P))) (Y : DE) :
    TM.map (Oc.hom.app Y) ≫ ehk.hom.app Y =
      ek.hom.app (Oh.obj Y) ≫ Xk.map (eh.hom.app Y) ≫ A.hom.app (TE.obj Y) := by
  let α : (Oh ⋙ Ok) ⋙ TM ⟶ TE ⋙ Xhk := Functor.whiskerRight Oc.hom TM ≫ ehk.hom
  let β : (Oh ⋙ Ok) ⋙ TM ⟶ TE ⋙ Xhk :=
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Oh ek.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eh.hom Xk ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft TE A.hom
  have := app_eq_of_essSurj Q α β (fun P ↦ by simpa [α, β] using h P) Y
  simpa [α, β] using this

theorem unit_of_essSurj {C : Type u₇} {DE : Type u₁} {EE : Type u₄} [Category.{v₇} C]
    [Category.{v₁} DE] [Category.{v₄} EE] (Q : C ⥤ DE) [Q.EssSurj]
    (Oh : DE ⥤ DE) (TE : DE ⥤ EE) (Xh : EE ⥤ EE) (eh : Oh ⋙ TE ≅ TE ⋙ Xh)
    (Ou : Oh ≅ 𝟭 DE) (Xu : Xh ≅ 𝟭 EE)
    (h : ∀ P, eh.inv.app (Q.obj P) ≫ TE.map (Ou.hom.app (Q.obj P)) =
      Xu.hom.app (TE.obj (Q.obj P))) (Y : DE) :
    eh.inv.app Y ≫ TE.map (Ou.hom.app Y) = Xu.hom.app (TE.obj Y) := by
  let α : TE ⋙ Xh ⟶ TE :=
    eh.inv ≫ Functor.whiskerRight Ou.hom TE ≫ (Functor.leftUnitor TE).hom
  let β : TE ⋙ Xh ⟶ TE := Functor.whiskerLeft TE Xu.hom ≫ (Functor.rightUnitor TE).hom
  have := app_eq_of_essSurj Q α β (fun P ↦ by simpa [α, β] using h P) Y
  simpa [α, β] using this

end Abstract

variable [IsNoetherian T]

theorem pbcAmbientScalarAssociator_eq_derivedComp {E L M : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) :
    pbcAmbientScalarAssociator l Ω T h k =
      pbcDerivedComp _ _ _ (pbcCompletedScalarMap_comp l Ω T h k) := rfl

end WeilConjectures.FdIntegralScalarForward
