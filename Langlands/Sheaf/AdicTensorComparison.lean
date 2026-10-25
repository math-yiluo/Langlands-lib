import Langlands.Coefficients.AdicTensorComparison
import Langlands.Sheaf.AdicSystem
import Mathlib.CategoryTheory.Sites.Adjunction

/-! # Sheafified tensor presentations of ideal-adic coefficient systems -/

noncomputable section

namespace Langlands.Sheaf.AdicSystem

open CategoryTheory Opposite

universe u uC vC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
variable {R : Type u} [CommRing R] (I : Ideal R)
variable [HasSheafify J (ModuleCat.{u} R)]

/-- Sheafified extension to the quotient ring is the existing quotient-coefficient functor. -/
def tensorReduction [HasSheafify J (ModuleCat.{u} (R ⧸ I))] :
    CategoryTheory.Sheaf.composeAndSheafify J
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)) ≅ quotientCoefficients J I :=
  Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{u} R))
    (Functor.isoWhiskerRight
      ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} (R ⧸ I))).mapIso
        (Langlands.Coefficients.AdicSystem.tensorReduction I))
      (presheafToSheaf J (ModuleCat.{u} (R ⧸ I))))

/-- Sheafify the tensor-power module endofunctor over the original coefficient ring. -/
abbrev tensorPower (n : ℕ) :
    CategoryTheory.Sheaf J (ModuleCat.{u} R) ⥤ CategoryTheory.Sheaf J (ModuleCat.{u} R) :=
  (sheafifyEndofunctor J).obj (Langlands.Coefficients.AdicSystem.tensorPower I n)

/-- The tensor presentation of the existing sheaf reduction at a power of the ideal. -/
def tensorPowerIso (n : ℕ) : tensorPower J I n ≅ (powers J I).obj (op n) :=
  (sheafifyEndofunctor J).mapIso (Langlands.Coefficients.AdicSystem.tensorPowerIso I n)

/-- The inverse system obtained by sheafifying the actual tensor transitions. -/
def tensorPowers :
    ℕᵒᵖ ⥤ (CategoryTheory.Sheaf J (ModuleCat.{u} R) ⥤ CategoryTheory.Sheaf J (ModuleCat.{u} R)) :=
  Langlands.Coefficients.AdicSystem.tensorPowers I ⋙ sheafifyEndofunctor J

/-- The tensor and quotient presentations agree at every level and transition. -/
def tensorPowersIso : tensorPowers J I ≅ powers J I :=
  Functor.isoWhiskerRight (Langlands.Coefficients.AdicSystem.tensorPowersIso I)
    (sheafifyEndofunctor J)

/-- The tensor inverse system is functorial in the original sheaf. -/
def tensorFunctor :
    CategoryTheory.Sheaf J (ModuleCat.{u} R) ⥤ (ℕᵒᵖ ⥤ CategoryTheory.Sheaf J (ModuleCat.{u} R)) :=
  (tensorPowers J I).flip

/-- The comparison is natural both in the sheaf and in the coefficient level. -/
def tensorFunctorIso : tensorFunctor J I ≅ functor J I :=
  NatIso.ofComponents (fun F => NatIso.ofComponents
    (fun n => (tensorPowerIso J I n.unop).app F) (by
      intro m n f
      exact congrArg (fun a => a.app F) ((tensorPowersIso J I).hom.naturality f)))
    (by
      intro F E f
      apply NatTrans.ext
      funext n
      exact (tensorPowerIso J I n.unop).hom.naturality f)

/-- The tensor unit, sheafified using the inverse sheafification counit. -/
def tensorUnit (n : ℕ) : 𝟭 (CategoryTheory.Sheaf J (ModuleCat.{u} R)) ⟶ tensorPower J I n :=
  inv (sheafificationAdjunction J (ModuleCat.{u} R)).counit ≫
    (sheafifyEndofunctor J).map
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit

/-- The tensor unit becomes the existing sheaf quotient map. -/
@[reassoc (attr := simp)] theorem tensorPowerIso_unit (n : ℕ) :
    tensorUnit J I n ≫ (tensorPowerIso J I n).hom = quotientMap J I n := by
  dsimp only [tensorUnit, tensorPowerIso, Functor.mapIso_hom, quotientMap]
  rw [Category.assoc, ← Functor.map_comp,
    Langlands.Coefficients.AdicSystem.tensorPowerIso_unit]

/-- The sheafified tensor units form a compatible family over all coefficient levels. -/
@[reassoc (attr := simp)] theorem tensorUnit_transition {m n : ℕ} (h : m ≤ n) :
    tensorUnit J I n ≫ (tensorPowers J I).map (homOfLE h).op = tensorUnit J I m := by
  change (inv (sheafificationAdjunction J (ModuleCat.{u} R)).counit ≫
      (sheafifyEndofunctor J).map
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit) ≫
      (sheafifyEndofunctor J).map (Langlands.Coefficients.AdicSystem.tensorTransition I h) = _
  rw [Category.assoc, ← Functor.map_comp,
    Langlands.Coefficients.AdicSystem.tensorTransition_unit]
  rfl

/-- Extension to the quotient ring and scalar restriction agree with the sheafified tensor power.
Preservation of sheaves is explicit on an arbitrary site; preservation of sheafification
follows from the restriction/coextension adjunction. -/
def extensionPowerIso (n : ℕ)
    [HasSheafify J (ModuleCat.{u} (R ⧸ I ^ n))]
    [J.HasSheafCompose (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)))] :
    CategoryTheory.Sheaf.composeAndSheafify J
        (ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n))) ⋙
      sheafCompose J (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))) ≅
        tensorPower J I n :=
  Functor.isoWhiskerLeft
    (sheafToPresheaf J (ModuleCat.{u} R) ⋙
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{u} R) (ModuleCat.{u} (R ⧸ I ^ n))).obj
        (ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n))))
    (sheafComposeNatIso J (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)))
      (sheafificationAdjunction J (ModuleCat.{u} (R ⧸ I ^ n)))
      (sheafificationAdjunction J (ModuleCat.{u} R))).symm

/-- Before sheafification the coefficient unit is the sectionwise tensor unit. -/
theorem tensorUnit_hom (n : ℕ) (F : CategoryTheory.Sheaf J (ModuleCat.{u} R)) :
    ((tensorUnit J I n).app F).hom =
      Functor.whiskerLeft F.obj
        (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit ≫
      toSheafify J (F.obj ⋙ Langlands.Coefficients.AdicSystem.tensorPower I n) := by
  change ((inv (sheafificationAdjunction J (ModuleCat.{u} R)).counit).app F).hom ≫
    sheafifyMap J (Functor.whiskerLeft F.obj
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit) = _
  have h : ((inv (sheafificationAdjunction J (ModuleCat.{u} R)).counit).app F).hom =
      toSheafify J F.obj := by
    change (sheafToPresheaf J (ModuleCat.{u} R)).map
      ((inv (sheafificationAdjunction J (ModuleCat.{u} R)).counit).app F) = _
    rw [NatIso.isIso_inv_app, Functor.map_inv, (sheafificationAdjunction J (ModuleCat.{u} R)).inv_counit_map]
    rfl
  rw [h]
  exact (toSheafify_naturality J (Functor.whiskerLeft F.obj
    (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n))).unit)).symm

/-- The scalar-extension adjunction unit agrees with the tensor-system unit. -/
@[reassoc (attr := simp)] theorem extensionPowerIso_unit (n : ℕ)
    [HasSheafify J (ModuleCat.{u} (R ⧸ I ^ n))]
    [J.HasSheafCompose (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)))] :
    (CategoryTheory.Sheaf.adjunction J
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n)))).unit ≫
        (extensionPowerIso J I n).hom = tensorUnit J I n := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  change ((CategoryTheory.Sheaf.adjunction J
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk (I ^ n)))).unit.app F).hom ≫
    ((extensionPowerIso J I n).hom.app F).hom = _
  rw [CategoryTheory.Sheaf.adjunction_unit_app_hom,
    tensorUnit_hom, Category.assoc]
  change _ ≫ (Functor.whiskerRight
      (toSheafify J (F.obj ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n))))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))) ≫
      (sheafifyComposeIso J (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)))
        (F.obj ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ n)))).inv) = _
  rw [sheafComposeIso_inv_fac]
  rfl

end Langlands.Sheaf.AdicSystem
