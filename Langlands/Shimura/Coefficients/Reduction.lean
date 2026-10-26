import Langlands.Shimura.Coefficients.ConstantScalarCompatibility
import Langlands.Geometry.EtaleAdicTensorComparison
import Langlands.Sheaf.AdicEpimorphisms

/-! # Coefficient reduction of actual associated sheaves -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {G : Type u} [Group G]

/-- The actual tensor/quotient identification preserves the coefficient group action. -/
def moduleTensorReductionActionIso :
    (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I)).mapAction G ≅
      (Langlands.Coefficients.AdicSystem.reduction I).mapAction G :=
  Functor.mapActionCongr G (Langlands.Coefficients.AdicSystem.tensorReduction I)

/-- Tensor extension followed by restriction presents the power-reduction action. -/
def moduleTensorPowerActionIso (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (I ^ n))).mapAction G ⋙
        (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n))).mapAction G ≅
      (Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction G :=
  (Functor.mapActionComp G _ _).symm ≪≫
    Functor.mapActionCongr G (Langlands.Coefficients.AdicSystem.tensorPowerIso I n)

/-- The genuine quotient map is equivariant and natural in the coefficient action. -/
def modulePowerReductionUnit (n : ℕ) :
    𝟭 (Action (ModuleCat.{u} R) G) ⟶
      (Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction G where
  app M :=
    { hom := (Langlands.Coefficients.AdicSystem.quotientMap I n).app M.V
      comm g := (Langlands.Coefficients.AdicSystem.quotientMap I n).naturality (M.ρ g) }
  naturality {M N} f := by
    apply Action.hom_injective
    exact (Langlands.Coefficients.AdicSystem.quotientMap I n).naturality f.hom

/-- The equivariant tensor unit becomes the equivariant quotient map. -/
@[reassoc (attr := simp)]
theorem moduleTensorPowerActionIso_unit (n : ℕ) :
    moduleExtensionActionUnit (Ideal.Quotient.mk (I ^ n)) ≫
      (moduleTensorPowerActionIso (G := G) I n).hom = modulePowerReductionUnit I n := by
  apply NatTrans.ext
  funext M
  apply Action.hom_injective
  exact congrArg (fun a => a.app M.V)
    (Langlands.Coefficients.AdicSystem.tensorPowerIso_unit I n)

/-- Actual power-quotient transitions, retaining the coefficient group action. -/
def modulePowerReductionTransition {m n : ℕ} (h : m ≤ n) :
    (Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction G ⟶
      (Langlands.Coefficients.AdicSystem.powerReduction I m).mapAction G where
  app M :=
    { hom := (Langlands.Coefficients.AdicSystem.transition I h).app M.V
      comm g := (Langlands.Coefficients.AdicSystem.transition I h).naturality (M.ρ g) }
  naturality {M N} f := by
    apply Action.hom_injective
    exact (Langlands.Coefficients.AdicSystem.transition I h).naturality f.hom

@[simp]
theorem modulePowerReductionTransition_refl (n : ℕ) :
    modulePowerReductionTransition (G := G) I (le_refl n) = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  apply Action.hom_injective
  exact congrArg (fun a => a.app M.V)
    (Langlands.Coefficients.AdicSystem.transition_refl I n)

@[reassoc (attr := simp)]
theorem modulePowerReductionTransition_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    modulePowerReductionTransition (G := G) I k ≫ modulePowerReductionTransition I h =
      modulePowerReductionTransition I (h.trans k) := by
  apply NatTrans.ext
  funext M
  apply Action.hom_injective
  exact congrArg (fun a => a.app M.V)
    (Langlands.Coefficients.AdicSystem.transition_comp I h k)

@[reassoc (attr := simp)]
theorem modulePowerReductionUnit_transition {m n : ℕ} (h : m ≤ n) :
    modulePowerReductionUnit (G := G) I n ≫ modulePowerReductionTransition I h =
      modulePowerReductionUnit I m := by
  apply NatTrans.ext
  funext M
  apply Action.hom_injective
  exact congrArg (fun a => a.app M.V)
    (Langlands.Coefficients.AdicSystem.quotientMap_transition I h)

/-- The inverse system of actual power-reduction functors on coefficient actions. -/
def modulePowerReductions :
    ℕᵒᵖ ⥤ (Action (ModuleCat.{u} R) G ⥤ Action (ModuleCat.{u} R) G) where
  obj n := (Langlands.Coefficients.AdicSystem.powerReduction I n.unop).mapAction G
  map f := modulePowerReductionTransition I (leOfHom f.unop)
  map_id n := modulePowerReductionTransition_refl I n.unop
  map_comp f g :=
    (modulePowerReductionTransition_comp I (leOfHom g.unop) (leOfHom f.unop)).symm

variable (X : Scheme.{u}) (Y : Action X.Etale G)

/-- Canonical comparison from quotienting an associated sheaf to associated quotient coefficients. -/
def constantAssociatedReductionComparison :
    constantAssociatedFunctor X.smallEtaleTopology Y ⋙
        EtaleAdicSystem.quotientCoefficients X I ⟶
      (Langlands.Coefficients.AdicSystem.reduction I).mapAction G ⋙
        constantAssociatedFunctor X.smallEtaleTopology Y :=
  Functor.whiskerLeft (constantAssociatedFunctor X.smallEtaleTopology Y)
      (EtaleAdicSystem.tensorReduction X I).inv ≫
    constantAssociatedExtendScalarsComparison (Ideal.Quotient.mk I) X Y ≫
      Functor.whiskerRight (moduleTensorReductionActionIso I).hom
        (constantAssociatedFunctor X.smallEtaleTopology Y)

/-- The corresponding comparison for power reductions over the original scalar ring. -/
def constantAssociatedPowerReductionComparison (n : ℕ) :
    constantAssociatedFunctor X.smallEtaleTopology Y ⋙
        (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).obj (op n) ⟶
      (Langlands.Coefficients.AdicSystem.powerReduction I n).mapAction G ⋙
        constantAssociatedFunctor X.smallEtaleTopology Y :=
  Functor.whiskerLeft (constantAssociatedFunctor X.smallEtaleTopology Y)
      (EtaleAdicSystem.extensionPowerIso X I n).inv ≫
    Functor.whiskerRight
        (constantAssociatedExtendScalarsComparison (Ideal.Quotient.mk (I ^ n)) X Y)
        (sheafRestrictScalars (Ideal.Quotient.mk (I ^ n)) X) ≫
    Functor.whiskerLeft
        ((ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk (I ^ n))).mapAction G)
        (constantAssociatedRestrictScalarsIso X.smallEtaleTopology
          (Ideal.Quotient.mk (I ^ n)) Y).hom ≫
    Functor.whiskerRight (moduleTensorPowerActionIso I n).hom
      (constantAssociatedFunctor X.smallEtaleTopology Y)

/-- The associated reduction comparison carries the genuine sheaf quotient unit. -/
@[reassoc]
theorem constantAssociatedPowerReductionComparison_unit (n : ℕ)
    (M : Action (ModuleCat.{u} R) G) :
    (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
        ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M) ≫
      (constantAssociatedPowerReductionComparison I X Y n).app M =
        (constantAssociatedFunctor X.smallEtaleTopology Y).map
          ((modulePowerReductionUnit I n).app M) := by
  have hq := congrArg
    (fun a => a.app ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M))
    (EtaleAdicSystem.extensionPowerIso_unit X I n)
  simp only [NatTrans.comp_app] at hq
  rw [← hq]
  dsimp only [constantAssociatedPowerReductionComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [constantAssociatedScalarChange_unit_assoc, ← Functor.map_comp]
  congr 1
  exact congrArg (fun a => a.app M) (moduleTensorPowerActionIso_unit I n)

/-- Quotient comparison commutes with every power-reduction transition. -/
@[reassoc]
theorem constantAssociatedPowerReductionComparison_transition {m n : ℕ} (h : m ≤ n) :
    Functor.whiskerLeft (constantAssociatedFunctor X.smallEtaleTopology Y)
        ((Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).map (homOfLE h).op) ≫
      constantAssociatedPowerReductionComparison I X Y m =
        constantAssociatedPowerReductionComparison I X Y n ≫
          Functor.whiskerRight (modulePowerReductionTransition I h)
            (constantAssociatedFunctor X.smallEtaleTopology Y) := by
  apply NatTrans.ext
  funext M
  apply (cancel_epi ((Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app
    ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M))).mp
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hs := congrArg
    (fun a => a.app ((constantAssociatedFunctor X.smallEtaleTopology Y).obj M))
    (Langlands.Sheaf.AdicSystem.quotientMap_transition X.smallEtaleTopology I h)
  have hm := congrArg (fun a => a.app M) (modulePowerReductionUnit_transition (G := G) I h)
  simp only [NatTrans.comp_app] at hs hm
  rw [← Category.assoc, hs, constantAssociatedPowerReductionComparison_unit,
    ← Category.assoc, constantAssociatedPowerReductionComparison_unit,
    ← Functor.map_comp, hm]

/-- Associated sheaves of the actual module power reductions, naturally in coefficients. -/
def constantAssociatedModuleReductionFunctor :
    Action (ModuleCat.{u} R) G ⥤
      (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :=
  (modulePowerReductions (G := G) I).flip ⋙
    (Functor.whiskeringRight ℕᵒᵖ (Action (ModuleCat.{u} R) G)
      (EtaleDerivedSections.ModuleSheaf X R)).obj
        (constantAssociatedFunctor X.smallEtaleTopology Y)

/-- Natural map from reductions of the associated sheaf to associated reduced coefficients. -/
def constantAssociatedReductionSystemsComparison :
    constantAssociatedFunctor X.smallEtaleTopology Y ⋙ EtaleAdicSystem.functor X I ⟶
      constantAssociatedModuleReductionFunctor I X Y where
  app M :=
    { app n := (constantAssociatedPowerReductionComparison I X Y n.unop).app M
      naturality m n f := congrArg (fun a => a.app M)
        (constantAssociatedPowerReductionComparison_transition I X Y (leOfHom f.unop)) }
  naturality {M N} f := by
    apply NatTrans.ext
    funext n
    exact (constantAssociatedPowerReductionComparison I X Y n.unop).naturality f

end Langlands.Shimura.Coefficients
