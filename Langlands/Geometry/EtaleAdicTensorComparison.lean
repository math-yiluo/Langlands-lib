import Langlands.Sheaf.AdicTensorComparison
import Langlands.Geometry.EtaleAdicSystem
import Langlands.Geometry.EtaleScalarExtension

/-! # Tensor extension presentation of etale coefficient inverse systems -/

noncomputable section

namespace Langlands.Geometry.EtaleAdicSystem

open CategoryTheory AlgebraicGeometry Opposite
open EtaleCohomologyAction

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)

/-- Actual etale scalar extension to a quotient ring is quotient followed by sheafification. -/
def tensorReduction :
    sheafExtendScalars (Ideal.Quotient.mk I) X ≅ quotientCoefficients X I :=
  Langlands.Sheaf.AdicSystem.tensorReduction X.smallEtaleTopology I

/-- Extension to a power quotient, viewed again as sheaves over the initial ring. -/
abbrev extensionPower (n : ℕ) :
    EtaleDerivedSections.ModuleSheaf X R ⥤ EtaleDerivedSections.ModuleSheaf X R :=
  sheafExtendScalars (Ideal.Quotient.mk (I ^ n)) X ⋙
    sheafRestrictScalars (Ideal.Quotient.mk (I ^ n)) X

/-- The actual extension/restriction functor agrees with the existing coefficient reduction. -/
def extensionPowerIso (n : ℕ) :
    extensionPower X I n ≅ (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).obj (op n) :=
  Langlands.Sheaf.AdicSystem.extensionPowerIso X.smallEtaleTopology I n ≪≫
    Langlands.Sheaf.AdicSystem.tensorPowerIso X.smallEtaleTopology I n

/-- The scalar-extension adjunction unit becomes the canonical sheaf quotient map. -/
@[reassoc (attr := simp)] theorem extensionPowerIso_unit (n : ℕ) :
    sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X ≫ (extensionPowerIso X I n).hom =
      Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n := by
  dsimp only [extensionPowerIso, Iso.trans_hom]
  rw [← Category.assoc]
  change (CategoryTheory.Sheaf.adjunction X.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (Ideal.Quotient.mk (I ^ n)))).unit ≫ _ ≫ _ = _
  rw [← Category.assoc]
  erw [Langlands.Sheaf.AdicSystem.extensionPowerIso_unit,
    Langlands.Sheaf.AdicSystem.tensorPowerIso_unit]

/-- Canonical coefficient transition on the actual sheaf scalar-extension presentation. -/
def extensionTransition {m n : ℕ} (h : m ≤ n) :
    extensionPower X I n ⟶ extensionPower X I m :=
  (extensionPowerIso X I n).hom ≫
    (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).map (homOfLE h).op ≫
    (extensionPowerIso X I m).inv

@[reassoc (attr := simp)] theorem extensionTransition_comparison {m n : ℕ} (h : m ≤ n) :
    extensionTransition X I h ≫ (extensionPowerIso X I m).hom =
      (extensionPowerIso X I n).hom ≫
        (Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I).map (homOfLE h).op := by
  simp [extensionTransition]

@[simp] theorem extensionTransition_refl (n : ℕ) :
    extensionTransition X I (le_refl n) = 𝟙 (extensionPower X I n) := by
  simp [extensionTransition]

@[reassoc (attr := simp)] theorem extensionTransition_comp {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n) :
    extensionTransition X I k ≫ extensionTransition X I h = extensionTransition X I (h.trans k) := by
  simp only [extensionTransition, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc]
  rfl

/-- The extension units are compatible with every coefficient transition. -/
@[reassoc (attr := simp)] theorem extensionTransition_unit {m n : ℕ} (h : m ≤ n) :
    sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X ≫ extensionTransition X I h =
      sheafExtensionUnit (Ideal.Quotient.mk (I ^ m)) X := by
  apply (cancel_mono (extensionPowerIso X I m).hom).mp
  rw [Category.assoc, extensionTransition_comparison, ← Category.assoc,
    extensionPowerIso_unit, Langlands.Sheaf.AdicSystem.quotientMap_transition,
    extensionPowerIso_unit]

/-- The inverse system of actual sheaf scalar-extension/restriction functors. -/
def extensionPowers :
    ℕᵒᵖ ⥤ (EtaleDerivedSections.ModuleSheaf X R ⥤ EtaleDerivedSections.ModuleSheaf X R) where
  obj n := extensionPower X I n.unop
  map f := extensionTransition X I (leOfHom f.unop)
  map_id _ := extensionTransition_refl X I _
  map_comp f g := (extensionTransition_comp X I (leOfHom g.unop) (leOfHom f.unop)).symm

/-- The comparison respects the whole inverse system of coefficient endofunctors. -/
def extensionPowersIso :
    extensionPowers X I ≅ Langlands.Sheaf.AdicSystem.powers X.smallEtaleTopology I :=
  NatIso.ofComponents (fun n => extensionPowerIso X I n.unop) (by
    intro m n f
    exact extensionTransition_comparison X I (leOfHom f.unop))

/-- Actual scalar-extension inverse systems, functorially in an etale sheaf. -/
def extensionFunctor :
    EtaleDerivedSections.ModuleSheaf X R ⥤ (ℕᵒᵖ ⥤ EtaleDerivedSections.ModuleSheaf X R) :=
  (extensionPowers X I).flip

/-- The extension presentation is naturally the existing etale coefficient-system functor. -/
def extensionFunctorIso : extensionFunctor X I ≅ functor X I :=
  NatIso.ofComponents (fun F => NatIso.ofComponents
    (fun n => (extensionPowerIso X I n.unop).app F) (by
      intro m n f
      exact congrArg (fun a => a.app F) (extensionTransition_comparison X I (leOfHom f.unop))))
    (by
      intro F E f
      apply NatTrans.ext
      funext n
      exact (extensionPowerIso X I n.unop).hom.naturality f)

end Langlands.Geometry.EtaleAdicSystem
