import Langlands.Geometry.EtaleAdicTensorComparison
import Langlands.Geometry.EtaleEquivariantScalarExtension
import Langlands.Sheaf.AdicEpimorphisms

noncomputable section

namespace Langlands.Geometry.EtaleAdicSystem

open CategoryTheory AlgebraicGeometry Opposite
open EtaleCohomologyAction Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (I : Ideal R)

/-- Extension to a quotient coefficient ring has an epimorphic underlying unit. -/
theorem extensionUnit_app_epi (n : ℕ) (F : EtaleDerivedSections.ModuleSheaf X R) :
    Epi ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F) := by
  have h := congrArg (fun a => a.app F) (extensionPowerIso_unit X I n)
  dsimp only [NatTrans.comp_app] at h
  have : Epi ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F ≫
      (extensionPowerIso X I n).hom.app F) := by
    rw [h]
    infer_instance
  exact (epi_comp_iff_of_isIso _ ((extensionPowerIso X I n).hom.app F)).mp inferInstance

variable {G : Type w} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- The power reduction is the existing geometric-equivariant extension followed by restriction. -/
abbrev equivariantPower (n : ℕ) : EquivariantSheaf R ρ ⥤ EquivariantSheaf R ρ :=
  scalarExtensionFunctor (Ideal.Quotient.mk (I ^ n)) ρ ⋙
    scalarRestrictionFunctor (Ideal.Quotient.mk (I ^ n)) ρ

/-- The ordinary coefficient transition commutes with the geometric action. -/
theorem extensionTransition_comm {m n : ℕ} (h : m ≤ n)
    (F : EquivariantSheaf R ρ) (g : G) :
    ((equivariantPower I ρ n).obj F).act g ≫ (extensionTransition X I h).app F.obj =
      (translateBy R ρ g).map ((extensionTransition X I h).app F.obj) ≫
        ((equivariantPower I ρ m).obj F).act g := by
  have : Epi ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj) :=
    extensionUnit_app_epi I n F.obj
  have : (translateBy R ρ g).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (EtaleAutomorphism.sheafEquivalence (ModuleCat.{u} R) (aut ρ g)).toAdjunction
  have : Epi ((translateBy R ρ g).map
      ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj)) :=
    Functor.map_epi _ _
  apply (cancel_epi ((translateBy R ρ g).map
    ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj))).mp
  have hn := scalarExtensionUnit_comm (Ideal.Quotient.mk (I ^ n)) ρ F g
  have hm := scalarExtensionUnit_comm (Ideal.Quotient.mk (I ^ m)) ρ F g
  have ht := congrArg (fun a => a.app F.obj) (extensionTransition_unit X I h)
  dsimp only [NatTrans.comp_app] at ht
  calc
    _ = ((translateBy R ρ g).map
        ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj) ≫
        ((equivariantPower I ρ n).obj F).act g) ≫ (extensionTransition X I h).app F.obj :=
      (Category.assoc _ _ _).symm
    _ = (F.act g ≫ (sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj) ≫
        (extensionTransition X I h).app F.obj :=
      congrArg (fun k => k ≫ (extensionTransition X I h).app F.obj) hn.symm
    _ = F.act g ≫ (sheafExtensionUnit (Ideal.Quotient.mk (I ^ m)) X).app F.obj :=
      (Category.assoc _ _ _).trans (congrArg (fun k => F.act g ≫ k) ht)
    _ = (translateBy R ρ g).map
        ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ m)) X).app F.obj) ≫
        ((equivariantPower I ρ m).obj F).act g := hm
    _ = (translateBy R ρ g).map
        ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj ≫
          (extensionTransition X I h).app F.obj) ≫
        ((equivariantPower I ρ m).obj F).act g :=
      congrArg (fun k => (translateBy R ρ g).map k ≫
        ((equivariantPower I ρ m).obj F).act g) ht.symm
    _ = _ := by rw [Functor.map_comp, Category.assoc]

/-- Canonical coefficient transitions as morphisms of geometrically equivariant sheaves. -/
def equivariantTransition {m n : ℕ} (h : m ≤ n) :
    equivariantPower I ρ n ⟶ equivariantPower I ρ m where
  app F := ⟨(extensionTransition X I h).app F.obj, extensionTransition_comm I ρ h F⟩
  naturality {F E} a := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (extensionTransition X I h).naturality a.hom

/-- The transition has exactly the ordinary coefficient map as its underlying morphism. -/
@[simp] theorem equivariantTransition_app_hom {m n : ℕ} (h : m ≤ n)
    (F : EquivariantSheaf R ρ) :
    ((equivariantTransition I ρ h).app F).hom = (extensionTransition X I h).app F.obj := rfl

@[simp] theorem equivariantTransition_refl (n : ℕ) :
    equivariantTransition I ρ (le_refl n) = 𝟙 (equivariantPower I ρ n) := by
  apply NatTrans.ext
  funext F
  apply TranslationAction.Equivariant.Hom.ext
  exact congrArg (fun a => a.app F.obj) (extensionTransition_refl X I n)

@[reassoc (attr := simp)] theorem equivariantTransition_comp {l m n : ℕ}
    (h : l ≤ m) (k : m ≤ n) :
    equivariantTransition I ρ k ≫ equivariantTransition I ρ h =
      equivariantTransition I ρ (h.trans k) := by
  apply NatTrans.ext
  funext F
  apply TranslationAction.Equivariant.Hom.ext
  exact congrArg (fun a => a.app F.obj) (extensionTransition_comp X I h k)

/-- The existing equivariant extension units are compatible with these transitions. -/
@[reassoc (attr := simp)] theorem equivariantTransition_unit {m n : ℕ} (h : m ≤ n) :
    scalarExtensionUnit (Ideal.Quotient.mk (I ^ n)) ρ ≫ equivariantTransition I ρ h =
      scalarExtensionUnit (Ideal.Quotient.mk (I ^ m)) ρ := by
  apply NatTrans.ext
  funext F
  apply TranslationAction.Equivariant.Hom.ext
  exact congrArg (fun a => a.app F.obj) (extensionTransition_unit X I h)

/-- The inverse system of actual geometric-equivariant coefficient endofunctors. -/
def equivariantPowers : ℕᵒᵖ ⥤ (EquivariantSheaf R ρ ⥤ EquivariantSheaf R ρ) where
  obj n := equivariantPower I ρ n.unop
  map f := equivariantTransition I ρ (leOfHom f.unop)
  map_id _ := equivariantTransition_refl I ρ _
  map_comp f g := (equivariantTransition_comp I ρ (leOfHom g.unop) (leOfHom f.unop)).symm

/-- Functorial geometric-equivariant coefficient inverse systems. -/
def equivariantFunctor : EquivariantSheaf R ρ ⥤ (ℕᵒᵖ ⥤ EquivariantSheaf R ρ) :=
  (equivariantPowers I ρ).flip

/-- The cone from a geometrically equivariant sheaf to all its coefficient reductions. -/
def equivariantQuotientCone (F : EquivariantSheaf R ρ) :
    Limits.Cone ((equivariantFunctor I ρ).obj F) where
  pt := F
  π :=
    { app := fun n => (scalarExtensionUnit (Ideal.Quotient.mk (I ^ n.unop)) ρ).app F
      naturality := by
        intro m n f
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        exact (congrArg (fun a => a.app F)
          (equivariantTransition_unit I ρ (leOfHom f.unop))).symm }

/-- Forgetting geometric equivariance yields exactly the ordinary extension system. -/
def equivariantExtensionForgetIso :
    equivariantFunctor I ρ ⋙
        (Functor.whiskeringRight ℕᵒᵖ (EquivariantSheaf R ρ)
          (EtaleDerivedSections.ModuleSheaf X R)).obj TranslationAction.Equivariant.forget ≅
      TranslationAction.Equivariant.forget ⋙ extensionFunctor X I :=
  Iso.refl _

/-- The underlying system is naturally the existing sheaf quotient coefficient system. -/
def equivariantFunctorForgetIso :
    equivariantFunctor I ρ ⋙
        (Functor.whiskeringRight ℕᵒᵖ (EquivariantSheaf R ρ)
          (EtaleDerivedSections.ModuleSheaf X R)).obj TranslationAction.Equivariant.forget ≅
      TranslationAction.Equivariant.forget ⋙ functor X I :=
  equivariantExtensionForgetIso I ρ ≪≫
    Functor.isoWhiskerLeft TranslationAction.Equivariant.forget (extensionFunctorIso X I)

/-- The underlying comparison carries the canonical equivariant cone to the quotient cone maps. -/
@[reassoc (attr := simp)] theorem equivariantFunctorForgetIso_unit
    (F : EquivariantSheaf R ρ) (n : ℕ) :
    ((equivariantQuotientCone I ρ F).π.app (op n)).hom ≫
        ((equivariantFunctorForgetIso I ρ).hom.app F).app (op n) =
      (Langlands.Sheaf.AdicSystem.quotientMap X.smallEtaleTopology I n).app F.obj := by
  change (sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj ≫
      (𝟙 _ ≫ (extensionPowerIso X I n).hom.app F.obj) = _
  rw [Category.id_comp]
  exact congrArg (fun a => a.app F.obj) (extensionPowerIso_unit X I n)

end Langlands.Geometry.EtaleAdicSystem
