import Langlands.Geometry.EtaleEquivariantAdicSystem
import Langlands.Geometry.EtaleEquivariantScalarExtensionPullback

noncomputable section

namespace Langlands.Geometry.EtaleAdicSystem

open CategoryTheory AlgebraicGeometry Opposite
open EtaleCohomologyAction EtalePullback Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R] (I : Ideal R)
variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- Coefficient reduction commutes with equivariant etale pullback at each power. -/
def equivariantPowerPullbackIso (n : ℕ) :
    equivariantPower I ρ n ⋙ equivariantPullback R ρ τ f hf ≅
      equivariantPullback R ρ τ f hf ⋙ equivariantPower I τ n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (scalarExtensionFunctor (Ideal.Quotient.mk (I ^ n)) ρ)
      (scalarRestrictionEquivariantPullbackIso (Ideal.Quotient.mk (I ^ n)) ρ τ f hf) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (scalarExtensionEquivariantPullbackIso (Ideal.Quotient.mk (I ^ n)) ρ τ f hf)
      (scalarRestrictionFunctor (Ideal.Quotient.mk (I ^ n)) τ) ≪≫
    Functor.associator _ _ _

/-- The level comparison respects the actual extension units. -/
@[reassoc (attr := simp)] theorem equivariantPowerPullbackIso_unit (n : ℕ)
    (F : EquivariantSheaf R ρ) :
    (equivariantPullback R ρ τ f hf).map
        ((scalarExtensionUnit (Ideal.Quotient.mk (I ^ n)) ρ).app F) ≫
      (equivariantPowerPullbackIso I ρ τ f hf n).hom.app F =
    (scalarExtensionUnit (Ideal.Quotient.mk (I ^ n)) τ).app
      ((equivariantPullback R ρ τ f hf).obj F) := by
  simpa only [equivariantPowerPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
    Category.comp_id, Category.assoc] using
      scalarExtensionUnit_equivariantPullback (Ideal.Quotient.mk (I ^ n)) ρ τ f hf F

/-- Pullback preserves the epimorphic coefficient unit. -/
theorem equivariantPullback_unit_epi (n : ℕ) (F : EquivariantSheaf R ρ) :
    Epi ((equivariantPullback R ρ τ f hf).map
      ((scalarExtensionUnit (Ideal.Quotient.mk (I ^ n)) ρ).app F)) := by
  have : Epi ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj) :=
    extensionUnit_app_epi I n F.obj
  have : (restriction f (ModuleCat.{u} R)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (restrictionAdjunction f (ModuleCat.{u} R))
  apply (TranslationAction.Equivariant.forget).epi_of_epi_map
  change Epi ((restriction f (ModuleCat.{u} R)).map
    ((sheafExtensionUnit (Ideal.Quotient.mk (I ^ n)) X).app F.obj))
  exact Functor.map_epi (restriction f (ModuleCat.{u} R)) _

/-- Level comparisons commute with every coefficient transition. -/
theorem equivariantPowerPullbackIso_transition {m n : ℕ} (h : m ≤ n)
    (F : EquivariantSheaf R ρ) :
    (equivariantPullback R ρ τ f hf).map ((equivariantTransition I ρ h).app F) ≫
        (equivariantPowerPullbackIso I ρ τ f hf m).hom.app F =
      (equivariantPowerPullbackIso I ρ τ f hf n).hom.app F ≫
        (equivariantTransition I τ h).app ((equivariantPullback R ρ τ f hf).obj F) := by
  have := equivariantPullback_unit_epi I ρ τ f hf n F
  apply (cancel_epi ((equivariantPullback R ρ τ f hf).map
    ((scalarExtensionUnit (Ideal.Quotient.mk (I ^ n)) ρ).app F))).mp
  have hn := congrArg (fun a => a.app F) (equivariantTransition_unit I ρ h)
  have hm := congrArg (fun a => a.app ((equivariantPullback R ρ τ f hf).obj F))
    (equivariantTransition_unit I τ h)
  dsimp only [NatTrans.comp_app] at hn hm
  rw [← Category.assoc, ← Functor.map_comp, hn,
    equivariantPowerPullbackIso_unit, ← Category.assoc,
    equivariantPowerPullbackIso_unit, hm]

/-- Pullback commutes naturally with the complete geometric-equivariant inverse system. -/
def equivariantFunctorPullbackIso :
    equivariantFunctor I ρ ⋙
        (Functor.whiskeringRight ℕᵒᵖ (EquivariantSheaf R ρ)
          (EquivariantSheaf R τ)).obj (equivariantPullback R ρ τ f hf) ≅
      equivariantPullback R ρ τ f hf ⋙ equivariantFunctor I τ :=
  NatIso.ofComponents (fun F => NatIso.ofComponents
    (fun n => (equivariantPowerPullbackIso I ρ τ f hf n.unop).app F)
    (by
      intro m n a
      exact equivariantPowerPullbackIso_transition I ρ τ f hf (leOfHom a.unop) F))
    (by
      intro F E a
      apply NatTrans.ext
      funext n
      exact (equivariantPowerPullbackIso I ρ τ f hf n.unop).hom.naturality a)

/-- The system comparison identifies the pulled-back canonical cone legs. -/
@[reassoc (attr := simp)] theorem equivariantFunctorPullbackIso_unit
    (F : EquivariantSheaf R ρ) (n : ℕ) :
    (equivariantPullback R ρ τ f hf).map ((equivariantQuotientCone I ρ F).π.app (op n)) ≫
        ((equivariantFunctorPullbackIso I ρ τ f hf).hom.app F).app (op n) =
      (equivariantQuotientCone I τ ((equivariantPullback R ρ τ f hf).obj F)).π.app (op n) :=
  equivariantPowerPullbackIso_unit I ρ τ f hf n F

end Langlands.Geometry.EtaleAdicSystem
