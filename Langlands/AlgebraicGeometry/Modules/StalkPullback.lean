import Langlands.AlgebraicGeometry.Modules.StalkAdjunction
import Langlands.Algebra.ExtendScalarsTensor

/-! # Stalks of ordinary module pullback -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

namespace StalkPullback

variable (N : ModuleCat.{u} (X.presheaf.stalk x))

/-- Pushforward of a skyscraper is a skyscraper with restricted local-ring scalars. -/
def skyscraperPushforwardHom :
    (Scheme.Modules.pushforward f).obj (StalkAdjunction.skyscraper x N) ⟶
      StalkAdjunction.skyscraper (f x) ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) where
  val :=
    { app := fun U => by
        let A := ((Scheme.Modules.pushforward f).obj (StalkAdjunction.skyscraper x N)).val.obj U
        let B := (StalkAdjunction.skyscraper (f x)
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).val.obj U
        exact ModuleCat.ofHom (R := Γ(Y, U.unop)) (X := A) (Y := B)
          { toFun := fun n hx => n hx
            map_add' := fun _ _ => rfl
            map_smul' := by
              intro r n
              funext hx
              change X.presheaf.germ (f ⁻¹ᵁ U.unop) x hx.down (f.app U.unop r) • n hx =
                f.stalkMap x (Y.presheaf.germ U.unop (f x) hx.down r) • n hx
              erw [f.germ_stalkMap_apply] }
      naturality := by intros; ext n; rfl }

/-- The inverse sectionwise identity in the skyscraper pushforward comparison. -/
def skyscraperPushforwardInv :
    StalkAdjunction.skyscraper (f x) ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (StalkAdjunction.skyscraper x N) where
  val :=
    { app := fun U => by
        let A := ((Scheme.Modules.pushforward f).obj (StalkAdjunction.skyscraper x N)).val.obj U
        let B := (StalkAdjunction.skyscraper (f x)
          ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj N)).val.obj U
        exact ModuleCat.ofHom (R := Γ(Y, U.unop)) (X := B) (Y := A)
          { toFun := fun n hx => n hx
            map_add' := fun _ _ => rfl
            map_smul' := by
              intro r n
              funext hx
              change f.stalkMap x (Y.presheaf.germ U.unop (f x) hx.down r) • n hx =
                X.presheaf.germ (f ⁻¹ᵁ U.unop) x hx.down (f.app U.unop r) • n hx
              erw [f.germ_stalkMap_apply] }
      naturality := by intros; ext n; rfl }

/-- The natural comparison of the two actual right adjoints. -/
def skyscraperPushforwardIso :
    StalkAdjunction.skyscraperFunctor x ⋙ Scheme.Modules.pushforward f ≅
      ModuleCat.restrictScalars (f.stalkMap x).hom ⋙ StalkAdjunction.skyscraperFunctor (f x) :=
  NatIso.ofComponents (fun N =>
    { hom := skyscraperPushforwardHom f x N
      inv := skyscraperPushforwardInv f x N
      hom_inv_id := by ext U n; rfl
      inv_hom_id := by ext U n; rfl }) (by intros; ext U n; rfl)

/-- The stalk of ordinary pullback is extension of scalars along the actual stalk map. -/
def pullbackStalkIso :
    Scheme.Modules.pullback f ⋙ stalkFunctor x ≅
      stalkFunctor (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom :=
  Adjunction.leftAdjointUniq
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (StalkAdjunction.adjunction x)).ofNatIsoRight (skyscraperPushforwardIso f x))
    ((StalkAdjunction.adjunction (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))

/-- The ordinary tensor product form of the module pullback stalk comparison. -/
def pullbackStalkTensorEquiv (M : Y.Modules) :
    letI := (f.stalkMap x).hom.toAlgebra
    stalk ((Scheme.Modules.pullback f).obj M) x ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] stalk M (f x) := by
  letI := (f.stalkMap x).hom.toAlgebra
  exact ((pullbackStalkIso f x).app M).toLinearEquiv.trans
    (Langlands.Scheme.Modules.extendScalarsAlgebraEquiv
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) ((stalkFunctor (f x)).obj M))

end StalkPullback

end Langlands.AlgebraicGeometry.Modules
