import Langlands.AlgebraicGeometry.Modules.LocalizationSectionsBaseChange

/-! # Actual sections of an open pushforward -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}}

/-- Sections of the pushforward of an open restriction are sections on that open,
with the actual `R`-action. -/
def openPushforwardSectionsLinearEquiv (P : (Spec R).Modules) (V : (Spec R).Opens) :
    (relativeGlobalSections V.ι).obj (P.restrict V.ι) ≃ₗ[R]
      (modulesSpecToSheaf.obj P).obj.obj (op V) := by
  let e : Γ(P, V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤)) ≅ Γ(P, V) :=
    P.presheaf.mapIso (eqToIso (by simp : V = V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤))).op
  let a : (relativeGlobalSections V.ι).obj (P.restrict V.ι) ≃+
      (modulesSpecToSheaf.obj P).obj.obj (op V) :=
    { toFun := e.hom
      invFun := e.inv
      left_inv := fun x => Iso.hom_inv_id_apply e x
      right_inv := fun x => Iso.inv_hom_id_apply e x
      map_add' := fun x y => e.hom.hom.map_add x y }
  refine AddEquiv.toLinearEquiv a ?_
  intro r x
  change P.presheaf.map _
    (((V.ι.app ⊤ ≫ (V.ι.appIso (V.ι ⁻¹ᵁ ⊤)).inv) ((Scheme.ΓSpecIso R).inv r)) • (show Γ(P, V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤)) from x)) = _
  rw [V.ι.app_appIso_inv]
  erw [Scheme.Modules.map_smul]
  change _ = ((Spec R).presheaf.map V.leTop.op ((Scheme.ΓSpecIso R).inv r)) •
    (P.presheaf.map _ (show Γ(P, V.ι ''ᵁ (V.ι ⁻¹ᵁ ⊤)) from x))
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The open sections equivalence sends the restriction unit to restriction of sections. -/
lemma openPushforwardSectionsLinearEquiv_unit (P : (Spec R).Modules)
    (V : (Spec R).Opens) (x : moduleSpecΓFunctor.obj P) :
    openPushforwardSectionsLinearEquiv P V
      (((Scheme.Modules.restrictAdjunction V.ι).unit.app P).app ⊤ x) =
        (modulesSpecToSheaf.obj P).obj.map V.leTop.op x := by
  change P.presheaf.map _
    (P.presheaf.map (homOfLE (V.ι.image_preimage_le ⊤)).op
      (show Γ(P, ⊤) from x)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end Langlands.AlgebraicGeometry.Modules.DerivedSections
