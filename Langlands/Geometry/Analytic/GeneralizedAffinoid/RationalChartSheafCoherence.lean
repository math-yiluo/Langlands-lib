import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCoverBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartPullbackCoherence

/-! # Coherent direct image on actual finite rational chart sites -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem hom_unique {A : PresentedAffinoidAlgebra K}
    {d e : RationalChart K A} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance f g

/-- Actual identity-pullback comparisons induce the identity comparison for
direct image of arbitrary-category sheaves on the finite rational chart site. -/
def coefficientSheafPushforwardIdIso (A : PresentedAffinoidAlgebra K)
    (E : Type v) [Category.{w} E] :
    coefficientSheafPushforward (BoundedAlgHom.id K A) E ≅
      𝟭 (Sheaf (finiteRationalTopology K A) E) :=
  Functor.sheafPushforwardContinuousId' (pullbackIdNatIso A) E
    (finiteRationalTopology K A)

/-- Actual composite-pullback comparisons identify successive sheaf direct
image with direct image along the composite bounded coefficient map. -/
def coefficientSheafPushforwardCompIso
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (E : Type v) [Category.{w} E] :
    coefficientSheafPushforward ψ E ⋙ coefficientSheafPushforward φ E ≅
      coefficientSheafPushforward (ψ.comp φ) E :=
  Functor.sheafPushforwardContinuousComp' (pullbackCompNatIso φ ψ).symm E
    (finiteRationalTopology K A) (finiteRationalTopology K B)
    (finiteRationalTopology K C)

variable (E : Type v) [Category.{w} E]

set_option backward.isDefEq.respectTransparency.types false

@[simp]
theorem coefficientSheafPushforwardIdIso_hom_app
    (F : Sheaf (finiteRationalTopology K A) E) (d : RationalChart K A) :
    (((coefficientSheafPushforwardIdIso A E).hom.app F).hom.app (Opposite.op d)) =
      F.obj.map (pullbackIdIso d).inv.op := by
  simp [coefficientSheafPushforwardIdIso, pullbackIdNatIso, NatIso.ofComponents]
  rfl

@[simp]
theorem coefficientSheafPushforwardIdIso_inv_app
    (F : Sheaf (finiteRationalTopology K A) E) (d : RationalChart K A) :
    (((coefficientSheafPushforwardIdIso A E).inv.app F).hom.app (Opposite.op d)) =
      F.obj.map (pullbackIdIso d).hom.op := by
  simp [coefficientSheafPushforwardIdIso, pullbackIdNatIso, NatIso.ofComponents]
  rfl

@[simp]
theorem coefficientSheafPushforwardCompIso_hom_app
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (F : Sheaf (finiteRationalTopology K C) E) (d : RationalChart K A) :
    (((coefficientSheafPushforwardCompIso φ ψ E).hom.app F).hom.app (Opposite.op d)) =
      F.obj.map (pullbackCompIso φ ψ d).hom.op := by
  simp [coefficientSheafPushforwardCompIso, pullbackCompNatIso, NatIso.ofComponents]
  rfl

@[simp]
theorem coefficientSheafPushforwardCompIso_inv_app
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (F : Sheaf (finiteRationalTopology K C) E) (d : RationalChart K A) :
    (((coefficientSheafPushforwardCompIso φ ψ E).inv.app F).hom.app (Opposite.op d)) =
      F.obj.map (pullbackCompIso φ ψ d).inv.op := by
  simp [coefficientSheafPushforwardCompIso, pullbackCompNatIso, NatIso.ofComponents]
  rfl

/-- Removing the identity at the source agrees with the identity comparison
on the directly imaged sheaf. -/
theorem coefficientSheafPushforwardCompIso_source_id
    (φ : BoundedAlgHom K A B) (F : Sheaf (finiteRationalTopology K B) E) :
    (coefficientSheafPushforwardCompIso (BoundedAlgHom.id K A) φ E).hom.app F =
      (coefficientSheafPushforwardIdIso A E).hom.app
        ((coefficientSheafPushforward φ E).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  change _ = (((coefficientSheafPushforwardIdIso A E).hom.app
    ((coefficientSheafPushforward φ E).obj F)).hom.app (Opposite.op d.unop))
  rw [coefficientSheafPushforwardCompIso_hom_app,
    coefficientSheafPushforwardIdIso_hom_app]
  change F.obj.map _ = F.obj.map _
  apply congrArg F.obj.map
  exact congrArg Quiver.Hom.op (hom_unique _ _)

/-- Removing the identity at the target agrees with direct image of the
identity comparison on the original sheaf. -/
theorem coefficientSheafPushforwardCompIso_target_id
    (φ : BoundedAlgHom K A B) (F : Sheaf (finiteRationalTopology K B) E) :
    (coefficientSheafPushforwardCompIso φ (BoundedAlgHom.id K B) E).hom.app F =
      (coefficientSheafPushforward φ E).map
        ((coefficientSheafPushforwardIdIso B E).hom.app F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  change (((coefficientSheafPushforwardCompIso φ (BoundedAlgHom.id K B) E).hom.app F
    ).hom.app (Opposite.op d.unop)) = _
  rw [coefficientSheafPushforwardCompIso_hom_app]
  dsimp [coefficientSheafPushforward, Functor.sheafPushforwardContinuous]
  rw [coefficientSheafPushforwardIdIso_hom_app]
  change F.obj.map _ = F.obj.map _
  apply congrArg F.obj.map
  exact congrArg Quiver.Hom.op (hom_unique _ _)

/-- The two comparison paths from three successive direct images to the
direct image along the composite coefficient map agree as sheaf morphisms. -/
theorem coefficientSheafPushforwardCompIso_assoc
    (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (χ : BoundedAlgHom K C D) (F : Sheaf (finiteRationalTopology K D) E) :
    (coefficientSheafPushforwardCompIso φ ψ E).hom.app
        ((coefficientSheafPushforward χ E).obj F) ≫
        (coefficientSheafPushforwardCompIso (ψ.comp φ) χ E).hom.app F =
      (coefficientSheafPushforward φ E).map
          ((coefficientSheafPushforwardCompIso ψ χ E).hom.app F) ≫
        (coefficientSheafPushforwardCompIso φ (χ.comp ψ) E).hom.app F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  change _ =
    (((coefficientSheafPushforward φ E).map
        ((coefficientSheafPushforwardCompIso ψ χ E).hom.app F)).hom.app
        (Opposite.op d.unop)) ≫ _
  rw [coefficientSheafPushforwardCompIso_hom_app,
    coefficientSheafPushforwardCompIso_hom_app,
    coefficientSheafPushforwardCompIso_hom_app]
  dsimp [coefficientSheafPushforward, Functor.sheafPushforwardContinuous]
  rw [coefficientSheafPushforwardCompIso_hom_app]
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg F.obj.map
  exact congrArg Quiver.Hom.op (hom_unique _ _)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
