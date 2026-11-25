import Langlands.Sheaf.Equivariant.TwistedInductionCoordinates

/-!
# Transport in the coordinates of twisted induction
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG uA vA

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] (ρ : G →* Aut X)

/-- The ordinary translated arrow underlying transport of a coordinate. -/
def transport {U V : TwistedOver P ρ} (f : U ⟶ V) (g : G) :
    (translate P ρ g).obj U.obj ⟶ (translate P ρ (g * (Hom.twist f)⁻¹)).obj V.obj :=
  MorphismProperty.Over.homMk (Hom.left (U := U) (V := V) f) (by
    change Hom.left f ≫ (V.hom ≫ (ρ (g * (Hom.twist f)⁻¹)).asIso.hom) = U.hom ≫ (ρ g).asIso.hom
    rw [← Category.assoc, Hom.w, Category.assoc, ← rho_mul_hom, inv_mul_cancel_right])

/-- Transport factors through the inverse relabelling with the reindexed label. -/
theorem relabelInv_comp {U V : TwistedOver P ρ} (f : U ⟶ V) (g : G) :
    relabelInv ρ g U.obj ≫ f =
      (ι P ρ).map (transport ρ f g) ≫ relabelInv ρ (g * (Hom.twist f)⁻¹) V.obj := by
  apply hom_ext
  · change Hom.twist f * g⁻¹ = (g * (Hom.twist f)⁻¹)⁻¹ * 1
    simp
  · change 𝟙 _ ≫ Hom.left f = Hom.left f ≫ 𝟙 _
    simp

variable {A : Type uA} [Category.{vA} A]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- A twisted arrow reindexes the projections by right multiplication by its inverse twist. -/
@[reassoc]
theorem map_projection (F : (P.Over ⊤ X)ᵒᵖ ⥤ A) {U V : TwistedOver P ρ}
    (f : U ⟶ V) (g : G) :
    ((ι P ρ).op.ran.obj F).map f.op ≫ projection ρ F U g =
      projection ρ F V (g * (Hom.twist f)⁻¹) ≫ F.map (transport ρ f g).op := by
  dsimp only [projection, objects]
  rw [← Functor.map_comp_assoc, ← op_comp, relabelInv_comp ρ f g, op_comp,
    Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  congr 1
  exact ((ι P ρ).op.ranCounit.app F).naturality (transport ρ f g).op

end Langlands.Sheaf.Equivariant.TwistedOver.InductionCoordinates
