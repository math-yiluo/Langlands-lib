import Langlands.Geometry.Analytic.InducedAnalyticSpace
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Induction of analytic spaces as a left adjoint of restriction -/

noncomputable section

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)

theorem homEquiv_naturality (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)
    {Y Y' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G}
    (g : Y ⟶ Y') (ψ : inducedAction H X ⟶ Y) :
    homEquiv H (ψ ≫ g) = homEquiv H ψ ≫ (Action.res _ H.subtype).map g := by
  rw [homEquiv_apply, homEquiv_apply, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Induction `X ↦ X_{G/H}` as a functor from `H`-objects to `G`-objects. On morphisms it is
determined by the universal property. -/
abbrev inductionFunctor :
    Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H ⥤
      Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G :=
  Adjunction.leftAdjointOfEquiv (G := Action.res _ H.subtype)
    (fun X _ => homEquiv H (X := X)) (fun X _ _ g ψ => homEquiv_naturality H X g ψ)

@[simp]
theorem inductionFunctor_obj (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H) :
    (inductionFunctor H).obj X = inducedAction H X := rfl

/-- Induction is left adjoint to restriction along `H → G`. -/
def inductionAdjunction : inductionFunctor.{u, v} (K := K) H ⊣ Action.res _ H.subtype :=
  Adjunction.adjunctionOfEquivLeft _ _

theorem inductionAdjunction_homEquiv
    (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)
    (Y : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G) :
    (inductionAdjunction H).homEquiv X Y = homEquiv H := by
  unfold inductionAdjunction Adjunction.adjunctionOfEquivLeft
  rw [Adjunction.mkOfHomEquiv_homEquiv]

theorem inductionFunctor_map
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X') :
    (inductionFunctor H).map f = lift H (f ≫ unit H X') := by
  change lift H (f ≫ homEquiv H (𝟙 _)) = _
  rw [homEquiv_apply, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The extension of `a` followed by the unit sends the copy `c` to the copy `c` by `a`. -/
theorem copy_liftHom_unitHom
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (a : X.V ⟶ X'.V)
    (c : G ⧸ H) :
    copy H X c ≫ liftHom H (Y := inducedAction H X') (a ≫ unitHom H X') = a ≫ copy H X' c := by
  rw [copy_liftHom, Category.assoc, unitHom, Category.assoc]
  change a ≫ X'.ρ (baseRep H)⁻¹ ≫ copy H X' (baseCoset H) ≫ actionMap H X' c.out = _
  rw [copy_actionMap, correction_out_baseCoset, out_smul_baseCoset, ρ_comp_assoc,
    mul_inv_cancel, Action.ρ_one, Category.id_comp]

/-- On the copy indexed by `c`, the induced morphism is `f` followed by the inclusion of the
copy `c`. -/
theorem copy_inductionFunctor_map
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X')
    (c : G ⧸ H) :
    copy H X c ≫ ((inductionFunctor H).map f).hom = f.hom ≫ copy H X' c := by
  rw [inductionFunctor_map, lift_hom]
  exact copy_liftHom_unitHom H f.hom c

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
