import Langlands.Shimura.RestrictedLevelTowerCanonicalCoefficients

/-! # Automorphism actions on the cohomology of a tower at a fixed level

Let `T` be a tower of schemes over levels satisfying a property, with projections `p` to a base
scheme `X`, and let a group `Γ` act on the tower by automorphisms over `X`. At every fixed level
`K`, the group `Γ` acts on the étale cohomology `H^n(T_K, p_K^* M)` of a sheaf `M` on `X`
pulled back to `T_K`: an element acts by pullback along its automorphism of `T_K`, with the
canonical comparison of the pulled-back coefficients. The action is natural in the sheaf, and the
insertion of the level-`K` cohomology into the colimit over all levels intertwines it with the
published action of `Γ` on the colimit. See `LevelAutomorphismAction.md`.
-/

noncomputable section

universe u v

namespace Langlands.Shimura.LevelAutomorphismAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Shimura.RestrictedLevelTowerCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G : Type u} [Group G] [TopologicalSpace G] {P : ObjectProperty (CompactOpenLevel G)}
  {T : P.FullSubcategory ⥤ Scheme.{u}} (R : Type u) [CommRing R] {X : Scheme.{u}}
  (p : T ⟶ (Functor.const P.FullSubcategory).obj X)
  {Γ : Type v} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ) (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

/-! ## The action at a fixed level -/

/-- The action of `Γ` on `H^n(T_K, p_K^* M)` at the level `K`: `γ` acts by pullback along its
automorphism of `T_K`, with the comparison of the pulled-back coefficients along the triangle
over `X`. -/
def levelAction (K : P.FullSubcategory) (n : ℕ) (M : ModuleSheaf X R) :
    Action (ModuleCat.{u} R) Γ where
  V := (cohomology (T.obj K) R n).obj ((inverseImage (p.app K) R).obj M)
  ρ :=
    { toFun γ := LevelTowerCohomology.projectionCohomologyMap R (p.app K) (p.app K)
        ((ρ γ).unop.hom.app K) (NatTrans.congr_app (hρ γ) K) n M
      map_one' := by
        rw [LevelTowerCohomology.projectionCohomologyMap_congr R (p.app K) (p.app K)
          (show (ρ 1).unop.hom.app K = 𝟙 (T.obj K) by
            rw [map_one, MulOpposite.unop_one]; rfl)
          _ (by rw [Category.id_comp]) n M]
        exact LevelTowerCohomology.projectionCohomologyMap_id R (p.app K) _ n M
      map_mul' γ δ := by
        rw [End.mul_def, LevelTowerCohomology.projectionCohomologyMap_comp]
        exact LevelTowerCohomology.projectionCohomologyMap_congr R _ _
          (by rw [map_mul, MulOpposite.unop_mul, Aut.Aut_mul_def, Iso.trans_hom]; rfl) _ _ n M }

theorem levelAction_ρ (K : P.FullSubcategory) (n : ℕ) (M : ModuleSheaf X R) (γ : Γ) :
    (levelAction R p ρ hρ K n M).ρ γ =
      LevelTowerCohomology.projectionCohomologyMap R (p.app K) (p.app K)
        ((ρ γ).unop.hom.app K) (NatTrans.congr_app (hρ γ) K) n M :=
  rfl

/-- The action at the level `K` is natural in the sheaf. -/
def levelActionFunctor (K : P.FullSubcategory) (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) Γ where
  obj M := levelAction R p ρ hρ K n M
  map α :=
    { hom := (cohomology (T.obj K) R n).map ((inverseImage (p.app K) R).map α)
      comm γ := (LevelTowerCohomology.projectionCohomologyMap_naturality R _ _ _ _ n α).symm }
  map_id M := Action.Hom.ext (by
    change (cohomology (T.obj K) R n).map ((inverseImage (p.app K) R).map (𝟙 M)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
  map_comp α β := Action.Hom.ext (by
    change (cohomology (T.obj K) R n).map ((inverseImage (p.app K) R).map (α ≫ β)) =
      (cohomology (T.obj K) R n).map ((inverseImage (p.app K) R).map α) ≫
        (cohomology (T.obj K) R n).map ((inverseImage (p.app K) R).map β)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp])

@[simp] theorem levelActionFunctor_obj (K : P.FullSubcategory) (n : ℕ) (M : ModuleSheaf X R) :
    (levelActionFunctor R p ρ hρ K n).obj M = levelAction R p ρ hρ K n M :=
  rfl

theorem levelActionFunctor_map_hom (K : P.FullSubcategory) (n : ℕ) {M N : ModuleSheaf X R}
    (α : M ⟶ N) :
    ((levelActionFunctor R p ρ hρ K n).map α).hom =
      (cohomology (T.obj K) R n).map ((inverseImage (p.app K) R).map α) :=
  rfl

/-! ## Comparison with the colimit over levels -/

variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
  (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
    T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
  [IsTopologicalGroup G] [IsConjStable P]

/-- The insertion of the level-`K` cohomology into the colimit over all levels intertwines the
action at the level `K` with the action of `Γ` on the colimit. -/
theorem automorphismAction_ρ_ι_apply (n : ℕ) (M : ModuleSheaf X R) (γ : Γ)
    (K : P.FullSubcategory) (x : (levelAction R p ρ hρ K n M).V) :
    SmoothRep.hom ((automorphismAction R p hT ρ hρ n M).ρ γ)
        ((RestrictedLevelColimit.ι ((canonicalCoefficients R p M).cohomology n) K).hom x) =
      (RestrictedLevelColimit.ι ((canonicalCoefficients R p M).cohomology n) K).hom
        (((levelAction R p ρ hρ K n M).ρ γ).hom x) :=
  congrArg (fun f => f.hom x) (canonicalPullback_ι R p (ρ γ).unop.hom (hρ γ) M n K)

end Langlands.Shimura.LevelAutomorphismAction
