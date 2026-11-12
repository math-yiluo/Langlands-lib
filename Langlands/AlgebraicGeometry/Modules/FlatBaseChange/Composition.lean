import Langlands.Cohomology.ExactBaseChange.ResolutionMap
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageBaseChange
import Langlands.AlgebraicGeometry.Modules.PushforwardBaseChangeComposition
import Langlands.Cohomology.AcyclicResolution.ExactComparison
import Langlands.Cohomology.AcyclicResolution.Lift

/-!
# Invertibility of base change transformations across composed squares

For two commutative squares `p ≫ f = f' ≫ b` and `q ≫ f' = f'' ≫ c` with exact pullbacks, if the
base change transformation of the second square is invertible at `p^* M`, then `c^*` of the
component at `M` of the first square's transformation is invertible exactly when the component at
`M` of the composite square's transformation is. The proof computes all three transformations with
injective resolutions through the resolution compatibility statement; the cochain map of the
composite square factors through those of the two squares by the degree-zero composition law
`pushforwardBaseChange_composition`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.FlatBaseChange

open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
open Langlands.Cohomology.ExactBaseChange
open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {S S' S'' X X' X'' : Scheme.{u}}
  (b : S' ⟶ S) (c : S'' ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S') (f'' : X'' ⟶ S'')
  (p : X' ⟶ X) (q : X'' ⟶ X') (w : p ≫ f = f' ≫ b) (v : q ≫ f' = f'' ≫ c)

/-- The degree-zero base change map of the composite square, solved from
`pushforwardBaseChange_composition`. -/
lemma pushforwardBaseChange_composite_eq (N : X.Modules) :
    pushforwardBaseChange (c ≫ b) f f'' (q ≫ p) (compositeBaseChangeSquare b c f f' f'' p q w v)
        N =
      (Scheme.Modules.pullbackComp c b).inv.app _ ≫
        (Scheme.Modules.pullback c).map (pushforwardBaseChange b f f' p w N) ≫
        pushforwardBaseChange c f' f'' q v ((Scheme.Modules.pullback p).obj N) ≫
        (Scheme.Modules.pushforward f'').map ((Scheme.Modules.pullbackComp q p).hom.app N) := by
  rw [← Iso.app_inv, Iso.eq_inv_comp, Iso.app_hom, pushforwardBaseChange_composition]
  rfl

variable [PreservesFiniteLimits (Scheme.Modules.pullback b)]
  [PreservesFiniteLimits (Scheme.Modules.pullback c)]
  [PreservesFiniteLimits (Scheme.Modules.pullback (c ≫ b))]
  [PreservesFiniteLimits (Scheme.Modules.pullback p)]
  [PreservesFiniteLimits (Scheme.Modules.pullback q)]
  [PreservesFiniteLimits (Scheme.Modules.pullback (q ≫ p))]

/-- **Composition of squares.** If the base change transformation of the square
`q ≫ f' = f'' ≫ c` is invertible at `p^* M`, then `c^*` of the component at `M` for the square
`p ≫ f = f' ≫ b` is invertible exactly when the component at `M` for the composite square is.
-/
theorem isIso_pullback_map_higherDirectImageBaseChange_iff (M : X.Modules) (n : ℕ)
    (hB : IsIso ((higherDirectImageBaseChangeNatTrans c f' f'' q v n).app
      ((Scheme.Modules.pullback p).obj M))) :
    IsIso ((Scheme.Modules.pullback c).map
        ((higherDirectImageBaseChangeNatTrans b f f' p w n).app M)) ↔
      IsIso ((higherDirectImageBaseChangeNatTrans (c ≫ b) f f'' (q ≫ p)
        (compositeBaseChangeSquare b c f f' f'' p q w v) n).app M) := by
  let I₀ := injectiveResolution M
  let I₁ := injectiveResolution ((Scheme.Modules.pullback p).obj M)
  let I₂ := injectiveResolution
    ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback p).obj M))
  let ψ₁ := lift (mapResolutionAugmentation (Scheme.Modules.pullback p) I₀.ι) (𝟙 _) I₁.ι
  have hψ₁ : mapResolutionAugmentation (Scheme.Modules.pullback p) I₀.ι ≫ ψ₁ = I₁.ι := by
    rw [comp_lift, CategoryTheory.Functor.map_id, Category.id_comp]
  let ψ₂ := lift (mapResolutionAugmentation (Scheme.Modules.pullback q) I₁.ι) (𝟙 _) I₂.ι
  have hψ₂ : mapResolutionAugmentation (Scheme.Modules.pullback q) I₁.ι ≫ ψ₂ = I₂.ι := by
    rw [comp_lift, CategoryTheory.Functor.map_id, Category.id_comp]
  let e := Scheme.Modules.pullbackComp q p
  let ε'' := (CochainComplex.single₀ X''.Modules).map (e.inv.app M) ≫ I₂.ι
  let ψ'' : ((Scheme.Modules.pullback (q ≫ p)).mapHomologicalComplex _).obj I₀.cocomplex ⟶
      I₂.cocomplex :=
    (NatTrans.mapHomologicalComplex e.inv _).app I₀.cocomplex ≫
      ((Scheme.Modules.pullback q).mapHomologicalComplex _).map ψ₁ ≫ ψ₂
  have hψ'' : mapResolutionAugmentation (Scheme.Modules.pullback (q ≫ p)) I₀.ι ≫ ψ'' = ε'' := by
    apply HomologicalComplex.from_single_hom_ext
    have h₁ := congrArg (fun φ => HomologicalComplex.Hom.f φ 0) hψ₁
    have h₂ := congrArg (fun φ => HomologicalComplex.Hom.f φ 0) hψ₂
    simp only [HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero] at h₁ h₂
    simp only [ψ'', ε'', HomologicalComplex.comp_f, mapResolutionAugmentation_f_zero,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
      CochainComplex.single₀_map_f_zero]
    have hn := e.inv.naturality (I₀.ι.f 0)
    have h₃ : (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback p).map (I₀.ι.f 0)) ≫
        (Scheme.Modules.pullback q).map (ψ₁.f 0) ≫ ψ₂.f 0 = I₂.ι.f 0 := by
      rw [← Functor.map_comp_assoc, h₁, h₂]
    rw [reassoc_of% hn]
    erw [h₃]
    rfl
  have : QuasiIso ε'' := by dsimp only [ε'']; infer_instance
  let τA := pushforwardBaseChangeNatTrans b f f' p w
  let τB := pushforwardBaseChangeNatTrans c f' f'' q v
  let τC := pushforwardBaseChangeNatTrans (c ≫ b) f f'' (q ≫ p)
    (compositeBaseChangeSquare b c f f' f'' p q w v)
  let E := (NatTrans.mapHomologicalComplex (Scheme.Modules.pullbackComp c b).inv
    (ComplexShape.up ℕ)).app (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj
      I₀.cocomplex)
  have : ∀ k, IsIso (E.f k) := fun k => by
    simp only [E, NatTrans.mapHomologicalComplex_app_f]
    infer_instance
  have : IsIso E := HomologicalComplex.Hom.isIso_of_components E
  have hΦ : resolutionBaseChangeMap τC ψ'' = E ≫
      ((Scheme.Modules.pullback c).mapHomologicalComplex _).map
        (resolutionBaseChangeMap τA ψ₁) ≫ resolutionBaseChangeMap τB ψ₂ := by
    refine HomologicalComplex.hom_ext _ _ (fun k => ?_)
    simp only [E, ψ'', τA, τB, τC, resolutionBaseChangeMap_f,
      HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, pushforwardBaseChangeNatTrans_app]
    rw [pushforwardBaseChange_composite_eq b c f f' f'' p q w v]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc (Scheme.Modules.pushforward f'')
      ((Scheme.Modules.pullbackComp q p).hom.app _), Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id,
      Category.id_comp, ← pushforwardBaseChange_naturality_assoc]
    rfl
  have hK₀ : ∀ k r : ℕ, IsZero (((Scheme.Modules.pushforward f).rightDerived (r + 1)).obj
      (I₀.cocomplex.X k)) := fun k r =>
    (Scheme.Modules.pushforward f).isZero_rightDerived_obj_injective_succ r _
  have hK₁ : ∀ k r : ℕ, IsZero (((Scheme.Modules.pushforward f').rightDerived (r + 1)).obj
      (I₁.cocomplex.X k)) := fun k r =>
    (Scheme.Modules.pushforward f').isZero_rightDerived_obj_injective_succ r _
  have hK₂ : ∀ k r : ℕ, IsZero (((Scheme.Modules.pushforward f'').rightDerived (r + 1)).obj
      (I₂.cocomplex.X k)) := fun k r =>
    (Scheme.Modules.pushforward f'').isZero_rightDerived_obj_injective_succ r _
  have hA_iff := isIso_map_baseChangeNatTrans_app_iff τA I₀.ι I₁.ι ψ₁ hψ₁ hK₀ hK₁
    (Scheme.Modules.pullback c) n
  have hB_iff := isIso_map_baseChangeNatTrans_app_iff τB I₁.ι I₂.ι ψ₂ hψ₂ hK₁ hK₂
    (𝟭 _) n
  have hC_iff := isIso_map_baseChangeNatTrans_app_iff τC I₀.ι ε'' ψ'' hψ'' hK₀ hK₂
    (𝟭 _) n
  simp only [Functor.id_map] at hB_iff hC_iff
  have : IsIso ((HomologicalComplex.homologyFunctor _ _ n).map
    (resolutionBaseChangeMap τB ψ₂)) := hB_iff.1 hB
  change IsIso ((Scheme.Modules.pullback c).map ((baseChangeNatTrans τA n).app M)) ↔
    IsIso ((baseChangeNatTrans τC n).app M)
  rw [hA_iff, hC_iff, hΦ, Functor.map_comp, Functor.map_comp, isIso_comp_left_iff,
    isIso_comp_right_iff]
  have hnat := (LeftExactHomology.homologyNatTrans (Scheme.Modules.pullback c)
    (ComplexShape.up ℕ) n).naturality (resolutionBaseChangeMap τA ψ₁)
  simp only [Functor.comp_map] at hnat
  rw [← IsIso.eq_comp_inv] at hnat
  rw [hnat, isIso_comp_right_iff, isIso_comp_left_iff]

end Langlands.AlgebraicGeometry.Modules.FlatBaseChange
