import Langlands.GroupScheme.RelativeLevi.ParabolicQuotientFamily
import Langlands.GroupScheme.SubgroupFunctor.ConjugateFamilyNormalizer
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Injective charts of the actual parabolic presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {G P : GroupScheme S}
    (hG : IsReductive G) (i : P ⟶ G) (hi : IsRelativeParabolicSubgroup i)
    {Q : Over S} (q : G.X ⟶ Q) [Smooth q.left] [Surjective q.left]
    (hfib : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (range i).normalizer.carrier U)

/-- The quotient family defines an actual natural parameterization of parabolics. -/
def quotientChart : (schemeYoneda S).obj Q ⟶ parabolicPresheaf G hG :=
  uliftYonedaEquiv.symm
    (quotientParabolic hG i hi q (fun U g h => (hfib U g h).mp))

/-- Evaluation of the chart is restriction of its actual quotient family. -/
theorem quotientChart_app {T : Over S} (a : T ⟶ Q) :
    (quotientChart hG i hi q hfib).app (op T) ⟨a⟩ =
      restrict hG a (quotientParabolic hG i hi q (fun U g h => (hfib U g h).mp)) := rfl

/-- An actual group-valued lift evaluates the chart to its conjugate parabolic. -/
theorem quotientChart_app_comp {T : Over S} (g : T ⟶ G.X) :
    (quotientChart hG i hi q hfib).app (op T) ⟨g ≫ q⟩ =
      conjugateParabolic hG i hi g :=
  restrict_quotientParabolic_comp hG i hi q _ g

/-- Exact full-normalizer fibers make the chart injective on every test scheme. -/
theorem quotientChart_injective (T : Over S) :
    Function.Injective ((quotientChart hG i hi q hfib).app (op T)) := by
  intro a' b' heq
  obtain ⟨a⟩ := a'
  obtain ⟨b⟩ := b'
  change restrict hG a (quotientParabolic hG i hi q _) =
    restrict hG b (quotientParabolic hG i hi q _) at heq
  apply ULift.ext
  let U₁ := pullback a q
  let r₁ : U₁ ⟶ T := pullback.fst a q
  let g₁ : U₁ ⟶ G.X := pullback.snd a q
  let U₂ := pullback (r₁ ≫ b) q
  let r₂ : U₂ ⟶ U₁ := pullback.fst (r₁ ≫ b) q
  let g₂ : U₂ ⟶ G.X := pullback.snd (r₁ ≫ b) q
  let c : U₂ ⟶ T := r₂ ≫ r₁
  have hp₁ := ((IsPullback.of_hasPullback a q).map (Over.forget S)).flip
  have hp₂ := ((IsPullback.of_hasPullback (r₁ ≫ b) q).map (Over.forget S)).flip
  let : Smooth r₁.left := MorphismProperty.of_isPullback (P := @Smooth) hp₁
    (inferInstance : Smooth q.left)
  let : Surjective r₁.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hp₁
      (inferInstance : Surjective q.left)
  let : Smooth r₂.left := MorphismProperty.of_isPullback (P := @Smooth) hp₂
    (inferInstance : Smooth q.left)
  let : Surjective r₂.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hp₂
      (inferInstance : Surjective q.left)
  let : Smooth c.left := by change Smooth (r₂.left ≫ r₁.left); infer_instance
  let : Surjective c.left := by change Surjective (r₂.left ≫ r₁.left); infer_instance
  have hc₁ : (r₂ ≫ g₁) ≫ q = c ≫ a := by
    dsimp [c, g₁, r₁]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have hc₂ : g₂ ≫ q = c ≫ b := by
    dsimp [g₂, r₂, c]
    rw [← pullback.condition, Category.assoc]
  have hfamily : conjugateParabolic hG i hi (r₂ ≫ g₁) =
      conjugateParabolic hG i hi g₂ := by
    let F := quotientParabolic hG i hi q (fun U g h => (hfib U g h).mp)
    calc
      conjugateParabolic hG i hi (r₂ ≫ g₁) =
          restrict hG ((r₂ ≫ g₁) ≫ q) F :=
        (restrict_quotientParabolic_comp hG i hi q _ (r₂ ≫ g₁)).symm
      _ = restrict hG (c ≫ a) F := congrArg (fun f => restrict hG f F) hc₁
      _ = restrict hG c (restrict hG a F) := (restrict_comp hG a c F).symm
      _ = restrict hG c (restrict hG b F) := congrArg (restrict hG c) heq
      _ = restrict hG (c ≫ b) F := restrict_comp hG b c F
      _ = restrict hG (g₂ ≫ q) F := congrArg (fun f => restrict hG f F) hc₂.symm
      _ = conjugateParabolic hG i hi g₂ :=
        restrict_quotientParabolic_comp hG i hi q _ g₂
  have hn := normalizer_of_range_conjugateFamily_eq i (r₂ ≫ g₁) g₂
    (congrArg Subtype.val hfamily)
  have hlift := (hfib U₂ (r₂ ≫ g₁) g₂).mpr hn
  have hc : c ≫ a = c ≫ b := hc₁.symm.trans (hlift.trans hc₂)
  let : Epi c.left := inferInstance
  apply Over.OverMorphism.ext
  exact (cancel_epi c.left).mp (congrArg (fun f : U₂ ⟶ Q => f.left) hc)

/-- The quotient chart is a monomorphism of actual presheaves. -/
theorem quotientChart_mono : Mono (quotientChart hG i hi q hfib) := by
  have : ∀ T, Mono ((quotientChart hG i hi q hfib).app T) := fun T =>
    ConcreteCategory.mono_of_injective _ (quotientChart_injective hG i hi q hfib T.unop)
  exact NatTrans.mono_of_mono_app _

end Langlands.GroupScheme.ParabolicSubgroupModuli
