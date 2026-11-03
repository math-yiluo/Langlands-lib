import Langlands.GroupScheme.ImageGenerationCommutator
import Langlands.GroupScheme.SmoothConnectedGeometryStatement
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Langlands.GroupScheme.Torus.Split

/-! # Source targets for smooth connected generated images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneratedImage

variable {B : Scheme.{u}} {G : GroupScheme B} {V : Over B} {f : V ⟶ G.X}

/-- The geometric conclusions required of an actual generated representative.
No regularity of the image or separability of `f` is assumed. -/
def HasSmoothConnectedGeneration (D : GeneratedImage f) : Prop :=
  Smooth D.group.X.hom ∧ IsAffineHom D.group.X.hom ∧
    GeometricallyConnected D.group.X.hom ∧
    ∃ n : ℕ, 0 < n ∧ IsDominant (D.powerMap n).left

end GeneratedImage

/-- General pointed-image generation over arbitrary fields and characteristic.
The existence, smoothness, connectedness and dominance are proof obligations. -/
def PointedImageGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    ∀ V : Over (Spec (CommRingCat.of k)),
    IsAffineHom V.hom → LocallyOfFiniteType V.hom → GeometricallyIntegral V.hom →
    ∀ (v₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V) (f : V ⟶ G.X),
    v₀ ≫ f = 1 →
      ∃ D : GeneratedImage f, D.HasSmoothConnectedGeneration

/-- Stability of the fixed closed envelope for a split-torus equivariant
pointed integral image. -/
def PointedImageEnvelopeStabilityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    ∀ V : Over (Spec (CommRingCat.of k)),
    IsAffineHom V.hom → LocallyOfFiniteType V.hom → GeometricallyIntegral V.hom →
    ∀ (v₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V) (f : V ⟶ G.X),
    v₀ ≫ f = 1 →
    ∀ S : CommGroupScheme (Spec (CommRingCat.of k)), IsSplitTorus S.toGrp →
    ∀ (a : PointwiseSchemeAction S.toGrp V) (b : AutomorphicAction S.toGrp G),
    a.IsEquivariant b.toPointwiseSchemeAction f → b.IsStable (closedImageEnvelope f)

/-- The invariant existence target includes the actual restricted action,
equivariant inclusion and factor, and an equivariant dominant positive power. -/
def InvariantPointedImageGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    ∀ V : Over (Spec (CommRingCat.of k)),
    IsAffineHom V.hom → LocallyOfFiniteType V.hom → GeometricallyIntegral V.hom →
    ∀ (v₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V) (f : V ⟶ G.X),
    v₀ ≫ f = 1 →
    ∀ S : CommGroupScheme (Spec (CommRingCat.of k)), IsSplitTorus S.toGrp →
    ∀ (a : PointwiseSchemeAction S.toGrp V) (b : AutomorphicAction S.toGrp G),
    a.IsEquivariant b.toPointwiseSchemeAction f →
      ∃ (D : GeneratedImage f) (c : AutomorphicAction S.toGrp D.group),
        D.HasSmoothConnectedGeneration ∧ b.IsStable (closedImageEnvelope f) ∧
        c.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction D.inclusion.hom.hom ∧
        a.IsEquivariant c.toPointwiseSchemeAction D.factor ∧
        ∃ n : ℕ, 0 < n ∧ IsDominant (D.powerMap n).left ∧
          (a.finitePower n).IsEquivariant c.toPointwiseSchemeAction (D.powerMap n)

/-- The invariant theorem follows constructively from generation and stability:
the action is the existing represented-subgroup restriction. -/
theorem invariantPointedImageGeneration_of_generation_and_stability
    (hGeneration : PointedImageGenerationStatement.{u})
    (hStability : PointedImageEnvelopeStabilityStatement.{u}) :
    InvariantPointedImageGenerationStatement.{u} := by
  intro k _ G hG hAff V hVAff hVFin hVInt v₀ f hv₀ S hS a b hf
  obtain ⟨D, hD⟩ := hGeneration k G hG hAff V hVAff hVFin hVInt v₀ f hv₀
  have hStable := hStability k G hG hAff V hVAff hVFin hVInt v₀ f hv₀ S hS a b hf
  refine ⟨D, D.action b hStable, hD, hStable, D.inclusion_equivariant b hStable,
    D.factor_equivariant b hStable a hf, ?_⟩
  obtain ⟨n, hn, hDom⟩ := hD.2.2.2
  exact ⟨n, hn, hDom, D.powerMap_equivariant b hStable a hf n⟩

/-- All general geometric source obligations of the pointed-image
infrastructure, excluding the special commutator weight bound. -/
def ImageGenerationSourceStatement : Prop :=
  SmoothConnectedAffineGeometryStatement.{u} ∧ PointedImageGenerationStatement.{u} ∧
    PointedImageEnvelopeStabilityStatement.{u}

end Langlands.GroupScheme
