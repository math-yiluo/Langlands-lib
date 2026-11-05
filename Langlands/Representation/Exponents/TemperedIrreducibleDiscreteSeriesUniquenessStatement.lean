import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Uniqueness of the discrete-series datum of an irreducible tempered representation

Renard 2026, VII.2.6, Theorem, second assertion (printed p.231/PDF p.237): if an
irreducible representation embeds into the normalized parabolic inductions of two
irreducible representations of Levi subgroups that are square-integrable modulo the
center, the two pairs are conjugate under `G(F)`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.2.6, Theorem, uniqueness: if an irreducible smooth representation `π`
of `G(F)` embeds into the normalized inductions of two irreducible representations `σ₁`,
`σ₂` of rational Levi subgroups `M₁`, `M₂` of actual rational parabolics, both
square-integrable modulo the center for every Haar measure, then some `g ∈ G(F)` and
some isomorphism `φ : M₁ ≅ M₂` satisfy `φ ≫ (M₂ ⟶ G) = (M₁ ⟶ G) ≫ Int(g)`, and
`σ₂ ∘ φ(F)` is isomorphic to `σ₁`. -/
def TemperedIrreducibleDiscreteSeriesUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)), π.IsIrreducible →
        ∀ (P₁ M₁ U₁ : GroupScheme (Spec (CommRingCat.of k)))
          (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁) (r₁ : U₁ ⟶ P₁)
          (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
          (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
          (hmul₁ : IsIso (subgroupMultiplication l₁ r₁)),
          haveI := hl₁.isConnectedReductive.isAffineHom
          letI : TopologicalSpace (rationalPoints M₁) := leviPointTopology l₁ hl₁
          haveI : LocallyCompactSpace (rationalPoints M₁) :=
            leviPoints_locallyCompactSpace p₁ l₁ hp₁ hl₁
          haveI : NonarchimedeanGroup (rationalPoints M₁) :=
            leviPoints_nonarchimedeanGroup p₁ l₁ hp₁ hl₁
          ∀ σ₁ : SmoothRep.{0, u, v} ℂ (rationalPoints M₁), σ₁.IsIrreducible →
            (∀ [MeasurableSpace (rationalPoints M₁ ⧸ Subgroup.center (rationalPoints M₁))]
              [BorelSpace (rationalPoints M₁ ⧸ Subgroup.center (rationalPoints M₁))]
              (haar : MeasureTheory.Measure
                (rationalPoints M₁ ⧸ Subgroup.center (rationalPoints M₁)))
              [haar.IsHaarMeasure],
              IsSquareIntegrableModCenter σ₁.representation haar) →
            (∃ f : π.representation.IntertwiningMap
                ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ₁).representation,
              Function.Injective f) →
          ∀ (P₂ M₂ U₂ : GroupScheme (Spec (CommRingCat.of k)))
            (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂) (r₂ : U₂ ⟶ P₂)
            (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
            (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
            (hmul₂ : IsIso (subgroupMultiplication l₂ r₂)),
            haveI := hl₂.isConnectedReductive.isAffineHom
            letI : TopologicalSpace (rationalPoints M₂) := leviPointTopology l₂ hl₂
            haveI : LocallyCompactSpace (rationalPoints M₂) :=
              leviPoints_locallyCompactSpace p₂ l₂ hp₂ hl₂
            haveI : NonarchimedeanGroup (rationalPoints M₂) :=
              leviPoints_nonarchimedeanGroup p₂ l₂ hp₂ hl₂
            ∀ σ₂ : SmoothRep.{0, u, v} ℂ (rationalPoints M₂), σ₂.IsIrreducible →
              (∀ [MeasurableSpace (rationalPoints M₂ ⧸ Subgroup.center (rationalPoints M₂))]
                [BorelSpace (rationalPoints M₂ ⧸ Subgroup.center (rationalPoints M₂))]
                (haar : MeasureTheory.Measure
                  (rationalPoints M₂ ⧸ Subgroup.center (rationalPoints M₂)))
                [haar.IsHaarMeasure],
                IsSquareIntegrableModCenter σ₂.representation haar) →
              (∃ f : π.representation.IntertwiningMap
                  ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ₂).representation,
                Function.Injective f) →
              ∃ (g : rationalPoints G) (φ : M₁ ≅ M₂),
                φ.hom ≫ l₂ ≫ p₂ = l₁ ≫ p₁ ≫ (G.innerIso g).hom ∧
                  ∃ T : σ₁ ≃ₗ[ℂ] σ₂, ∀ (m : rationalPoints M₁) (x : σ₁),
                    T (σ₁.representation m x) =
                      σ₂.representation (rationalPoints.map φ.hom m) (T x)

end Langlands.Aubert.General.RepresentedParabolic
