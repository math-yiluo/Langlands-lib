import Langlands.Representation.Exponents.DiscreteSeriesEmbeddingStandardReductionStatement
import Langlands.Representation.Exponents.LeviConjugateEmbedding
import Langlands.GroupScheme.Rational.ParabolicLeviStandardConjugation
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Standard parabolic witnesses for discrete-series embeddings -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- A discrete-series induction embedding of an irreducible representation
can be realized in any fixed standard parabolic and Levi family. -/
theorem discreteSeriesEmbeddingStandardReduction :
    DiscreteSeriesEmbeddingStandardReductionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ T i ν hi hν π hπ
  constructor
  · rintro ⟨P, M, U, p, l, r, hp, hl, hr, hmul, σ, hσ, hsq, hf⟩
    obtain ⟨g, J, ζ, hζ, hP, hM, _, _⟩ :=
      parabolicLeviStandardConjugatingPoint
        parabolicDynamic dynamicGeometricUnipotentRadical smoothMaximalSplitTorusConjugacy
        hG hi (relativeRootSystem k G hG T i hi) hν p l hp hl
    have := hl.isConnectedReductive.isAffineHom
    let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    let e : M ≅ M := Iso.refl M
    have hρ : Representation.Equiv σ.representation
        (σ.representation.comp (rationalPoints.map e.hom)) := by
      refine Representation.Equiv.mk (LinearEquiv.refl ℂ _) ?_
      intro m
      have hm : rationalPoints.map e.hom m = m := by
        rw [rationalPoints.map_apply]
        change m ≫ 𝟙 M.X = m
        exact Category.comp_id m
      ext x
      change σ.representation m x = σ.representation (rationalPoints.map e.hom m) x
      rw [hm]
    have hM' : SubgroupFunctor.range ((e.hom ≫ l) ≫ p ≫ (G.innerIso g).hom) =
        standardLevi i ν J := by
      simpa only [e, Iso.refl_hom, Category.id_comp] using hM
    exact ⟨J, hζ.subset, P, M, U, p ≫ (G.innerIso g).hom, e.hom ≫ l, r,
      hp.comp_iso (G.innerIso g), hl.iso_comp e, hr,
      isIso_subgroupMultiplication_iso_comp e (l := l) (r := r) hmul,
      hP, hM', σ, hσ, hsq, exists_embedding_conjugate_presentation
        hG p l r hp hl hr hmul e g σ σ hρ π hπ hf⟩
  · rintro ⟨J, _, P, M, U, p, l, r, hp, hl, hr, hmul, _, _, hσ⟩
    exact ⟨P, M, U, p, l, r, hp, hl, hr, hmul, hσ⟩

end Langlands.Aubert.General.RepresentedParabolic
