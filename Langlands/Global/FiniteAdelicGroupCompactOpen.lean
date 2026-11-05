import Langlands.Global.RepresentationGrowth
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact
import Langlands.GroupScheme.AffinePointClosedImmersion
import Langlands.GroupScheme.AffineLinearEmbeddingCorepresentedProof

/-! # Compact open subgroups of the actual finite adelic point group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))

/-- Evaluate the specified representation on the original finite adelic points. -/
def finiteMatrix : FiniteAdelicGroupPoints F G →ₜ* FiniteAdelicGL F N where
  toMonoidHom := (GeneralLinearGroupPoints.finiteHomeomorph F N).toMonoidHom.comp
    (G.affinePointsTarget rho (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)))
  continuous_toFun := (GeneralLinearGroupPoints.finiteHomeomorph F N).continuous.comp
    (G.continuous_affinePointsTarget (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) rho)

/-- The preimage of the actual standard integral matrix subgroup is open. -/
def finiteIntegralOpenSubgroup : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
  (FiniteAdelicGL.standardIntegral F N).comap (finiteMatrix F G rho).toMonoidHom
    (finiteMatrix F G rho).continuous

/-- Closed scheme embeddings give closed embeddings on actual finite adelic points. -/
theorem isClosedEmbedding_finiteMatrix [IsClosedImmersion rho.hom.hom.left] :
    IsClosedEmbedding (finiteMatrix F G rho) := by
  let : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs
    (T2Space (Πʳ v : FinitePlace F, [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : IsAffine (Langlands.GroupScheme.GeneralLinear.groupScheme
      (Fin N) (CommRingCat.of F)).X.left :=
    Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin N) (CommRingCat.of F)
  exact (GeneralLinearGroupPoints.finiteHomeomorph F N).isClosedEmbedding.comp
    (G.isClosedEmbedding_affinePointsTarget _
      (CommAlgCat.of F (FiniteAdeleRing (𝓞 F) F)) rho)

/-- Pullback of the standard integral subgroup is compact for a closed representation. -/
theorem isCompact_finiteIntegralOpenSubgroup [IsClosedImmersion rho.hom.hom.left] :
    IsCompact (finiteIntegralOpenSubgroup F G rho : Set (FiniteAdelicGroupPoints F G)) :=
  (isClosedEmbedding_finiteMatrix F G rho).isCompact_preimage
    (FiniteAdelicGL.isCompact_standardIntegral F N)

end Langlands.Global.RepresentationGrowth

namespace Langlands.Global.FiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- Existence is supplied by the proved algebraic closed linear embedding theorem. -/
theorem exists_isCompact_openSubgroup :
    ∃ C : OpenSubgroup (FiniteAdelicGroupPoints F G),
      IsCompact (C : Set (FiniteAdelicGroupPoints F G)) := by
  obtain ⟨N, rho, hrho⟩ := Langlands.GroupScheme.affineLinearEmbeddingStatement_viaCorepresented
    F G (inferInstance : IsAffineHom G.X.hom) (inferInstance : LocallyOfFiniteType G.X.hom)
  let : IsClosedImmersion rho.hom.hom.left := hrho
  exact ⟨RepresentationGrowth.finiteIntegralOpenSubgroup F G rho,
    RepresentationGrowth.isCompact_finiteIntegralOpenSubgroup F G rho⟩

/-- Choose one actual compact open subgroup; no linear representation is part of its type. -/
def compactOpenSubgroup : OpenSubgroup (FiniteAdelicGroupPoints F G) :=
  (exists_isCompact_openSubgroup F G).choose

theorem isCompact_compactOpenSubgroup :
    IsCompact (compactOpenSubgroup F G : Set (FiniteAdelicGroupPoints F G)) :=
  (exists_isCompact_openSubgroup F G).choose_spec

end Langlands.Global.FiniteAdelicGroupPoints
