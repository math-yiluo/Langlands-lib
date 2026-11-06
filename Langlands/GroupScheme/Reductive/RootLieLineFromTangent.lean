import Langlands.GroupScheme.Rational.RootParabolicProper
import Langlands.GroupScheme.Absolute.RootVectorLineStructuralAssembly
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Torus.WeightSpaceScalarExtension
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Actual root Lie lines from intrinsic root tangent bounds -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

section Tangent

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- A nonzero actual root weight has dimension one if the whole intrinsic
root tangent has dimension at most one. -/
theorem finrank_weightSpace_eq_one_of_rootTangent_le_one
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (χ : characterLattice T) (hχ : χ ∈ roots i)
    (hdim : Module.finrank k
      (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup i χ)) ≤ 1) :
    Module.finrank k (weightSpace i χ) = 1 := by
  let : Nontrivial (weightSpace i χ) :=
    Submodule.nontrivial_iff_ne_bot.mpr hχ.2
  have hpos : 0 < Module.finrank k (weightSpace i χ) := Module.finrank_pos
  have hle : Module.finrank k (weightSpace i χ) ≤
      Module.finrank k (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup i χ)) :=
    Submodule.finrank_mono
    (RelativeRoot.weightSpace_le_tangentSubmodule_subgroup i hT hχ.1)
  omega

/-- Choose an actual linear trivialization of the original root weight
space from the intrinsic tangent bound. -/
def rootLieLineOfTangentBound
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (χ : characterLattice T) (hχ : χ ∈ roots i)
    (hdim : Module.finrank k
      (RelativeRoot.tangentSubmodule (RelativeRoot.subgroup i χ)) ≤ 1) :
    k ≃ₗ[k] weightSpace i χ :=
  Classical.choice (Module.nonempty_linearEquiv_of_finrank_eq_one
    (finrank_weightSpace_eq_one_of_rootTangent_le_one hT i χ hχ hdim))

end Tangent

/-- The existing intrinsic root-tangent argument yields actual root weight
lines over algebraically closed fields from dynamic-centralizer reductivity.
The fixed-point, projective-dimension and solvable-quotient inputs are proved
imports, while the centralizer input remains explicit. -/
theorem rootLieLine_of_dynamicCentralizerReductive
    (hDyn : DynamicCentralizerReductiveStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) :
    letI := hG.isAffineHom
    ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro χ hχ
  have hdim := absoluteRootTangent_le_one_of_structuralInputs
    solvableProperFixedPoint projectiveTorusFixedPointDimension solvableTorusQuotient
    hDyn k G hG T i ⟨hT, hi.2.1⟩ hi χ hχ
  exact ⟨rootLieLineOfTangentBound hT i χ hχ hdim⟩

set_option maxHeartbeats 800000 in
/-- Actual root Lie lines over arbitrary fields reduce to two explicit
structural inputs. Extension to the algebraic closure supplies the tangent
bound, and the actual weight-space scalar-extension comparison reflects the
line back to the original field. -/
theorem rootLieLine_of_twoStructuralInputs
    (hDyn : DynamicCentralizerReductiveStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) :
    letI := hG.isAffineHom
    ∀ χ ∈ roots i, Nonempty (k ≃ₗ[k] weightSpace i χ) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro χ hχ
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let GK := (GroupScheme.baseChange b).obj G
  let TK := (CommGroupScheme.baseChange b).obj T
  let iK : TK.toGrp ⟶ GK := (GroupScheme.baseChange b).map i
  have hGK : IsConnectedReductive GK := connectedReductiveFieldExtensionStatement k K G hG
  let : IsAffineHom GK.X.hom := hGK.isAffineHom
  have hiK : IsMaximalTorus iK := (hmax k K G T i hi.1 hi.2.1).mp hi
  have hTK : IsSplitTorus TK.toGrp := hT.baseChange b
  have hχK : characterLattice.baseChange b T χ ∈ roots iK :=
    (mem_roots_baseChange_iff (K := K) G T hT i χ).mpr hχ
  have hline := rootLieLine_of_dynamicCentralizerReductive hDyn K GK hGK
    TK hTK iK hiK (characterLattice.baseChange b T χ) hχK
  exact (weightSpace_line_baseChange_iff (K := K) hT i χ).mp hline

end Langlands.GroupScheme
