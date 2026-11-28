import Langlands.Representation.Aubert.General.InducedCuspidalSupportCategoryReduction
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionFromSpecialVertex
import Langlands.Representation.CuspidalSupport.RationalCuspidalInertiaDecompositionReduction
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Induced inside-Levi cuspidal representations lie in `Alg({K})`

Renard, proof of Théorème VI.7.2 (printed p. 183), on the actual standard
rational-point families: the actual normalized induction of a smooth
representation of an actual standard Levi that is cuspidal inside that Levi
lies in the actual support category of that Levi. -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Renard, proof of Théorème VI.7.2: for every nonarchimedean local field,
connected reductive group, maximal split torus, generic cocharacter and standard
index `K`, the actual normalized induction `i_{L_K}(τ)` of an arbitrary smooth
representation `τ` of the actual standard Levi `L_K` that is cuspidal inside
`L_K` lies in `Alg({K})` for the actual root association. The special-vertex
inputs come from the joint special compact basis
(`Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence`); they
give the proper-standard exclusion, which together with the geometric filtration
of `r_J i_K(τ)` proves the statement. -/
theorem rationalInducedCuspidalSupportCategory :
    RationalInducedCuspidalSupportCategoryStatement.{u, v} :=
  rationalInducedCuspidalSupportCategory_of_extractionInputs.{u, v}
    (rationalCuspidalExtractionInputs_of_specialVertexInputs.{u, v}
      (Langlands.CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis.{u}
        Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{u}))

end Langlands.Aubert.General.RationalPointFamily
