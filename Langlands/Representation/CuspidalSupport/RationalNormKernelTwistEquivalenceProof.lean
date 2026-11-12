import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.CuspidalSupport.NormKernelTwistEquivalence
import Langlands.Representation.CuspidalSupport.RationalPointCentralCharacter
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex

/-!
# Renard VI.3.2(iii) on the actual norm kernel

The published generic twist equivalence is applied to the actual rational-point
group. Its inputs are the open norm kernel, its commutator containment, finite
index of the norm kernel joined with the centre, and the scalar central action
on irreducible smooth representations.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV uW

/-- Renard VI.3.2(iii): for irreducible smooth representations of the actual
rational-point group, isomorphic restrictions to the actual norm kernel, an
unramified twist equivalence and a nonzero restricted intertwiner are
equivalent. -/
theorem rationalNormKernelTwistEquivalence :
    RationalNormKernelTwistEquivalenceStatement.{u, uV, uW} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  have : (Plancherel.commonNormKernel
      (fun χ => (Plancherel.rationalNormCharacters G χ).toMul) ⊔
      Subgroup.center (GroupScheme.rationalPoints G)).FiniteIndex :=
    rationalCommonNormKernel_sup_center_finiteIndex F G hG
  intro π₁ π₂ h₁ h₂
  exact normKernelTwistEquivalence_of_finiteIndex_scalar
    (fun χ => (Plancherel.rationalNormCharacters G χ).toMul)
    (Plancherel.isOpen_rationalCommonNormKernel G)
    (Plancherel.commutator_le_rationalCommonNormKernel G)
    π₁.representation π₂.representation h₁ h₂
    (exists_scalar_rationalPoint_center F G hG π₁ h₁)
    (exists_scalar_rationalPoint_center F G hG π₂ h₂)

end Langlands.CuspidalSupport
