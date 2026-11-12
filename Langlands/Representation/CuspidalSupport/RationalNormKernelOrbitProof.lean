import Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RestrictionConstituentExistence
import Langlands.Representation.CuspidalSupport.NormalRestrictionOrbit

/-! # Renard VI.3.2(i)

The irreducible constituents of the restriction of an irreducible smooth
representation to the rational common norm kernel exist and form one orbit under
inverse conjugation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV

/-- **Renard VI.3.2(i)**: the restriction of an irreducible smooth complex
representation of the rational points of a connected reductive group to the rational
common norm kernel has an irreducible subrepresentation, ambient translates of
irreducible subrepresentations are irreducible with the inverse-conjugated action,
and any two irreducible subrepresentations are related by such a translate. -/
theorem rationalNormKernelOrbit : RationalNormKernelOrbitStatement.{u, uV} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  let : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro π hπ
  refine ⟨rationalNormKernelConstituent_of_finiteRestriction
      rationalNormKernelFiniteRestriction.{u, uV} F G hG π hπ, ?_, ?_⟩
  · intro W hW g
    exact NormalRestrictionOrbit.covariance π.representation
      (Plancherel.rationalCommonNormKernel G) W hW g
  · intro W₁ W₂ hW₁ hW₂
    exact NormalRestrictionOrbit.singleOrbit π.representation
      (Plancherel.rationalCommonNormKernel G) hπ W₁ W₂ hW₁ hW₂

end Langlands.CuspidalSupport
