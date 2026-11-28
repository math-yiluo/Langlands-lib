import Langlands.Representation.Exponents.RepresentedSupercuspidalSubquotientRealizationReduction
import Langlands.Representation.Exponents.RepresentedSupercuspidalCompactRestrictionReduction
import Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.Representation.Plancherel.SplitComponentLatticeProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Renard VI.3.6, Lemma: realization of an admissible supercuspidal subquotient

Renard 2026, VI.3.6, Lemma (printed pp.147–148 / PDF pp.153–154), for every
connected reductive group over every nonarchimedean local field: an irreducible
supercuspidal smooth subquotient of an admissible smooth representation is both
a subrepresentation and a quotient of it.

The proof composes two reductions with proved structural statements.
`representedSupercuspidalSubquotientRealizationReduction` derives the lemma
from the finite index of `⁰G ⊔ Z(G)` and from compactly supported smooth-dual
coefficients of the restriction of the subquotient to the common norm kernel
`⁰G`. The finite index is `finiteIndex_rationalCommonNormKernel_sup_center`
applied to the split-component lattice theorem; the coefficient condition is
`representedSupercuspidalCompactRestrictionReduction` applied to the proved
parabolic-dynamic, standard-cocharacter, relative-root-system and joint
special-compact-basis statements.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.3.6, Lemma: for every nonarchimedean local field `k`, every
connected reductive group `G` over `k` with the canonical topology on its
rational points, and smooth complex representations `π` and `τ` of `G(k)` with
`π` admissible and `τ` irreducible, supercuspidal (the normalized Jacquet module
of `τ` vanishes for every proper rational parabolic) and a subquotient of `π`,
the representation `τ` is a subrepresentation and a quotient of `π`. -/
theorem representedSupercuspidalSubquotientRealization :
    RepresentedSupercuspidalSubquotientRealizationStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ π τ hπ hτ hsc hτπ
  exact representedSupercuspidalSubquotientRealizationReduction k G hG π τ
    (finiteIndex_rationalCommonNormKernel_sup_center
      Plancherel.RenardCartan.splitComponentLattice G hG)
    hπ hτ
    (representedSupercuspidalCompactRestrictionReduction parabolicDynamic
      standardCocharacter relativeRootSystem
      BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence k G hG τ hsc)
    hτπ

end Langlands.Aubert.General.RepresentedParabolic
