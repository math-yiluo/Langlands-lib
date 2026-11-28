import Langlands.Representation.Exponents.RepresentedSupercuspidalCentralProjectivityReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.Representation.Plancherel.SplitComponentLatticeProof

/-! # Renard VI.3.6, Proposition: proof

An irreducible supercuspidal representation of `G(F)` with central character `χ` is
projective and injective in the full subcategory `M(G)_χ` of smooth representations on
which the centre acts through `χ` (Renard 2026, VI.3.6, the Proposition after the Lemma,
printed p.148 / PDF p.154), for every connected reductive group over every nonarchimedean
local field. The theorem applies
`representedSupercuspidalCentralProjectivity_of_structure` to the Library's proofs of its
five structural premises.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VI.3.6, Proposition, for all actual connected reductive groups: an irreducible
smooth representation of `G(F)` with central character `χ`, whose Jacquet modules along all
proper actual rational parabolics vanish, is projective and injective in the full
subcategory of smooth representations on which the centre of `G(F)` acts through `χ`. -/
theorem representedSupercuspidalCentralProjectivity :
    RepresentedSupercuspidalCentralProjectivityStatement.{u, v} :=
  representedSupercuspidalCentralProjectivity_of_structure
    Langlands.GroupScheme.parabolicDynamic
    Langlands.GroupScheme.standardCocharacter
    Langlands.GroupScheme.relativeRootSystem
    Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
    Langlands.Plancherel.RenardCartan.splitComponentLattice

end Langlands.Aubert.General.RepresentedParabolic
