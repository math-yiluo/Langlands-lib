# Proof of `Langlands.GroupScheme.PseudoReductiveCentralCocharacterStatement`

This module proves the published proposition `Langlands.GroupScheme.PseudoReductiveCentralCocharacterStatement` (module `Langlands.GroupScheme.Dynamic.PseudoReductiveCentralCocharacterStatement`) at every universe `u`. The statement says that for a pseudo-reductive group `G` over a field and a cocharacter `χ`, `Dynamic.parabolic χ = ⊤` if and only if `Dynamic.centralizer χ = ⊤` (Conrad–Gabber–Prasad, Lemma 2.2.3(2)).

The theorem is `Langlands.GroupScheme.pseudoReductiveCentralCocharacter : PseudoReductiveCentralCocharacterStatement.{u}`, with no hypotheses.

## Proof

A short tactic proof: `IsPseudoReductive G` supplies smoothness, an affine structure map (hence an affine underlying scheme, by Mathlib's `AlgebraicGeometry.isAffine_of_isAffineHom`) and a trivial ground-field unipotent radical. The published `Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent` gives the equivalence from that radical condition and a closed unipotent subgroup representing `U(χ)`. The representative is `Dynamic.Affine.unipotentHom χ`: `Dynamic.Affine.isRepresentedBy_unipotentHom` and `Dynamic.Affine.isClosedSubgroup_unipotentHom` give representability and closedness, and `dynamicUnipotentUnipotence` gives unipotence.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent` (module `Langlands.GroupScheme.Dynamic.TrivialUnipotentCentralizer`)
- `Langlands.GroupScheme.Dynamic.Affine.isRepresentedBy_unipotentHom` (module `Langlands.GroupScheme.Dynamic.AffineRepresentability`)
- `Langlands.GroupScheme.Dynamic.Affine.isClosedSubgroup_unipotentHom` (module `Langlands.GroupScheme.Dynamic.AffineRepresentability`)
- `Langlands.GroupScheme.dynamicUnipotentUnipotence` (module `Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof`)
