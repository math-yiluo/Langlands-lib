# Unimodularity of actual connected reductive rational-point groups

`Langlands.Aubert.General.RationalPointFamily.RationalReductiveUnimodularityStatement`
is a proposition target in arbitrary universe `u`. For every nonarchimedean
local field `k` with its supplied field, valuation and topology, and every
connected reductive group scheme `G` over `k`, it asserts that Mathlib's
`modularCharacter` on the actual identity-test group `RationalPoint k G.X`
is identically one.

The topology is exactly `RationalPointFamily.pointTopology`. Local compactness,
the nonarchimedean group structure, Hausdorffness, and the published
`StandardCocharacterStatement.{u}` remain explicit premises. Affineness is
supplied by connected reductivity. No torus, generic cocharacter, Cartan
decomposition, compact cover or character identity is part of the input.
The proposition supplies no proof of unimodularity.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
2026 French version, V.5.4, the Proposition on printed p.126 (PDF p.132),
source ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard proves unimodularity using Cartan coverage and compact open Iwahori
decompositions. Those structural assertions are proof obligations, not
premises of this target. Renard's modular function and Mathlib's modular
character have inverse conventions; their being identically one is equivalent.

This interface isolates the ambient conclusion needed for
`RationalParabolicModulusStatement` and allows it to be applied again to a
connected reductive representative of an actual standard Levi. The retained
standard-cocharacter premise matches that consumer. It does not assert
connected reductivity of a Levi representative, nor the parabolic modulus
comparison. The companion reduction explains those separate dependencies.
