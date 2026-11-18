# Fixed vectors of normalized induction inside a standard Levi

Module `Langlands.Representation.CuspidalSupport.StandardLeviInductionFixedVectors`.
Namespace `Langlands.CuspidalSupport`.

This is an internal derived helper for the standard-Levi form of Renard VI.10.6,
Corollary. Its provenance is the published normalized induction-in-stages
isomorphism `bernsteinStandardInductionStagesIso` and the published prescribed-level
criterion `Jacquet.nontrivial_standardInduction_fixedVectors_iff`.

`nontrivial_standardLeviInduction_fixedVectors_iff` proves the named proposition
`StandardLeviInductionFixedVectorsStatement`, over a nonarchimedean local field
with its valuation relation and topology. It considers a standard family,
standard Levis indexed by `leviIndex J I ⊆ J`, and a compact open subgroup `K`
normalized by `K₀`. It assumes the minimal Iwasawa factorization using `K₀` and
an Iwahori intersection decomposition of `K` along every standard parabolic.
For any smooth coefficient representation at carrier universe `max uF uV`,
normalized induction inside the larger Levi has nonzero `K ∩ M_J` fixed vectors
if and only if the coefficient has nonzero `K ∩ M_{leviIndex J I}` fixed vectors.
The intersections are literal subgroup comaps.

The proof applies the ambient fixed-vector criterion first to induction from
`M_J` and then to direct induction from `M_{leviIndex J I}`. The published
induction-in-stages isomorphism identifies the resulting ambient induced
representations. Its induced linear equivalence on `K` fixed spaces preserves
nontriviality. Composing these three equivalences proves the claim. No compact
inheritance or inertial-support invariance result is assumed.

The source context is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, VI.10.6, printed
pp.213–215 / PDF pp.219–221. The implemented induction-in-stages argument is a
derived route to the fixed-vector step inside the Levi; it does not claim to
follow the source's proof line by line.
