# Simple connectedness and trivial Picard group for split semisimple groups

`Langlands.GroupScheme.splitSemisimpleSimplyConnectedPicard` proves
`SplitSemisimpleSimplyConnectedPicardStatement.{u}` in every universe `u`.
For any field `k : Type u` and semisimple group scheme `G` over `Spec k`
with a split maximal torus, `G` is simply connected if and only if every
line bundle on its underlying scheme is isomorphic to the trivial line
bundle. This is the semisimple specialization of Milne, *Algebraic Groups*
(2017), Proposition 18.19 and Corollary 18.24, printed pp. 391–393
(PDF pp. 407–409). [Statement and source comparison](SplitPicardTrivialStatement.md)

The proof applies `splitSemisimplePicardReduction` to the published
theorems `splitCentralIsogenyPicardCharacterLifting` and
`splitSemisimplePicardTrivialCover`. The reduction establishes
`SplitSemisimplePicardReductionStatement.{u}`, the implication from the
conjunction of those two geometric inputs to the criterion.
[Reduction statement](SplitPicardReductionStatement.md)
[Character lifting](SplitPicardCharacterLifting.md)
[Picard-trivial cover](SplitPicardTrivialCoverProof.md)

For a simply connected semisimple group, the cover input gives a central
isogeny from a semisimple group on which every line bundle is trivial.
Simple connectedness makes that isogeny invertible. The proof applies
`SplitPicardCharacterLifting.lineBundlesTrivial_of_isIso` to the underlying
scheme isomorphism. That lemma pulls a line bundle back to the cover and
reflects its trivialization along the isomorphism using
`LineBundle.isoOfPullbackIso`.

Conversely, consider any central isogeny from a semisimple group to a split
semisimple group with trivial Picard group. The published
`centralIsogenySplitMaximalTorusLift` supplies a split maximal torus of the
source. The character-lifting input makes restriction onto the full
scheme-theoretic kernel's rational characters surjective. Rational characters
of a semisimple group vanish by the published
`IsSemisimple.subsingleton_rationalCharacters`. Thus every character of the
kernel vanishes.

`IsCentralIsogeny.isIso_of_kernel_characters_eq_zero` turns this vanishing
into invertibility of the isogeny. Centrality places the kernel's range
functor in the centralizer of a split maximal torus of the source, and
`maximalTorusCentralizer` identifies this centralizer with that torus.
The represented-subgroup factorization constructs a homomorphism from the
full kernel into the split torus. The published
`IsSplitTorus.hom_eq_zero_of_characters_eq_zero` makes that homomorphism zero,
so the original kernel inclusion is zero. On every test scheme, a point
killed by the isogeny lifts to the kernel and is therefore the identity.
Applying this to the quotient of two points proves that the isogeny is a
monomorphism. The finite underlying scheme map is quasi-compact, so the
flat surjective monomorphism is an isomorphism. The forgetful functors
reflect that isomorphism to group schemes.

The reduction and kernel lemma are derived from the Library results above.
The published cover proof obtains Picard triviality from factoriality of
the split simply connected cover. The character argument works with the
full scheme-theoretic kernel, including nonreduced kernels in positive
characteristic.
