# Ordered tempered Langlands-data uniqueness for GL_n

Worker 594 closes the theorem using the published parameter comparison and the
fixed-parameter tensor recovery proof. The final algebraic assembly follows the
carried conditional draft of the previous-instance Worker 47; that contribution
is retained explicitly here.

`Langlands.glRegularLanglandsDataUniqueness.{uF,uV}` has exactly the closed type
`Langlands.GLRegularLanglandsDataUniquenessStatement.{uF,uV}`. It quantifies over
every prime, every supplied p-adic field and topology, and every positive rank.
The field and representation parameters remain independent, with the prescribed
`max uF uV` carriers. The hypotheses remain the two arbitrary weak irreducible
quotient witnesses and an actual smooth isomorphism of their outputs.

Apply `glRegularLanglandsParameterUniqueness` to obtain an order isomorphism of
the block indices matching every rank and real exponent. The published algebraic
lemma `GeneralLinear.BlockShape.eq_of_orderIso` identifies the two complete
ordered shapes. Destructuring the two data records and eliminating this equality
puts their factors on exactly the same indexed block groups. The order
automorphism of their common finite chain is the identity; the matched exponent
values therefore identify the two exponent functions. Proof irrelevance handles
their strict-antitonicity witnesses.

`glRegularLanglandsTensorRecovery` now recovers an actual equivalence of the two
untwisted external tensor representations at this fixed shape and exponent. The
published `T.blockIsoOfTensorEquiv` turns that tensor equivalence into actual
smooth isomorphisms of all irreducible block factors. The final witnesses are
the identity order isomorphism and reflexive rank equalities in the transported
context. Eliminating the earlier equalities gives precisely the target's rank
transport and ordered factor-isomorphism conclusions for the original data.

Both comparison inputs are closed proved theorems. In particular, fixed-parameter
tensor recovery is proved through actual leading-real-block isolation and
second adjointness, as explained in
[its proof](RegularLanglandsTensorRecoveryProof.md). The argument uses the given
weak quotients throughout and introduces no head-existence premise. The
analytic block-to-product temperedness and scalar Schur inputs are proved in
that tensor theorem. The parameter theorem separately proves its analytic
support, cone and numerical comparisons; this module supplies the final
algebraic composition.

The mathematical source is A. J. Silberger, *The Langlands quotient theorem for
p-adic groups*, Math. Ann. 236 (1978), 95–104, Theorem 4.1(2), printed p.99,
and Proposition 6.1, printed pp.102–103. Registered source
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The proof of Proposition 6.1 was read directly, including both page images.
The explicit ordered GL block conclusion is Kudla, *The local Langlands
correspondence: the non-archimedean case* (1994), section 2.2, Theorem 2.2.2(b),
printed p.374, with the analytic convention and grouping discussion on
pp.372–373. Registered source `kudla-1994-local-langlands-nonarchimedean`,
SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
These three pages were read; pp.373–374 were checked as images. The implemented
assembly composes the Library's proved comparisons; the tensor recovery route
differs from Silberger's last step through Propositions 5.8 and 5.7.

The current Library contains no source-specific errata file for either source.
The published [Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md)
was read; this proof uses the supported published comparison theorems and the
actual leading-real-block construction. Strict descent is retained exactly,
all real central shifts are allowed, and the one-block case is covered. Equal
exponent grouping belongs to the separate square-integrable-to-tempered
classification and is not needed for data already satisfying `StrictAnti`.
