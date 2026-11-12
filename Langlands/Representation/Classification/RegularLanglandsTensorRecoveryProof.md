# Recovery of the untwisted tensor at a fixed regular Langlands parameter

Worker 594 authored the proof. Worker 859 checked the source conventions,
the proof assembly and its import dependencies, and prepared the contribution.
The imported results retain their documented authorship.

`Langlands.glRegularLanglandsTensorRecovery.{uF,uV}` proves exactly
`Langlands.GLRegularLanglandsTensorRecoveryStatement.{uF,uV}`. It retains
arbitrary irreducible quotient witnesses, all positive ranks, every supplied
p-adic field and topology, independent field and carrier parameters, and the
saturated carrier universe `max uF uV`. No distinguished head or additional
support condition is required.

## Implemented proof

The helper `fixedRegularLeviRecovery` works with arbitrary irreducible
analytically tempered representations `sigma` and `tau` of one actual product
Levi, independent carrier universes, a strictly decreasing real determinant
parameter `t`, and surjections from both twisted upper inductions onto one
irreducible ambient representation `J`.

Write `alpha = sigma(t)`, `beta = tau(t)`, and let `N` be the actual normalized
opposite Jacquet module of `J`. The published theorem
`Exponents.wholeInductionLeadingRealBlock` gives an embedding `i` of `alpha`
into the opposite Jacquet module of its full induction and a retraction `r`.
Their composite projector fixes every generalized full-central-character
space whose open-kernel character has block-scalar real part
`x(k) = B.size k * t(k)`.

`RelativeCosocleHomIsolationReduction.temperedInductionFiniteGeneration`
proves finite generation of this full induction. The published
`ActualQuotientRealBlock.quotientRetractionOfFiniteGeneration` applies to the
first given quotient map `q`. It constructs an intertwiner `rQ : N -> alpha`
whose projector satisfies

```
Jacquet(q)(i(rQ(v))) = v
```

for every vector in `T.realCentralBlock B N x`. This is a proved actual
quotient construction: finite central actions and second adjointness are
discharged by the imported theorem. The quotient is the given `J` throughout.

For the competing quotient map, actual second adjointness supplies a nonzero
intertwiner `g : beta -> N` by
`ActualQuotientRealBlock.nonzeroAdjunctionMap`. Admissibility of `beta` and
`J` follows from `relativeCosocleAdmissibility`; irreducibility of `J` excludes
the zero carrier. The analytic unitary central character of `tau` proves
`TemperedCoarseRealBlock.realBlockEqTop`, so every vector of `beta` belongs
to its real block `x`. Intertwiners preserve the grouped generalized character
spaces, hence every `g(v)` lies in the same real block of `N`.

Consequently `rQ` composed with `g` is nonzero: if it vanished, the displayed
projector identity would force every `g(v)` to vanish. Both twists are
irreducible by the published twist criterion. Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero` therefore makes this
nonzero intertwiner an actual representation equivalence. Cancelling the
common character with `untwistIntertwining` and taking the inverse gives
`sigma.Equiv tau`. No variation of parameters, relative recovery premise,
classification statement, or semisimplicity of the full Jacquet module is
used in this helper.

The import closure includes proposition definitions for regular data uniqueness
and relative recovery through existing interface modules. No theorem proving
either proposition is imported, and neither proposition is assumed in this
proof. The tensor recovery statement and all its imported Lean/Markdown pairs
are unchanged.

For the exact tensor target, form the two untwisted external tensors of the
supplied block families. Admissibility of each analytically tempered block,
the admissible scalar Schur theorem, and
`FiniteTensor.isIrreducible_external` prove irreducibility of each tensor.
`glBlockTensorTempered` proves whole-Levi analytic temperedness for every
Borel Haar realization. `RegularHeadExistence.standardModuleLeviTwistEquiv`
identifies each actual block standard module with induction of the common
real twist of that untwisted tensor. Composing the two given quotient maps
with these equivalences and with the inverse of the supplied output
isomorphism produces two surjections onto the first supplied quotient.
Apply `fixedRegularLeviRecovery` to obtain the required untwisted tensor
equivalence.

## Sources and provenance

The mathematical conclusion is the fixed-parabolic, fixed-parameter part of
A. J. Silberger, *The Langlands quotient theorem for p-adic groups*, Math.
Ann. 236 (1978), 95–104, Proposition 6.1, printed pp.102–103. Registered
source `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
These pages were read directly and checked as images. Silberger's final step
uses Propositions 5.8 and 5.7. The implemented proof instead uses the stronger
published leading-real-block projector and actual quotient extraction, as
described above; this is an internal derived proof route rather than a
transcription of those two propositions.

The explicit ordered GL block conclusion and analytic convention are also
recorded by S. S. Kudla, *The local Langlands correspondence: the
non-archimedean case* (1994), section 2.2, printed pp.372–374, especially
Theorem 2.2.2(b). Registered source
`kudla-1994-local-langlands-nonarchimedean`, SHA256
`0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
These pages were read directly; pp.373–374 were checked as images. The
current Library has no source-specific errata file for either source. The
published [Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md)
was read; its unsupported unrestricted multiplicity assertion is not invoked.

All analytic comparison, actual geometric filtration, character exclusion,
finite-generation and quotient-lifting results used here are imported
published theorems, with their own proof and source explanations. The upper
induction uses right translation and positive-half-modulus covariance;
the opposite normalized Jacquet module uses the positive half of the upper
modulus. The absolute value remains residue normalized. Real central twists
are unrestricted, and the one-block case is retained because strict descent
on a singleton is vacuous.
