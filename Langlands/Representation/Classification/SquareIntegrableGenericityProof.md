# Intrinsic Whittaker genericity of a square-integrable representation

Authors: Worker 386 and Worker 1722.

`Langlands.Classification.squareIntegrableGenericity` proves exactly the
published proposition
`Langlands.Classification.SquareIntegrableGenericity.{uF,uV} F T`.
The only outer parameters are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. There are no additional
hypotheses.

## Exact scope

After installing `T.topology`, the theorem takes every `n : ℕ` and every
actual
`π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier)`.
Its hypotheses are algebraic irreducibility, the existing analytic
`T.IsSquareIntegrable π.representation`, and the existing
`IsUnitarizable π.representation`. For every continuous nontrivial unitary
additive character `ψ`, it proves `Whittaker.IsGeneric ψ n π.representation`.
Field and carrier universes remain independent. The argument includes
`n = 0`, hence `GL₁`, without a rank exception.

The analytic hypothesis is unchanged: for every Borel Haar measure on the
actual quotient by the full center, the smooth-dual coefficient norms
descend to square-integrable functions. It is not replaced by a
classification-image predicate, an ordinary `L²(GL)` condition, or a
central-character assumption. The invariant positive Hermitian form in the
unitarizability hypothesis remains part of the exact target; this route
proves the conclusion from irreducibility and analytic square-integrability
alone, so it does not need to choose that form.

The conclusion uses the actual standard upper-unipotent subgroup and the
positive superdiagonal character. It includes irreducibility, admissibility
and an actual nonzero algebraic complex-linear functional. No topology or
finite-dimensionality is imposed on the representation carrier.

## Implemented proof

First apply
`PadicField.TopologicalData.IsSquareIntegrable.isEssentiallySquareIntegrable`.
This chooses real exponent zero in the analytic essential
square-integrability predicate and uses `realPowerTwist_zero`.
Apply the proved theorem
`Classification.segmentEssentialSquareIntegrableClassification` in rank
`n + 1`, which is positive for every `n`. It supplies an actual segment `Δ`,
an equality `hΔ : Δ.degree = n + 1`, and

```text
T.IsSegmentHead Δ (hΔ.symm ▸ π).
```

This is the strong head relation for the original representation at the
equal rank. It includes an actual irreducible quotient and kernel
uniqueness; no representative or abstract isomorphism class is substituted.

Define a `SegmentProductDatum` with one segment `Δ` and the one actual block
`hΔ.symm ▸ π`. Its degree sum is `hΔ`. The supplied strong head proves
`HasSegmentHeads`. Its multisegment is the singleton containing `Δ`.
Any two members therefore equal `Δ`; `Segment.not_isLinked_self` proves
that this multisegment is unlinked.

`SegmentProductOrderedAssembly.singletonIso` supplies the actual
isomorphism from the singleton normalized induced representation to its
block at the ambient rank. It uses the existing single-block normalized
induction equivalence, including the actual action and covariance, and
then the rank-transport equivalence. The private helper `rankCastCancelIso`
removes the remaining numerical equality transport: for arbitrary
`h : a = b`, transport of `h.symm ▸ π` along `generalLinearRankCast T h`
is isomorphic to `π`. Its proof eliminates `h` and uses the identity
isomorphism. Composing these gives `d.induced ≅ π`, and taking its inverse
gives exactly the isomorphism required by generic-product exhaustion.

Finally use the reverse implication of the proved theorem
`Classification.genericSegmentProductExhaustion` for the given `ψ`, `n`
and `π`, supplying this same datum, its strong heads, nonlinkage and the
actual isomorphism. No genericity premise is assumed. That published
implication proves irreducibility and admissibility of the product,
obtains a nonzero top derivative, identifies its dual with the actual
Whittaker functional space, and transports genericity along the supplied
representation equivalence. These are the implemented special-constituent
genericity and functional-passage inputs of this route.

## Provenance and independence

This proof is an internal assembly of published Library theorems. Worker
1722 identified and supplied the singleton classification route; Worker
386 checked the inputs and implemented the final assembly.

The classification input is the proved analytic theorem from
`SegmentEssentialSquareIntegrableClassificationProof`; its converse is
implemented using integral cuspidal Jacquet words, minimal consecutive
runs, actual segment factors and the strict analytic scalar cone. The
genericity input is the proved theorem from
`GenericSegmentProductExhaustionProof`. Only its reverse implication is
used here. Their paired Markdown explains their respective proofs and
upstream dependencies.

This route corresponds to Zelevinsky's special-quotient conventions in
§9.1, printed p.197, the essentially square-integrable classification in
§9.3, printed p.198, and special-head genericity in Theorem 9.7(a), printed
p.199. Zelevinsky explicitly omits the classification converse proof;
the present proof relies on the actual published Lean proof rather than
treating that source assertion as a proof.

The target's direct Jacquet–Shalika source uses a unitary mirabolic route.
That is a different proof route. The present module does not establish
the separate unitary restriction, Fourier/Mackey or mirabolic comparison
statements. Kudla's §2.3, printed p.374, gives the same positive-character
functional convention and the single-segment genericity example.
Neither its broader tempered-genericity assertion nor the dependent
`SquareIntegrableBlockGenericity` and `TemperedUnitarityAndGenericity`
propositions supplies an input to this proof. The convention and source
boundaries in
[the classification source note](../../../notes/henniart/gln-classification-sources.md)
are preserved.

## Retained originals

The registered originals were read directly; the relevant formulas in
Zelevinsky pp.197–199, Jacquet–Shalika pp.108–109 and Kudla p.374 were
also checked visually. Their file hashes were rechecked for this assembly.
No source-specific `notes/errata` file for these sources was present in the
supplied Library snapshot.

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  pp.165–210. Source ID `zelevinsky-1980-induced-ii`, §§9.1, 9.3 and
  Theorem 9.7(a), printed pp.197–199 (one-based PDF pp.34–36).
  SHA256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- H. Jacquet and J. A. Shalika, *The Whittaker models of induced
  representations*, Pacific J. Math. 109 (1983), pp.107–120.
  Source ID `jacquet-shalika-1983-whittaker`, §1.2, printed pp.108–109
  (one-based PDF pp.3–4).
  SHA256 `e171831da6c064fdcb55efe79381ba1f85daa4efd7f3a79071589ffee9527f98`.
- S. S. Kudla, *The local Langlands correspondence: the non-archimedean
  case*, Motives, Part 2, Proc. Sympos. Pure Math. 55 (1994), pp.365–391.
  Source ID `kudla-1994-local-langlands-nonarchimedean`, §2.3, equation
  (2.3.1) and the single-segment example, printed p.374 (one-based PDF
  p.384 of the retained volume).
  SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
