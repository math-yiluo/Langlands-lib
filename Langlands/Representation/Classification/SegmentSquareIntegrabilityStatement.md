# Special representations and square-integrability for GL_n

Author: Worker 47.

This module states the segment classification of essentially square-integrable
irreducible representations, uniqueness of its parameter, the square-integrability
criterion for special representations, their centered normalization, and uniqueness
of the real square-integrability exponent. Every new declaration is a `Prop`-valued
definition. No assertion in this module is proved or assumed as an axiom.

## Objects and conventions

Fix a prime `p`, an actual finite p-adic extension `F : PadicField.{uF} p`,
and its compatible topological realization `T`. Put `v = max uF uV`.
Representation carriers and the supercuspidal representatives in segments lie
in `Type v`; they need not be finite-dimensional. In particular, exhaustion
does not require a supercuspidal representation on a smaller carrier universe
than the representation being classified.

A segment `Δ : T.Segment.{v, uF}` consists of a positive cuspidal rank `r`,
a genuine supercuspidal isomorphism class `ρ` of that rank, and a positive
length `m`. Its entries are `ρ, νρ, …, ν^(m-1)ρ`, with `ν = |det|_F` and
`|ϖ|_F = q^(-1)`. Its degree is `m*r`. Segment equality compares the rank,
length and actual supercuspidal isomorphism class.

`T.segmentInduced` is the increasing product with upper block parabolic,
right translation, and covariance with the positive half modulus.
`T.IsSegmentQuotient Δ π` asserts that `π` is irreducible and is an actual
surjective intertwining image of this product for a representative of `ρ`.
`T.IsSegmentHead Δ π` strengthens this to uniqueness of the irreducible
quotient kernel. Neither relation chooses a quotient or assumes its existence.
These are the relations for the special representation `δ(Δ)` of Ze80 §9.1,
called `St_m(ρ)` in H02 §2.6. They are distinct from Ze80 §3.1's unique
irreducible subrepresentation `Z(Δ)` of the same increasing product.
Existence and strong uniqueness for each segment are separate published
statement definitions in `SegmentConstituentStatement`.

`T.IsSquareIntegrable π.representation` is the analytic predicate from
`Classification/Tempered`. For every Borel Haar measure on the actual central
quotient `GL_n(F)/Z`, it requires admissibility, a unitary scalar central
character with open kernel, and membership in `L²` of all descended absolute
matrix coefficients from vectors and smooth-dual functionals. The Library
proves that such a Haar measure exists. Quantification over all Haar measures
matches the source's fixed-measure condition by uniqueness up to positive
scalar and invariance of integrability under such scaling; that equivalence
remains a proof obligation.

`T.IsEssentiallySquareIntegrable π.representation` means that for some real
`s`, the actual twist `ν^(-s)π` is square-integrable. This is an analytic
definition, independent of segments. `UnitaryCentralCharacter` contains an
actual scalar action on every vector, and `IsUnitarizable` means existence of
an invariant positive definite Hermitian form on the carrier, without a chosen
completion.

## Exact statements

All names below are in `Langlands.Classification`.

1. `SegmentSpecialEssentialSquareIntegrability F T`: every `π` satisfying
   `T.IsSegmentQuotient Δ π` is essentially square-integrable.

2. `SegmentEssentialSquareIntegrableClassification F T`: for every `n > 0`
   and irreducible smooth complex representation `π` of `GL_n(F)`,
   essential square-integrability holds if and only if there exist a segment
   `Δ` and `h : Δ.degree = n` such that
   `T.IsSegmentHead Δ (h.symm ▸ π)`. The transport changes the group index
   along the displayed equality; it does not replace the representation.

3. `SegmentSpecialParameterUniqueness F T`: if `π` and `π'` are heads for
   `Δ` and `Δ'`, `h : Δ.degree = Δ'.degree`, and there is an actual category
   isomorphism `(h ▸ π) ≅ π'`, then `Δ = Δ'`. Thus the uniqueness concerns
   the full segment parameter on genuine isomorphism classes.

4. `SegmentSpecialSquareIntegrabilityCriterion F T`: for each irreducible
   segment quotient `π`, both equivalences hold:

       T.IsSquareIntegrable π.representation
         ↔ Nonempty (UnitaryCentralCharacter π.representation)

       T.IsSquareIntegrable π.representation
         ↔ IsUnitarizable π.representation.

   The restriction to a special quotient is essential. The statement does
   not give either converse for an arbitrary irreducible representation.

5. `SegmentCenteredSpecialSquareIntegrability F T`: given a supercuspidal
   representative `A` of `Δ.base` with an invariant positive Hermitian form,
   every irreducible quotient `π` of the increasing segment product satisfies
   square-integrability and unitarizability after twisting by
   `ν^(-(m-1)/2)`. In Lean the exponent is
   `-(((Δ.length : ℝ) - 1) / 2)`, with real division. The segment constructor
   remains uncentered.

6. `EssentialSquareIntegrabilityExponentUniqueness F T`: for `n > 0`,
   an irreducible essentially square-integrable `π` has exactly one real `s`
   such that `ν^(-s)π` is square-integrable. This asserts uniqueness of the
   exponent, without selecting a normalized representation.

`SegmentSquareIntegrabilityTheorems F T` conjoins these six propositions.
`PadicSegmentSquareIntegrabilityTheorems` quantifies them over all primes,
all finite p-adic extensions and all compatible `T`, at the displayed
universes. Rank zero is excluded explicitly in the two rank-indexed clauses
and intrinsically by segment positivity in the other four.

## Source correspondence and derived content

| Lean clause | Source and translation |
| --- | --- |
| `SegmentSpecialEssentialSquareIntegrability` | Ze80 §9.3, printed p.198 (PDF p.35), construction direction, using the special quotient convention of §9.1, p.197 (PDF p.34). H02 §2.6, p.595 (PDF p.9), states the same for the unique quotient of the increasing product. |
| `SegmentEssentialSquareIntegrableClassification` | Bernstein's theorem in Ze80 §9.3, p.198; Au04 Theorem 6.1, p.18, supplies a later written proof route. Strong head uniqueness is the separate segment-constituent assertion in Ze80 §9.1. |
| `SegmentSpecialParameterUniqueness` | H02 §2.6, p.595, explicitly states a bijection from pairs `(ρ,m)`, with `m > 0`, to essentially square-integrable isomorphism classes. |
| `SegmentSpecialSquareIntegrabilityCriterion` | Derived from the construction direction, the unitary central-character normalization in Au04 Definitions 4.7 and 4.14–4.16, pp.9–10, and the invariant-form result Ca95 Proposition 2.5.4, p.29. Au04 Proposition 4.17 and Remark 4.18, p.10, record the corresponding unitarity conclusion. |
| `SegmentCenteredSpecialSquareIntegrability` | Derived from the preceding criterion and the scalar-character computation for the increasing product; Au04 Proposition 5.5, p.15, and Theorem 5.13(g), p.18, give the centered central-character description and its preservation by the duality operation. Ze80 §9.2, p.198, checks the Steinberg normalization. |
| `EssentialSquareIntegrabilityExponentUniqueness` | Derived from the analytic definition, unitary scalar central characters (Ca95 §2.5, p.28; Au04 Definitions 4.7 and 4.14, pp.9–10), and the nontrivial residue-normalized absolute value on scalar matrices. |

Ze80 allows a suitable character in the definition of quasi-square-integrability.
For `GL_n(F)` a smooth character factors through the determinant, and its
absolute value is a real power of the residue-normalized absolute value of
`F`. Removing its unitary part does not change absolute matrix coefficients
or square-integrability. This explains the real-exponent formulation; the
character decomposition and preservation by unitary twists remain proof
obligations. Au04 Lemma 4.15, p.10, gives the central-character normalization.
Au04's matrix coefficient uses `g⁻¹`; the Library and Ca95 use `g`.
Inversion preserves Haar measure on the unimodular central quotient here,
so the integrability conditions agree. That comparison is not proved here.

For the first equivalence in clause 4, write a special quotient as `ν^s π₀`
with `π₀` square-integrable. If `π` also has a unitary scalar central
character, comparing central actions on a nonzero vector at `ϖ I_n` gives
`|ϖ|^(ns) = 1`. Since `n > 0` and `0 < |ϖ| < 1`, this forces `s = 0`.
The forward implication is part of the square-integrability predicate.
For the second equivalence, square-integrability supplies an invariant
positive form by Ca95 Proposition 2.5.4; conversely such a form forces any
scalar central action to have norm one. Essential square-integrability
already supplies the scalar action after undoing the real twist.
This argument applies only under the stated special-quotient hypothesis.

For clause 5, if `A` has unitary central character `ω`, the scalar action
on the increasing induction, and hence on its quotient, is

    ω(z)^m |z|^(r*m*(m-1)/2).

The modulus is trivial on scalar matrices. The twist by `-(m-1)/2`
on `GL_(mr)` cancels the absolute-value factor. This yields clause 5 from
clause 4. The general segment scalar-character computation is separately
stated in `SegmentConstituentCompatibilityStatement`.

For clause 6, existence is already in the definition of essential
square-integrability. If both `ν^(-s)π` and `ν^(-t)π` are square-integrable,
their unitary central characters, evaluated on the same nonzero vector,
give `|ϖ|^(n*(s-t)) = 1`; hence `s = t`. Positive rank is necessary:
the determinant character is trivial at rank zero. These arguments explain
the derived statements; the module does not implement their proofs.

## The omitted converse and remaining proof obligations

Ze80 §9.3 explicitly omits the converse's proof. Its forward direction
invokes Casselman's criterion with the normalized Jacquet computation in
§9.1, including the half-modulus conversion. Au04 §§5.3–6, pp.17–22, give
a written converse using the involution `D`: after centering, a dual
Casselman criterion and the multisegment classification force a single
segment. Au04 Theorem 5.13 invokes Aubert 1995 (with the 1996 erratum) and
Schneider–Stuhler 1997 for the required duality properties. Those originals
have not been read in this branch. Their proof inputs, Casselman's criterion,
and the classification and Jacquet results are separate obligations.
Ze80 §9.17 is a conjecture in that original and is not a proof of these inputs.

The following corrections to Au04 are retained when citing that route:
Theorem 5.12, p.17, should use products of segment classes as an additive
basis, or equivalently the polynomial generators of Ze80 Corollary 7.5;
the reference preceding Theorem 6.1 is to Ze80 §9.3; the exponent vector
in Example 6.13 includes the common cuspidal-rank factor; the criterion's
excluded central/compact set is determined by Definitions 6.6 and 6.11
and Theorem 6.8; the concluding contradiction on p.22 concerns `Dπ`.
None of these misprints is copied into the Lean propositions.

The paired analytic definitions also leave Haar-measure independence and
the character decomposition as proof obligations. Source admissibility of
irreducible smooth `GL_n(F)` representations is used in translating the
classification, and is not added as an extra hypothesis to clause 2.
No general reductive tempered-induction assertion occurs in this file.

## Published dependency versions and exact sources

The declarations were checked against Library commit
`a175d25f6a5a9e22525012e3cae66e9f8dfacba9`. Direct imports are
`Langlands.Representation.Classification.Segments` (actual segments,
induction and constituent relations) and
`Langlands.Representation.Classification.Tempered` (analytic predicates and
real twists). They reuse the published `Classification.ConstituentRelations`,
`Classification.SupercuspidalTwist`, `Induction.BlockFactors`,
`MatrixCoefficient.ModuloCenter`, `Smooth.Contragredient.Definitions` and
`Unitary.Basic`. The related constituent and compatibility statements named
above are mathematical proof dependencies, not assumed theorem arguments.

The retained source files, registered in the literature index, have these
SHA-256 fingerprints:

- Ze80, `zelevinsky-1980-induced-ii`:
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- H02, `henniart-2002-characterization`:
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- Au04, `provided-dd2424348af1ddf73426a58cb44a42985d610bade9fb26dd0da2739fbc2494d1`:
  `3a6bcabbd0fa06a16e530cd3e7381c42742e3f1e4545316e2bf047e62afb1e65`.
- Ca95, `casselman-1995-admissible-representations`, draft of 1 May 1995:
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.

Au04 and Ca95 page numbers above are also their one-based PDF pages.
