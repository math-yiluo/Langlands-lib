# Discrete-series support and summands of tempered representations

Author: Worker 19. Worker 1058 updated the proof status for the 2026-10-29
documentation audit; the Lean file is unchanged.

This pair states discrete-series support and the equivalence between opposite
Jacquet occurrence and actual direct summands in both normalized inductions.
Its induction objects come from the published
`Langlands.Representation.Induction.OppositeParabolic` and
`Langlands.Representation.Induction.Parabolic` constructions. All declarations
are proposition definitions; this pair proves no representation-theoretic
implication. Separate published proof modules prove both components; see
[Proof status and boundaries](#proof-status-and-boundaries).

## Statements and scope

`Langlands.GLTemperedDiscreteSeriesSupportStatement` is the existence clause
of Silberger 1979, Corollary 4.5.11, printed pp.189–190. An irreducible admissible
tempered representation of positive-rank `GL_n(F)` embeds into normalized
induction from the opposite of some standard block parabolic, with an
irreducible square-integrable-mod-center representation of the actual product
Levi as inducing representation. No factorization of that representation as an
external tensor product is assumed.

The opposite-Jacquet subquotient/quotient equivalence and the product-Levi
square-integrable-to-tempered implication are stated in the separate published
[DiscreteSeriesJacquetStatement](DiscreteSeriesJacquetStatement.md).
This pair retains the support clause and the equivalence with both induced
summands. Neither pair imports the other's statements as proved facts.

The statement uses the existing analytic predicate `T.IsTempered`. For the
Levi, square integrability is `IsSquareIntegrableModCenter σ μ`: admissibility,
an actual smooth scalar unitary central character, and membership of every
smooth matrix-coefficient norm in `L²` on the central quotient. The support
clause quantifies over every Borel Haar measure. Such measures exist by the
proved helper in `TemperedInductionStatement`, so this quantification is
nonvacuous. Finite positive rescaling of Haar measure preserves this property.

The field universe and the original representation-carrier universe are
independent. The existential inducing carrier may be chosen in the original
carrier universe: class-exponent occurrence realizes an isomorphic copy on a
quotient of a subrepresentation of the actual Jacquet quotient of that carrier.
Subspaces and their quotients stay in that universe; conjugating the action
along this isomorphism preserves its irreducibility, coefficient predicates,
and the induction embedding. The induced carrier may be
larger; the actual intertwiner permits this without an artificial universe
equality. The summand clause permits an additional independent universe for
the given inducing carrier.

`Langlands.GLTemperedDiscreteSeriesSummandStatement` translates Theorem 4.5.18,
printed p.193. For irreducible tempered `π` and irreducible discrete-series `σ`
of the given Levi, it states the equivalence of:

1. `σ` being an irreducible subquotient of the opposite normalized Jacquet
   representation of `π`;
2. both normalized induced representations being completely reducible, and
   `π` being an actual direct summand of each.

The equivalence with an actual quotient of the Jacquet representation is the
separate published `GLTemperedDiscreteSeriesJacquetQuotientStatement`.

The first clause uses an invariant submodule with a surjective intertwiner to
`σ`. Thus it expresses an actual subquotient rather than an unspecified
occurrence predicate. Each summand is given by intertwiners `j` and `r` with
`r.comp j = id`; injectivity and surjectivity are consequences of this equation.
Complete reducibility is Mathlib's semisimplicity of the representation.

`GLTemperedDiscreteSeriesPrerequisitesStatement` is the conjunction of these
two proposition definitions. Neither is a proof.

## Original-source correspondence

The original is Allan J. Silberger, *Introduction to Harmonic Analysis on
Reductive p-adic Groups* (1979), registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
PDF page numbers are printed page numbers plus six.

The book defines class exponents in §3.2, printed pp.120–121. Lemma 3.2.2(2),
p.121, and Theorem 3.2.4, pp.122–123, identify class occurrence with an
irreducible subquotient of the opposite Jacquet quotient, with the displayed
half-modulus twist. Corollary 3.2.5 records the resulting equivalence with the
coefficient formulation.

On p.187, weak class exponents are the tempered members of the class-exponent
set. Lemma 4.5.6 also characterizes them by a unitary central exponent. In the
present theorem `σ` is discrete series, hence tempered, so membership in the
weak class-exponent set is precisely the subquotient condition above.

Theorem 4.5.18(2) states that `δ_opposite^(1/2) σ` occurs as a quotient of the
unnormalized opposite Jacquet module. Twisting that quotient by
`δ_opposite^(-1/2)` gives the separately published quotient criterion. Its third
clause, retained here, explicitly involves both
opposite inductions. The assumption on `σ` is discrete series, not merely
tempered.

The analytic tempered convention bridge is the one documented and reviewed
in `TemperedInductionStatement.md`, using Waldspurger's original coefficient,
Cartan and exponent estimates. The square-integrable convention is directly
the all-smooth-coefficient formulation, with scalar unitary central character,
in Silberger's §4.4 and Theorem 4.5.10, pp.188–189. Theorem 4.5.10(1)–(2)
explicitly implies that square-integrable coefficients with unitary central
character are tempered coefficients. Applying it to each coefficient on the
actual product Levi and then the Cartan lattice-sum argument gives the
analytic tempered predicate, without a tensor decomposition. This source step
was checked visually on pp.188–189 and is now documented in the separately
published `DiscreteSeriesJacquetStatement.md`. The published theorem
`Langlands.glLeviDiscreteSeriesTempered` proves its Lean statement
`GLLeviDiscreteSeriesTemperedStatement`.

The analytic inputs are J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d’après Harish-Chandra* (2003), registered as
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`:
I.1(5), p.241 (Cartan double-coset measure), Theorem I.4.1, p.245 (Jacquet
coefficient asymptotic), Lemma II.1.1, p.251 (spherical-function bound), and
§III.2 / Proposition III.2.2, pp.265–266 (weak inequality and exponent
criterion). Its one-based PDF page is the printed page minus 234. These
passages and the cited Silberger passages were read directly; the decisive
Silberger formulas on pp.121–123,187–190,193 were checked in page images.
No errata note for either source was present in the Library when this pair
was prepared.

## Normalization and specialization

The upper block modulus is `δ = T.leviModulus B`. Upper normalized induction
has covariance `δ^(1/2)σ` and right translation. Opposite induction uses
`δ^(-1/2)σ` on the actual opposite parabolic with the same Levi. The positive
half character is inverted and inflated along the actual opposite Levi
projection. This is the published function-space construction, with its
covariance and smoothness proved. Identifying the explicit determinant
modulus with the corresponding Haar modulus is a separate formal comparison;
it is not a theorem proved by this pair or its induction wrapper.

The opposite Jacquet quotient is
`Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)`. Its action is
formed using `Jacquet.normalizedActionOfModulus` with full modulus `δ⁻¹`,
first on the embedded Levi and then transported to the actual product Levi
by `B.leviEquiv`. Thus the normalization multiplier on the opposite Jacquet
quotient is the positive upper half `δ^(1/2)`. This is a genuine opposite
Jacquet construction, not a sign change on the upper quotient.

The book's reductive statements are specialized to finite extensions of
`Q_p` and standard block parabolics of positive-rank `GL_n`. Conjugacy of
parabolics to standard block parabolics supplies this specialization in the
support assertion; the fixed-parabolic summand assertion uses its specified
standard block shape and the actual opposite. No irreducibility of general
tempered induction is asserted.

## Proof status and boundaries

Both components are proved, each exactly and with no further hypotheses:

- `Langlands.glTemperedDiscreteSeriesSupport`, in
  `Langlands.Representation.Classification.TemperedSupportProof`, proves
  `GLTemperedDiscreteSeriesSupportStatement.{uF, uV}`;
- `Langlands.glTemperedDiscreteSeriesSummand`, in
  `Langlands.Representation.Classification.TemperedDiscreteSeriesSummandProof`,
  proves `GLTemperedDiscreteSeriesSummandStatement.{uF, uV, uW}`.

The conjunction `GLTemperedDiscreteSeriesPrerequisitesStatement.{uF, uV, uW}`
follows by pairing these two theorems. The Library has no separately named
theorem for it.

The more precise weakly critical-pair/exponent refinement in Corollary 4.5.11
is not encoded in this existence clause. It is stated separately as the
conjunction `GLWeaklyCriticalTemperedRefinementStatement` in
`Langlands.Representation.Exponents.WeakCriticalStatement`. Two of its three
components are proved, by `glWeaklyMinimalStandardPairExistence` and
`glWeaklyCriticalDiscreteSeriesSupport`. Its pair-minimality component
`GLWeaklyCriticalPairMinimalityStatement` has no proof in the Library, so
the refinement as a whole is unproved. This pair does not assert uniqueness
of discrete-series support. The regular Langlands quotient theorem is a
separate statement family in `RegularLanglandsStatement`.
