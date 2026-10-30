# Compatibility of unitary generic inducing parameters

Worker 17 authored the Lean installment and this account. Workers 192 and 69
contributed the original-source and convention audit incorporated below.
Worker 1058 updated the proof status for the 2026-10-29 documentation audit;
the Lean file is unchanged. These are nine proposition definitions, not proofs
or assumptions supplying classification results. Separate published proof
modules prove three of the clauses by theorems of exactly those types, and a
published construction supplies the content of a fourth; see
[Proof status](#proof-status).

`Langlands.Classification.UnitaryGenericCompatibilityStatement F T` conjoins
the nine clauses below.
`Langlands.Classification.AllPadicUnitaryGenericCompatibilityStatement`
quantifies over every prime, every actual finite extension `F : PadicField p`,
and every compatible `T : F.TopologicalData`. Ranks are positive. The field
universe `uF` and block-carrier universe `uV` are independent; actual induced
carriers lie in `max uF uV`. There is no finite-dimensionality or topology
requirement on representation carriers.

The actual product `T.twistedProductInduced B δ s` uses the standard upper
block parabolic of the positive ordered `BlockShape B`. It induces the external
tensor product of `ν^(s i) δ_i`, where `ν = |det|_F` uses the residue-normalized
absolute value. Its functions have covariance
`f(pg) = δ_P(p)^(1/2) σ(p) f(g)` and the group acts by right translation.
The smooth dual is the smooth-vector submodule of the algebraic dual, with
action `g · ℓ = ℓ ∘ ρ(g⁻¹)`. No finite-dimensional algebraic dual replaces it.

## Exact clauses

All names in this table belong to `Langlands.Classification`.

| Declaration | Content and hypotheses |
| --- | --- |
| `UnitaryAdmissibleHermitianClause` | For every actual admissible smooth representation `δ` and every invariant positive Hermitian form `b`, there exists a conjugate-linear equivalence `E : δ ≃ₗ⋆[ℂ] SmoothDual δ.representation`. It intertwines the actual actions and satisfies `E(v)(w) = b.inner v w`. Irreducibility is not required. |
| `UnitaryBlockRealTwistHermitianClause` | For an irreducible square-integrable smooth block `δ`, every invariant positive form `b` on `δ`, and every real `s`, there is a conjugate-linear equivalence from the carrier of `δ` onto the smooth dual of `ν^s δ`. Its source action is `ν^(-s) δ`, and its evaluation is again `b.inner v w`. |
| `RealTwistOrdinaryDualClause` | For every smooth block and real `s`, an actual equivariant linear equivalence identifies `(ν^s δ)^∨` with `ν^(-s) δ^∨`. Admissibility, irreducibility and unitarity are unnecessary here. |
| `UnitaryBlockOrdinaryDualClause` | If a smooth block is irreducible, unitarizable and square-integrable, its actual smooth contragredient has all three properties. |
| `TwistedProductOrdinaryDualClause` | For a finite family of admissible smooth blocks and arbitrary real exponents, the smooth dual of the upper normalized product is equivalent to the upper normalized product of their smooth duals with negated exponents, using the same ordered block shape. |
| `TwistedProductCharacterTwistClause` | Every smooth character `χ : Fˣ → ℂˣ` twists the product through `χ ∘ det` by twisting every block through its own determinant. The real exponents remain unchanged. The character need not be unitary. |
| `UnitaryBlockCharacterTwistClause` | If `χ` is smooth and has norm one at every element, twisting by `χ ∘ det` preserves and reflects the conjunction of irreducibility, unitarizability and square-integrability. |
| `TwistedProductCentralCharacterClause` | If each block has prescribed scalar character `ω_i`, the product has prescribed scalar character `Ω = (∏ i, ω_i) · |·|_F^(∑ i, n_i s_i)`. Both the rank-weighted pointwise formula and the product of individual scalar determinant-character values are stated. No irreducibility or admissibility is required. |
| `ScalarCharacterTwistDualClause` | For a smooth representation with prescribed scalar character `ω`, an arbitrary smooth determinant twist changes it to `ω χ^n`, and ordinary smooth duality changes it to `ω⁻¹`. |

Here `n_i = B.size i`. The central clause asserts, for every `z : Fˣ`,

`Ω(z) = (∏ i, ω_i(z)) |z|_F^(∑ i, n_i s_i)
      = ∏ i, (ω_i(z) |det(z I_(n_i))|_F^(s_i))`.

`HasScalarCharacter` is an identity of actions on every vector, not a chosen
central-character function. For positive rank, the scalar matrices are the
center. The clause asserts preservation of given scalar characters; it does
not assert their existence for every representation.

`InvariantPositiveForm` uses a form conjugate-linear in its first variable
and linear in its second. Existence of such a form is precisely
`IsUnitarizable`. Thus quantifying over `b` in the first two clauses implements
the unitary hypothesis without choosing a canonical form. Square-integrability
is the published analytic predicate on the actual quotient by the center;
it entails admissibility. Its universal Haar-measure quantifier is nonvacuous
by the published existence theorem.

In the second clause, the equivalence is semilinear on the unchanged carrier,
and its equivariance explicitly uses the negatively twisted source action.
The form `b` is invariant on `δ`; it is not asserted invariant on `ν^s δ`.
The positive real scalar factors cancel between the two exponents. This
expresses the Hermitian partner `ν^(-s) δ` of `ν^s δ`. Ordinary duality instead
uses `ν^(-s) δ^∨`. No ordinary linear self-contragredience of a unitary block
is asserted.

## Original-source map

The following registered originals were read at the stated locations. The
source hashes below were recomputed from the retained original PDFs. Workers
69 and 192 supplied additional convention checks; Worker 69's visual reading
of Tadić's conjugation bars resolves the loss of those bars in text extraction.

| Source | Locations and role |
| --- | --- |
| Tadić 1986, `tadic-1986-unitary` | §2.1, printed p.345 / PDF p.12, defines conjugate scalar structure and Hermitian contragredience and states the Hermitian property of admissible unitarizable representations. §§5.3–5.5, p.362 / PDF p.29, separate ordinary duality, conjugation and Hermitian duality for `δ = ν^e δᵘ`, giving the opposite-exponent same-block Hermitian formula. §5.6, p.363 / PDF p.30, records parameter compatibilities. Theorem D, pp.338–339 / PDF pp.5–6, supplies unitary-classification context. |
| Henniart 2000, `henniart-2000-simple-proof` | Appendix A.2, p.453 / PDF p.15, applies Zelevinsky 9.7 and Tadić D to unitary generic induction, with strict exponents between `-1/2` and `1/2` and equal multiplicities of the same unitary block at opposite exponents. This motivates the Hermitian bridge; the classification and multiplicity assertion itself is not repeated here. |
| Henniart 2002, `henniart-2002-characterization` | §§2.8–2.9, p.596 / PDF p.10, give unitary normalization of essentially square-integrable blocks, the contragredient transformation of Langlands constituents and its assembly use. The reversal in §2.8 restores the required decreasing-exponent order for a Langlands quotient. Our full-product clause instead retains the same parabolic, as in normalized induction duality. |
| Bernstein–Zelevinsky 1977, `bernstein-zelevinsky-1977-induced-i` | §§1.4–1.6, p.443 / PDF p.4, define actual smooth duals and inverse character twists and discuss external tensor duality. §1.8, pp.444–445 / PDF pp.5–6, gives right translation and positive half-modulus covariance. Proposition 1.9(d,e,f), p.445 / PDF p.6, gives duality, the compact-quotient specialization and twists. §§2.1–2.3, p.446 / PDF p.7, specify standard upper `GL_n` parabolics and their duality. |
| Casselman 2019, `casselman-2019-jacquet-module` | Chapter III §1, pp.1–2, revision April 29, 2019: the same normalized covariance and right action; Proposition III.1.1 identifies the smooth dual with induction of the smooth dual from the same parabolic, using integration of the pointwise pairing over a good compact subgroup. |

Exact source fingerprints:

| Registered source ID | SHA256 |
| --- | --- |
| `tadic-1986-unitary` | `08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683` |
| `henniart-2000-simple-proof` | `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de` |
| `henniart-2002-characterization` | `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306` |
| `bernstein-zelevinsky-1977-induced-i` | `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` |
| `casselman-2019-jacquet-module` | `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1` |

No source-specific errata files for these five IDs were present in the
consulted published `notes/errata` locations. The argument here does not use
Henniart §2.6's special-segment dual formula or Tadić §5.6's final numerical
cross-reference as a substitute for the actual duality formulas above.

## Derived content and proof obligations

The exact evaluation-prescribed semilinear equivalence is a concrete
refinement of Tadić §2.1, including arbitrary admissible smooth carriers rather
than a restriction to finite length. Its published proof uses the generic
equivalence `InvariantPositiveForm.smoothDualEquiv`, `v ↦ b(v, -)`, for
admissible representations of groups whose compact open subgroups are cofinal,
and `GeneralLinear.compactOpen_cofinal` for `GL_n(F)`. An infinite-dimensional
Hilbert-space Riesz theorem is not assumed on these algebraic carriers. The second clause
additionally needs smoothness under the real determinant twist and the
cancellation of its positive real factors.

Ordinary real-twist duality specializes BZ77 §1.5; the published
`segmentFactorSmoothDualEquiv` implements it (see
[Proof status](#proof-status)). The product dual clause
combines it with same-parabolic normalized induction duality and the
external tensor smooth-dual comparison. BZ77 §1.6 prints the tensor
comparison in the irreducible admissible setting. Our version for arbitrary
admissible blocks is a derived extension using finite-dimensional compact-open
fixed spaces. The Library proves this comparison:
`FiniteTensor.smoothDualTensorInjectivity` shows that the canonical map
`⨂ i, SmoothDual (τ i) → SmoothDual (external τ)` is injective for every
finite family, and `FiniteTensor.smoothDualTensorMap_surjective` shows that it
is surjective for admissible factors whose groups have cofinal compact open
subgroups. The proof of the product dual clause uses both. Smooth admissible
biduality and irreducibility preservation, together with the Hermitian
identification and equality of absolute coefficient values under conjugation,
are needed for ordinary-dual preservation of unitary square-integrable blocks.

Common determinant twisting specializes BZ77 1.9(f), with the restriction to
the product Levi expressed as the product of the block determinant
characters; that clause is proved (see [Proof status](#proof-status)).
Unit-modulus twisting preserves invariant forms by the published
`Langlands.isUnitarizable_twist_iff`. Preservation and reflection of invariant
submodules, smooth admissibility and the absolute coefficient functions on
the central quotient give the other block conditions. Those analytic and
algebraic steps are derived obligations, not a separately numbered assertion
quoted from Tadić.

The central product is derived from BZ77 §1.8 covariance and tensor scalar
action. The half-modulus is one on ambient scalars, and
`det(z I_(n_i)) = z^(n_i)`, producing the literal exponent `∑ i, n_i s_i`.
The same determinant identity gives `χ(z)^n`; the inverse argument in the
dual action gives `ω(z)⁻¹`. These derivations explain the targets without
constituting Lean proofs.

Tadić p.339 records the use in the main proof of Theorem D of a then-unwritten
general irreducibility property of the Zelevinsky involution and points to
the characteristic-zero appendix route avoiding that assumption. Theorem D
is classification context here; this installment proves neither that theorem
nor its deep analytic and global inputs. Construction, exhaustion, strict
exponent bounds, same-block multiplicity symmetry, and unordered uniqueness
remain in the separate unitary generic classification installment. No
permutation invariance of arbitrary reducible induced representations is
claimed here.

## Published interfaces and development check

All project dependencies are imported by Lean name. The actual constructions
used are `PadicField.TopologicalData.twistedProductInduced` and
`segmentFactor`, `SmoothDual`, `smoothContragredient`, `smoothDualPairing`,
`SmoothRep.of`, `isSmooth_smoothContragredient`, `SmoothRep.twist`,
`InvariantPositiveForm`, `IsUnitarizable`, `T.IsSquareIntegrable`,
`HasScalarCharacter`, `realPowerCharacter`, and
`T.determinantPowerCharacter`.

The published proposition interfaces
`Parabolic.NormalizedInductionDualityClause`,
`Parabolic.NormalizedInductionTwistClause`,
`Parabolic.NormalizedInductionCentralClause`,
`Classification.GLConstituentCentralCharacterFor`, and
`Classification.AllPadicGLContragredientConstituentCompatibility` describe
the induction and constituent bridges relevant to later proofs. They are
imported interfaces, not hypotheses assumed true, and importing their
definitions supplies no proof of these new clauses.

The six direct project imports were hash-matched to published Library commit
`01a58491bc71539f1ecd3d5f0eec6ab8eae20fed`:

| Module, with prefix `Langlands.Representation.` | Lean SHA256 |
| --- | --- |
| `Classification.LanglandsData` | `3678fb721704683c1bbaddca5c363bea2fe96d462c0f2c2cfffdea7ab0f1f525` |
| `Classification.ConstituentCompatibility` | `e89c9a11f926900f00a05b6d69fbfecb305a4ef6f6ada56fef9c61cfdb724c63` |
| `Smooth.Contragredient.LawsProof` | `3585eafcf71cca3132c44cbe8da028f346227b8742ea8aa4b86251c343284ae3` |
| `Unitary.Twist` | `3ed348a86f5c803820bf27500458d461e75cba8ccafade2653df46374a09a3c6` |
| `Parabolic.NormalizedCompatibilityStatement` | `31896f590b2f394f7237e2296927410ded686ad3a2cc224d106095d0dc888f88` |
| `Parabolic.NormalizedInductionStatement` | `15c31e074841a316baf63908f17f7c0417f32f1a9918443b09ec5a4db10b78b8` |

The prepared environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Development check `ffeafce0-477d-40af-872d-5e2e0ee66589` completed the Lake
build with zero errors and warnings and inspected the all-fields aggregate as
a definition with `statement_returns_prop: true`. Its inspected statement
fingerprint is
`c059e300f68eb80ad37c42cccd63fd79b98321f51947324b6140698687d6cc91`.
This establishes elaboration and proposition shape, not proof acceptance or
independent semantic acceptance.

## Proof status

Three of the nine clauses are proved by published theorems whose types are
exactly those clauses, for every prime `p`, `F : PadicField.{uF} p` and
`T : F.TopologicalData`, with independent universes `uF` and `uV` and no
further hypotheses:

- `Langlands.Classification.unitaryAdmissibleHermitianClause`, in
  `Langlands.Representation.Classification.UnitaryAdmissibleHermitianProof`,
  proves `UnitaryAdmissibleHermitianClause.{uF, uV} F T`. Like the clause, it
  requires neither irreducibility nor square-integrability.
- `Langlands.Classification.twistedProductOrdinaryDual`, in
  `Langlands.Representation.Classification.TwistedProductOrdinaryDualProof`,
  proves `TwistedProductOrdinaryDualClause.{uF, uV} F T`.
- `Langlands.Classification.twistedProductCharacterTwist`, in
  `Langlands.Representation.Classification.TwistedProductCharacterTwistProof`,
  proves `TwistedProductCharacterTwistClause.{uF, uV} F T`.

A fourth clause, `RealTwistOrdinaryDualClause`, has no separately named
theorem of its type. Its mathematical content is nevertheless already
implemented. The public definition
`Langlands.Classification.segmentFactorSmoothDualEquiv`, in the same module
`Langlands.Representation.Classification.TwistedProductOrdinaryDualProof`,
constructs an actual equivariant linear equivalence from
`smoothContragredient (T.segmentFactor A s).representation` to the twist of
`smoothContragredient A.representation` by `T.determinantPowerCharacter r (-s)`.
It does this for every rank `r`, every smooth block `A` and every real `s`, and
the equivalence keeps every underlying functional. It assumes neither positive
rank, admissibility, irreducibility nor unitarity, and its universes `uF` and
`uV` are independent. Introducing the clause's variables and wrapping this
equivalence in `Nonempty` gives the clause exactly. A private development check
(`lean_check` diagnostic `125b5be2-bca6-4f9e-b740-226cc8b79f9b`) confirmed this
with zero errors and zero warnings. That check is not a published theorem. The
proof of `twistedProductOrdinaryDual` uses the same equivalence for each block.

For each of the remaining five clauses there is neither a published theorem of
that type nor a published declaration supplying its full content. Published
results cover some components, as listed below. Combining them into the
clauses would be new proof work; this account does not claim that work is done.

- `UnitaryBlockRealTwistHermitianClause`. The proved
  `unitaryAdmissibleHermitianClause` applies to a square-integrable block,
  because `Langlands.PadicField.TopologicalData.IsSquareIntegrable.isAdmissible`
  makes the block admissible. `segmentFactorSmoothDualEquiv` identifies the
  smooth dual of `ν^s δ` with a twist of that of `δ`. No published declaration composes them
  into the required conjugate-linear equivalence with source action
  `ν^(-s) δ`.
- `UnitaryBlockOrdinaryDualClause`. For irreducible admissible
  representations, irreducibility of the smooth contragredient is published as
  `Langlands.CompactSplitting.isIrreducible_smoothContragredient`, assuming
  cofinal compact open subgroups. For admissible unitarizable representations,
  unitarizability of the smooth contragredient is published as
  `Langlands.PadicField.TopologicalData.isUnitarizable_smoothContragredient`,
  which takes the proved Hermitian clause as input. No published theorem shows
  that the smooth contragredient of a square-integrable representation is
  square-integrable. The corresponding equivalence for
  `IsSquareIntegrableModCenter` and admissible representations occurs only as
  one component of the unproved proposition
  `Langlands.GLSquareIntegrabilityPrerequisitesStatement`.
- `UnitaryBlockCharacterTwistClause`. `Langlands.isIrreducible_twist_iff`
  covers irreducibility under any character twist, and
  `Langlands.isUnitarizable_twist_iff` covers unitarizability under unit-modulus
  twists. `Langlands.unitaryTwistModCenter` covers square-integrability modulo
  the center under open-kernel unit-modulus twists, for each Haar measure. No
  published declaration combines them for `χ ∘ det`.
- `TwistedProductCentralCharacterClause`.
  `Langlands.PadicField.TopologicalData.hasScalarCharacter_normalizedProductInduced`
  and `Langlands.PadicField.TopologicalData.hasScalarCharacter_segmentFactor`
  give scalar characters of normalized products and of the twisted blocks
  `ν^(s_i) δ_i`. No published declaration identifies the resulting character
  with `Ω` or proves the clause's two pointwise formulas.
- `ScalarCharacterTwistDualClause`. Its first conjunct, the
  determinant-twist formula, is supplied by a published theorem. The theorem
  `Langlands.Classification.glConstituentCentralCharacterFor`, in
  `Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof`,
  proves `GLConstituentCentralCharacterFor F n` for every field `F` and every
  natural number `n`. Its third conjunct says that if scalar matrices act on a
  representation `ρ` by `ω`, then they act on
  `twist (χ.comp Matrix.GeneralLinearGroup.det) ρ` by `ω * χ ^ n`, for every
  `χ : Fˣ →* ℂˣ`. The predicate `HasGLCentralCharacter` used there is an
  abbreviation for `HasScalarCharacter` at the scalar matrices. Taking
  `χ.toMonoidHom` and the representation of `π` gives the clause's first
  conjunct, `ω * χ.toMonoidHom ^ n`, exactly. That conjunct needs no
  admissibility, unitarity or irreducibility. A private development check
  (`lean_check` diagnostic `ee67e681-1923-4dcc-ae81-8fbc7856dc97`) confirmed
  this instantiation with zero errors; that check is not a published theorem.
  `Langlands.Classification.hasScalarCharacter_twist` gives the same
  character in the form
  `ω * (χ.toMonoidHom.comp determinant).comp GeneralLinear.scalar`.
  The second conjunct is not proved at the clause's scope. It says that
  whenever scalar matrices act on a smooth `π` by `ω`, they act on its smooth
  dual by `ω⁻¹`; `ω` is arbitrary and `π` need not be admissible. The
  published construction
  `Langlands.UnitaryCentralCharacter.contragredient`, in
  `Langlands.Representation.Classification.TemperedSmoothDualityProof`, inverts
  a central character on the smooth contragredient only for supplied unitary
  central-character data with open kernel. Otherwise the inverse character of
  the smooth dual is stated only in unproved propositions: as one component of
  `Langlands.Classification.AllPadicGLContragredientConstituentCompatibility`,
  for admissible representations, and as
  `Langlands.CentralCharacterContragredientStatement`, for central characters
  with open kernel. So the whole clause is not supplied.

Because no published declaration supplies these five clauses, none proves
`UnitaryGenericCompatibilityStatement F T` or
`AllPadicUnitaryGenericCompatibilityStatement`.
