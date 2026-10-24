# Analytic temperedness and square-integrability of actual GL block tensors

Author: Worker 161. Worker 47 specified the target and its dependency boundary.

## Statements and quantifiers

This module defines three closed propositions:
`Langlands.GLBlockTensorTemperedStatement`,
`Langlands.GLBlockTensorSquareIntegrableStatement`, and their conjunction
`Langlands.GLBlockTensorAnalyticStatement`. It proves neither comparison.
The conjunction is one statement contribution; its two components can be proved
separately.

Fix any prime `p`, a finite extension `F : PadicField.{uF} p`, and any supplied
`T : F.TopologicalData`. Fix `n > 0` and an actual ordered block shape
`B : GeneralLinear.BlockShape n`. Its positive sizes sum to `n`, and its indices
are `i : Fin B.length`. In particular there is at least one block.
Quantify over every family of complex vector spaces `V i : Type uV` and actual
representations

```text
ρ i : Representation ℂ (GL_(B.size i)(F)) (V i).
```

The field universe `uF` and carrier universe `uV` are independent. There is no
countability or finite-dimensionality assumption on the carriers and no topology
on them. Each `ρ i` is assumed irreducible and admissible. Algebraic
irreducibility includes nontriviality; zero factors are excluded.

Put `M = B.Levi F.Carrier = ∏ i, GL_(B.size i)(F)` and `Q = M / Z(M)`.
Install `T.topology`, the supplied product topology `T.leviTopology B`, and
the proved instance `T.leviTopologicalGroup B`. The quotient has the actual
quotient topology; neither a discrete topology nor a transported substitute is
chosen. The representation of `M` is precisely

```text
σ = B.blockTensor ρ = FiniteTensor.external ρ
  : Representation ℂ M (PiTensorProduct ℂ V).
```

The published `blockTensor_tprod` gives its action:
`σ(m)(⊗ᵢ vᵢ) = ⊗ᵢ (ρ i (m i) vᵢ)`. This is an algebraic finite tensor product,
without any completed tensor product or symbolic representation.

Under these hypotheses the two targets assert, respectively,

```text
(∀ i, T.IsTempered (ρ i)) ↔
  ∀ Borel measurable-space realizations on Q, ∀ Haar measures μ on Q,
    IsTemperedModCenter σ μ;

(∀ i, T.IsSquareIntegrable (ρ i)) ↔
  ∀ Borel measurable-space realizations on Q, ∀ Haar measures μ on Q,
    IsSquareIntegrableModCenter σ μ.
```

The Lean quantifiers on the right are `[MeasurableSpace Q] [BorelSpace Q]`,
followed by `(μ : Measure Q) [μ.IsHaarMeasure]`. In particular these
quantifiers are **inside the right side of each equivalence**. The forward
direction supplies the property for any such measure; the reverse direction
assumes it for all of them. `BorelSpace` requires equality with the Borel
σ-algebra of the specified quotient topology. On the factor side,
`T.IsTempered` and `T.IsSquareIntegrable` already quantify over every Haar
measure on the canonical Borel measurable space of that factor's actual
central quotient.

This is the same actual Levi and Borel Haar convention used by
`GLTemperedInductionStatement`. Its result is not an input. The existing
`T.exists_isHaarMeasure_centralQuotient` and
`T.exists_isHaarMeasure_leviCentralQuotient` establish nonvacuity of the
respective measure quantifications. The latter helper is in
`Classification/TemperedInductionStatement`; the present module need not import
that statement module to refer to its already proved existence fact.

## Exact meaning of the analytic predicates

`IsAdmissible ρ` in `Smooth/Definitions` means smoothness together with
`Module.Finite ℂ (fixedVectors ρ K)` for **every open subgroup** `K`.
Smoothness means that every vector is fixed by an open subgroup. Over `ℂ`,
`Module.Finite` means finite-dimensionality. This retains the Library's exact
all-open convention. For the locally profinite groups here, the usual
compact-open convention gives it because every open subgroup contains a
compact open subgroup and its fixed space is a subspace of that smaller
subgroup's fixed space. No such equivalence is proved in this statement file.

`SmoothDual ρ` is the smooth-vector subspace of the full algebraic dual, for
the contragredient action `(g · ℓ)(v) = ℓ(ρ(g⁻¹)v)`. A matrix coefficient is
`g ↦ ℓ(ρ(g)v)`, with `ℓ` ranging over this smooth dual and `v` over the entire
carrier. The statement does not test only pure tensor vectors or functionals.

`UnitaryCentralCharacter ρ` consists of a homomorphism
`Z(G) → ℂˣ` with open kernel, norm one at every central element, and a proof
that the center acts by its scalars. The analytic predicate existentially
quantifies this datum; no central character is supplied as a premise.
For such a datum `c`, the published construction
`c.coefficientNorm ℓ v` is the real nonnegative function on `G/Z(G)` with value
`‖ℓ(ρ(g)v)‖` at `gZ(G)`. Its well-definedness follows from the scalar action
and norm-one character, and is already proved in `MatrixCoefficient/ModuloCenter`.
It is the norm, rather than the complex coefficient itself, that descends.

`IsSquareIntegrableModCenter ρ μ` is admissibility and the existence of
such a `c` for which every descended coefficient norm belongs to
`MemLp … 2 μ`. `IsTemperedModCenter ρ μ` uses
`MemLp … (ENNReal.ofReal (2 + ε)) μ` for every real `ε > 0`.
These conditions include the measurable-function requirement of `MemLp`.
The existential character is inside the fixed-measure predicate, so the
syntax permits it to depend on the measure. The published
`coefficientNorm_eq` shows that the descended function is independent of the
chosen character datum. Neither predicate assumes unitarizability or uses
exponents, induction, or classification as its definition.

The measures satisfy Mathlib's `Measure.IsHaarMeasure` on the actual quotient.
No volume normalization is imposed. Quotient comparison, product integration,
and invariance under positive finite rescaling must justify passage from
product measures to all the measures quantified here; those are proof
obligations below, not implicit fields of a certificate.

## Source correspondence and provenance

The exact finite-product equivalences are **derived product statements**.
They are not attributed verbatim to a theorem in the following originals.
The sources specify the analytic conventions, and the tensor/coefficient
argument described below explains the derivation that a later proof must
implement. All cited originals were read at the indicated locations.

| Registered original | Exact location | Correspondence |
| --- | --- | --- |
| Stephen S. Kudla, *The local Langlands correspondence: the non-archimedean case*, in *Motives*, Part II (1994), `kudla-1994-local-langlands-nonarchimedean` | Printed p.367 (one-based PDF p.377), and §2.2, printed p.372 (PDF p.382) | Smooth admissible representations and their smooth duals; temperedness by unitary central character and all `L^(2+ε)` coefficients modulo the center. |
| W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive groups*, draft 1 May 1995, `casselman-1995-admissible-representations` | §2.5, printed/PDF p.28, after Corollary 2.5.2 | Smooth-dual matrix coefficients, their smoothness, and square-integrability of an admissible scalar-central-character representation, requiring a unitary character and all absolute coefficients in `L²(G/Z)`. |
| A. J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic Groups* (1979), `silberger-1979-harmonic-analysis` | §4.5, printed p.184 (PDF p.190) | Related definition by tempered coefficient functions. This is context, not a finite tensor comparison or an identification already proved with the Library's `L^(2+ε)` definition. |
| J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques d'après Harish-Chandra* (2003), `waldspurger-2003-plancherel` | §III.2 and Proposition III.2.2, printed pp.265–266 (PDF pp.31–32) | Related weak coefficient bound and exponent criterion. Neither replaces the required tensor/coefficient product argument. |

The corresponding SHA256 fingerprints are:

```text
Kudla:       0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b
Casselman:   78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a
Silberger:   b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc
Waldspurger: 4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7
```

No source-specific errata file was present in the consulted Library notes.
Kudla writes `Z\G`, whereas Lean uses `G/Z`; centrality identifies these cosets.
Kudla's irreducible algebraic scope is retained by the explicit irreducibility
and admissibility assumptions. The general reductive conventions of Casselman,
Silberger and Waldspurger are used here only for GL factors and their finite
product. No assertion about all reductive groups is made.

## Remaining proof obligations and reuse

A proof of these targets must implement the following steps, or another
complete argument. This list records mathematical obligations and does not
assert that their analytic comparisons are already proved in Lean.

1. **Centers and quotient topology.** Identify `Z(∏ᵢ Gᵢ)` with `∏ᵢ Z(Gᵢ)`
   and construct the actual topological group isomorphism
   `(∏ᵢ Gᵢ)/Z(∏ᵢ Gᵢ) ≃ ∏ᵢ (Gᵢ/Z(Gᵢ))`. Verify its Borel compatibility and
   Haar transport for the supplied `T`, rather than substituting the ambient
   scalar center of `GL_n` for the full center of the product Levi.
2. **Central characters.** Assemble the factor characters into a smooth
   unitary character of the product center and prove its action on tensors.
   Conversely, restrict a tensor's unitary central character to each central
   coordinate and recover its scalar action on that factor using nonzero
   vectors in the other factors and linear contractions. Verify open kernels
   and norm one. Nontriviality is essential here.
3. **Smooth functionals and coefficients.** Construct products of smooth
   functionals and show that every smooth functional on the external tensor
   is a finite sum of such products under admissibility. One route fixes a
   product of compact open subgroups inside its stabilizer and uses averaging
   projections onto finite-dimensional fixed spaces. The dual of their finite
   tensor then decomposes as a tensor of duals; pulling back along these
   projections gives smooth factor functionals. This needs proof and cannot
   be replaced by the false assertion that the full dual of an arbitrary
   infinite-dimensional tensor is the tensor of full duals. Together with
   finite sums of pure vectors, prove that every actual coefficient is a
   finite sum of products of factor coefficients.
4. **Product integration, forward direction.** For each finite exponent
   `r = 2` or `r = 2 + ε`, prove measurability and the product integral formula
   for the `r`th powers of the nonnegative pure coefficient norms. Deduce
   `MemLp` for pure coefficients and then for the finite sums from step 3,
   using the norm triangle inequality and finite-sum `L^r` bounds. Prove the
   required measure hypotheses for Tonelli/Fubini on these quotients.
5. **Nonzero-factor reflection.** For an arbitrary coefficient in a chosen
   factor, choose smooth coefficients nonzero at the identity in all other
   factors, using nontriviality and separation by the smooth dual. Their
   norms are bounded below on neighborhoods with positive finite Haar
   measure. Integrating the product coefficient on the chosen factor times
   these neighborhoods forces that factor's `r`th-power integral to be
   finite. This avoids restricting an `L^r` function to a potentially
   measure-zero coordinate slice, and does not assume in advance that the
   other factors are integrable. Apply this for every coefficient and, for
   temperedness, every positive `ε`.
6. **All Haar realizations.** Transport product measures across step 1 and
   establish the Haar uniqueness and positive finite rescaling comparison
   needed for every Borel Haar measure in the targets. Establish any local
   compactness, second-countability or sigma-finiteness hypotheses used from
   the actual p-adic topology. No countability of the representation carrier
   or equality of field and carrier universes may be added.

Reuse the published tensor action and pure-tensor formula from `Tensor/Finite`
and `Induction/BlockFactors`. `FiniteTensor.isSmooth_external` and
`FiniteTensor.isAdmissible_external` already give the relevant smoothness and
admissibility preservation. `FiniteTensor.isIrreducible_external` is the
existing irreducibility result with its scalar-endomorphism hypotheses; it
is not necessary to add tensor irreducibility as a premise of these targets.
The algebraic factorization of an arbitrary irreducible admissible Levi
representation in `CuspidalSupport/LeviAdmissibleFactorizationProof` is a
separate published result. It does not supply this analytic comparison and is
not reproduced.

The only imports here are `Classification/Tempered` and
`Induction/BlockFactors`, supplying the predicates and actual tensor.
The statement assumes no downstream induction theorem, tempered
classification, square-integrable classification, or regular Langlands
uniqueness. Those results may consume the proved comparisons later.
