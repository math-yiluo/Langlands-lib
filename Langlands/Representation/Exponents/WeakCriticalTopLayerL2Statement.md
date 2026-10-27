# Square-integrability of weakly critical maximal-layer quotients

This module defines the proposition
`Langlands.GLWeaklyCriticalTopLayerL2Statement` (universe parameters
`uF uV uW`). It states the assertion but does not prove it. Every object it
uses is an existing Library declaration, used unchanged. The module introduces
no new data.

Worker 322 wrote the Lean formulation. Worker 728 audited it against the source
and the published API, reused it unchanged, and wrote this Markdown.

## Exact statement

Fix a prime `p`, a field `F : PadicField.{uF} p` with supplied topological data
`T : F.TopologicalData`, and the topology `T.topology`. Let `n > 0` and let
`B : GeneralLinear.BlockShape n` be a block shape. Let
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)` satisfy

- `Representation.IsIrreducible A.ρ`, and
- `T.IsTempered A.ρ`.

Let `χ : (Fin B.length → F.Carrierˣ) →* ℂˣ` satisfy

```
T.IsWeaklyCriticalDualJacquetExponent (Exponents.ConjugateBlockPair.standard B) A χ.
```

Let `d` be a natural number with `0 < d` and

```
T.dualJacquetExponentNilpotenceIndex B A χ = (d : ℕ∞).
```

Let `a : Fin B.length → F.Carrierˣ` be any block scalar, and let
`S : Rep.{uW} ℂ (B.Levi F.Carrier)` satisfy

- `Representation.IsIrreducible S.ρ`;
- `IsAdmissible S.ρ`, for the Levi topology with `T.leviTopologicalGroup B`;
- `Classification.HasScalarCharacter S.ρ (B.blockScalarLevi F.Carrier) χ`.

Let `q` be a full-Levi intertwining map from
`(T.dualJacquetCharacterDefectRangeRepresentation B A χ a (d - 1)).ρ` to
`S.ρ`, with `Function.Surjective q`.

Then, with `Q := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)`, for
every `[MeasurableSpace Q]` with `[BorelSpace Q]` and every Haar measure `μ` on
`Q`, `IsSquareIntegrableModCenter S.ρ μ` holds.

Since `0 < d`, the natural subtraction `d - 1` is the ordinary predecessor.
When `d = 1` the zeroth power is used, so the range is the whole character
quotient.

## Meaning of the objects used

- **Source hypotheses.** `Representation.IsIrreducible` is `IsSimpleOrder` on
  subrepresentations, so the carrier is nonzero. `T.IsTempered A.ρ` is the
  analytic predicate of `Classification/Tempered.lean`. For every Borel Haar
  measure on `GL_n(F)` modulo its center, it asks for admissibility, a unitary
  central character, and `MemLp` coefficient bounds of every exponent `2 + ε`.
  It is not an exponent-only substitute.
- **Normalized opposite Jacquet module.**
  `CuspidalJacquetMultiplicity.oppositeJacquet T B A` is the module of
  coinvariants of `A` under the opposite unipotent radical
  `B.oppositeUnipotentSubgroup`. It carries the action of the full product
  Levi `B.Levi F.Carrier`, with `m` acting by `δ(m)^{1/2} · A.ρ(m)`, where
  `δ = T.leviModulus B` is the upper block modulus. The Library restricts it to
  block scalars as
  `T.splitCentreOppositeJacquet B A`; the same-order transpose on the full
  algebraic dual is `T.splitCentreDualJacquet B A`. This transpose has no
  inversion and no complex conjugation.
- **Nilpotence index.** `T.dualJacquetExponentNilpotenceIndex B A χ` is
  `commutativeCharacterNilpotenceIndex` of that transpose at `χ`. It is the
  least `k` for which a single power `k` kills `T a - χ a` on the whole
  generalized `χ`-component of the dual, uniformly in `a`, and `⊤` if there is
  no such `k`. The hypothesis thus says that this component is nonzero, has a
  finite uniform exponent, and that this exponent is exactly `d`. The index is
  taken at `B, A`, the same coordinates in which the range representation is
  built.
- **Weak criticality.** `T.IsWeaklyCriticalDualJacquetExponent P A χ`, from
  `Exponents/WeakCritical.lean`, is used unchanged at
  `P = ConjugateBlockPair.standard B = ⟨B, 1⟩`. It requires two things.
  - `χ` is a unitary dual exponent of the pulled-back source
    `P.pullbackRep A`: the kernel of `χ` is open, `χ` has a nonzero dual
    eigenspace, and `‖χ a‖ = 1` for all `a`.
  - For every concrete conjugate pair `Q` with `Q.StrictlyRefines P`, every
    unitary dual exponent `ψ` of `Q.pullbackRep A` with
    `Q.CharacterExtends P _ ψ χ` has nilpotence index at `Q` strictly smaller
    than the index of `χ` at `P`.

  `StrictlyRefines` compares the actual parabolic and split-component
  subgroups, not their presentations. Every concrete conjugate pair is
  quantified, not only standard pairs.
- **Character quotient and maximal layer.** These come from the accepted
  module `Langlands.Representation.Exponents.DualCharacterQuotient`.
  `T.dualJacquetCharacterQuotient B A χ` is the quotient of the full opposite
  Jacquet module by the common kernel of the generalized `χ`-component of the
  dual. It keeps the full Levi action and the carrier universe `uV`.
  `T.dualJacquetCharacterDefect B A χ a` is the full-Levi endomorphism
  `D_a = ρ(blockScalarLevi a) - χ(a)` of that quotient.
  `T.dualJacquetCharacterDefectRangeRepresentation B A χ a (d - 1)` is the range
  `W` of `D_a ^ (d - 1)` with the full-Levi representation it inherits.
- **Target hypotheses.** `IsAdmissible S.ρ` is taken for the product topology
  on `B.Levi F.Carrier` given by `T`. `Classification.HasScalarCharacter` means
  `S.ρ (blockScalarLevi c) w = χ(c) • w` for all `c` and all `w`. The map `q`
  is an actual `Representation.IntertwiningMap` for the full Levi, and it is
  surjective. So `S` is an irreducible quotient of the maximal layer `W`.
- **Conclusion.** `IsSquareIntegrableModCenter S.ρ μ`, from
  `MatrixCoefficient/ModuloCenter.lean`, is `IsAdmissible S.ρ` together with a
  `UnitaryCentralCharacter` datum `c` such that, for every smooth-dual
  functional `ℓ` and every vector `v`, the descended coefficient norm
  `c.coefficientNorm ℓ v` lies in `MemLp 2 μ`. The quotient is by the full
  actual center of the product Levi. The conclusion holds for every Borel
  measurable structure on it and every Haar measure. This clause is copied
  from the published `GLWeaklyCriticalDiscreteSeriesSupportStatement`.

## Scope

- The field, source-carrier and quotient-carrier universes `uF`, `uV`, `uW`
  are independent.
- No tensor factorization of `S` and no extra unitarity of `A` is assumed. Nor
  is it assumed that finer exponents are absent; criticality is retained
  exactly.
- The statement does not assert that `W` is nonzero, that an irreducible
  quotient `S` exists, that `S` embeds into an induced representation, or that
  `S` is an opposite Jacquet class exponent. Those are separate algebraic
  results. Since `S` is irreducible and `q` is surjective, the hypotheses
  already force `W ≠ 0`.
- The selected maximal layer is not replaced by an arbitrary tempered
  constituent. No vanishing of weak constant terms, no `L²` criterion and no
  analytic bridge appears as a hypothesis. Irreducibility, admissibility,
  scalar action and the actual quotient map isolate the analytic step from the
  algebraic ones.
- **Coordinates.** The index hypothesis and the range representation use
  `B, A`. The critical predicate uses its published convention: at the
  standard pair it reads the pulled-back source
  `(standard B).pullbackRep A`, which is `A` conjugated by the matrix `1`.
  This equals `A` as a representation but not by definition. The proof must
  supply this transport. It is not a new hypothesis replacing criticality.

## Provenance

This is a derived internal analytic criterion, not a verbatim theorem of the
source. The source is Silberger, *Introduction to harmonic analysis on
reductive p-adic groups* (1979), registered as
`silberger-1979-harmonic-analysis` with SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`. The PDF page
number is the printed page number plus six. Worker 728 reread the pages below.

- **Printed p.189 (PDF p.195).** This page defines weakly `π`-minimal and weakly
  `π`-critical pairs and exponents. `χ ∈ wX_π(P, A)` is weakly `π`-critical if
  `d(χ') < d(χ)` for every `(P', A') ⊊ (P, A)` and every
  `χ' ∈ wX_π(P', A')` with `χ'|A = χ`. Our critical predicate is the published
  Library version of this definition, used unchanged. It represents the weak
  class exponents by unitary dual exponents of the pulled-back source.
- **Corollary 4.5.11, printed pp.189–190 (PDF pp.195–196).** Let `π` be
  irreducible admissible tempered. If `(P, A)` is a standard weakly
  `π`-critical pair and `χ` a weakly `π`-critical exponent, then
  `π ⊂ Ind(δ^{1/2}σ)` with `σ ∈ ω ∈ E₂(M)`, and `ω` may be chosen with
  central exponent `χ`. The proof first applies Corollary 4.5.7. It then
  says "Applying Corollary 4.5.9, Theorem 4.5.10, Theorem 3.2.4, and arguing
  as in Corollary 2.4.2, we obtain `ω ∈ E₂(M)`". The present statement
  isolates the analytic part of that sentence. An irreducible quotient of the
  maximal image is square-integrable modulo the center.
- **Corollary 4.5.9, printed p.188 (PDF p.194).** This is transitivity of weak
  constant terms along a chain of parabolic pairs.
- **Theorem 4.5.10, printed pp.188–189 (PDF pp.194–195).** This characterizes
  square-integrability modulo the center: by weak constant terms vanishing on
  all proper pairs, and by exponent inequalities.
- **Theorem 3.2.4, printed p.122 (PDF p.128).** For irreducible admissible
  `π`, every matrix coefficient `h` of `V/V(N̄)` is related to a coefficient
  `f` of `π` by `f_P = δ_P^{1/2} h`. Hence the class of an irreducible
  subquotient of `V/V(N̄)` is a class exponent of `π`. This is how the proof
  of Corollary 4.5.11 passes from a quotient of the Jacquet module to
  coefficients of the source.
- **Corollary 2.4.2, printed pp.91–92 (PDF pp.97–98).** This is the
  maximal-image construction. It uses the multiplicity `d(χ)` and the quotient
  `V̄_χ`, with dual `V'_χ`, from printed p.91, and the image `W` of
  `(π̄(a) − δ^{1/2}(a)χ(a))^{d-1}` from printed p.92. The Library's published
  `DualCharacterQuotient` objects realize this construction.

The source text and the central library contain no erratum for these pages.

Our objects correspond to Silberger's as follows.

| Silberger | This statement |
| --- | --- |
| the Levi `M` of a standard pair | `B.Levi F.Carrier` |
| the split component `A` | block scalars, via `blockScalarLevi` |
| `π̄` on `V/V(N̄)` | `CuspidalJacquetMultiplicity.oppositeJacquet T B A` |
| `V'_χ`, `d(χ)` | the generalized dual component, its nilpotence index `d` |
| `V̄_χ`, `W` | the character quotient, the range of `D_a^(d-1)` |
| an irreducible quotient of `W` | `S` with the surjection `q` |
| `ω ∈ E₂(M)` | `IsSquareIntegrableModCenter S.ρ μ` for every Haar `μ` |

The Library's opposite Jacquet module already carries its normalization, so
Silberger's `δ^{1/2}χ` corresponds to our `χ`.

The project made three choices. The source representation is irreducible and
analytically tempered. The quotient `S`, its irreducibility, admissibility and
scalar action are explicit hypotheses rather than constructions. The
conclusion is quantified over every Borel Haar measure.

## Proof obligations

These are for the separate proof task. Nothing here is assumed or proved.

- **Coordinate transport.** Relate `(standard B).pullbackRep A` to `A`, so that
  the criticality data at `standard B` can be compared with the index at
  `B, A`.
- **Analytic comparison.** Suppose `S` had a nonzero weak constant term along a
  proper parabolic pair of the Levi. The argument would then produce a strictly
  finer concrete pair `Q` of `GL_n`. It would also produce a unitary exponent
  `ψ` of `Q.pullbackRep A` extending `χ`, of nilpotence index at least `d`.
  That contradicts weak criticality. This needs an actual analytic comparison
  for arbitrary product Levi groups. Algebraic Jacquet transitivity alone does
  not establish it.
- **`L²` conclusion.** The `MemLp` bound at exponent `2` must follow from the
  vanishing of proper weak constant terms. A weak half-modulus bound times a
  polynomial height does not give it.
- **Forbidden routes.** The proof must not use the host support theorem,
  critical-to-minimal equivalence, ordinary tempered discrete-series support,
  tempered exhaustion, unitarity or genericity, regular exhaustion, or
  equal-exponent grouping.
