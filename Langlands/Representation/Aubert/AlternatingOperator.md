# The unadjusted alternating induction–Jacquet operator

Implementation and documentation: Worker 1180. Mathematical specification:
Worker 320 (task `a145f2e4-6268-470c-b7bc-0d6946db41d0`).

This module defines the unadjusted alternating sum of Aubert's Definition 1.5
on the exact Grothendieck group of finite-length smooth complex representations
of `GL_n` over a p-adic field. It first names the integer-linear maps induced by
actual normalized parabolic induction and the actual normalized Jacquet functor,
proves their generator formulas and uniqueness, and then forms the signed sum
over all ordered positive block shapes. It proves no involutivity, commutation
identity or irreducibility statement.

## Source and sign convention

Registered original: `aubert-1995-duality`, Aubert, *Dualité dans le groupe de
Grothendieck de la catégorie des représentations lisses de longueur finie d'un
groupe réductif p-adique*, Trans. Amer. Math. Soc. 347 (1995), 2179–2189,
SHA-256 `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
Définition 1.5, printed p.2181 (PDF page 3, checked on the rendered page),
defines on the Grothendieck group `R(G)` of finite-length smooth
representations

    D_G := sum_{I ⊂ S} (-1)^|I| i^G_{L_I} ∘ r^G_{L_I},

where `S` is the set of simple roots for a fixed minimal parabolic, `L_I` is
the standard Levi subgroup of the standard parabolic `P_I` determined by `I`,
and `i`, `r` are the normalized Bernstein–Zelevinsky induction and restriction
functors (p.2180, citing [BZ, 2.3]).

In positive rank, for `GL_n` with its upper triangular Borel subgroup, the standard parabolic
subgroups are the upper block parabolics. A subset `I` of the `n - 1` simple
roots corresponds to exactly one ordered composition of `n`: the blocks are the
maximal runs of consecutive indices joined by roots in `I`. This is an ordered
positive block shape `B : GeneralLinear.BlockShape n`, and `L_I` is its
block-diagonal Levi `B.Levi`. The roots of `I` are the simple roots inside the
blocks, so

    |I| = sum_i (B.size i - 1) = n - B.length.

The coefficient implemented here is therefore exactly
`(-1 : ℤ) ^ (n - B.length)`. Since `B.length ≤ n` (`BlockShape.length_le`), the
natural-number subtraction is the true difference. The one-block shape
(`I = S`, Levi `GL_n`) has coefficient `(-1)^(n-1)` in positive rank; the shape
with `n` blocks of size one (`I = ∅`, the diagonal torus) has coefficient `1`.

This is not the sign-adjusted operator of Aubert's Definition 2.1 (printed
p.2184), which multiplies `D_G` by a cuspidal-support-dependent sign. No such
adjustment is made here. See `notes/henniart/aubert-duality-route.md` for the
retained source boundaries; the 1996 erratum and the Ban–Jantzen repair concern
later irreducibility arguments and do not affect this elementary definition.

The identification of subsets of simple roots with ordered block shapes is a
standard translation for `GL_n`; it is explained here and is not itself a Lean
theorem of this module. The Lean definition sums directly over block shapes.

## Groups, functors and universes

All declarations take `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)` and install exactly `letI := T.topology`; `T` is any
supplied topological realization, not only the canonical one. The field
universe `uF` and the carrier parameter `uV` are independent, and every
representation carrier is in `Type (max uF uV)`. Inspection of
`Langlands.Aubert.alternatingOperator` reports level parameters `[uF, uV]`.

The groups are the published exact Grothendieck groups from
[`Smooth.FiniteLengthGrothendieck`](../Smooth/FiniteLengthGrothendieck.md):
`GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier` and
`B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier`. Each is the free integral
module on genuine isomorphism classes of actual smooth representations of
finite group-algebra length, modulo the relations of all actual short exact
sequences, nonsplit ones included. Zero representations, every rank and
arbitrary representations of the product Levi are included. No tensor
factorization or finite-dimensionality restriction is imposed.

The functors are the published
`T.normalizedParabolicInductionFunctor.{uF, max uF uV} B` from
[`Induction.Parabolic`](../Induction/Parabolic.md) and
`T.normalizedJacquetFunctor.{uF, max uF uV} B` from
[`Jacquet.Parabolic`](../Jacquet/Parabolic.md), unchanged. Induction is from
the standard upper block parabolic, with right translation and the covariance
`f(p g) = δ_P(m(p))^(1/2) • σ(m(p)) (f g)` (`T.normalizedParabolicInduced_covariant`,
`B.normalizedInducedOf_apply`). The Jacquet module is the quotient by upper
unipotent coinvariant relations with Levi action
`m · [v] = δ_P(m)^(-1/2) • [ρ(m) v]` (`T.normalizedJacquet_mk`,
`T.normalizedJacquet_mk_eq_inv_halfModulus`). Induction's output level
`max uF (max uF uV)` is definitionally `max uF uV`.

## The named maps (namespace `Langlands.Parabolic`)

For every `n : ℕ` and `B : GeneralLinear.BlockShape n`:

```lean
normalizedInductionK0 F T B :
  B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier
normalizedJacquetK0 F T B :
  GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier
```

These are exactly the domains and codomains of
`NormalizedInductionGrothendieckStatement` and
`NormalizedJacquetGrothendieckStatement`. They have no preservation,
admissibility or exactness premises. Each is the published generic functor map
`B.finiteLengthMapToGeneralLinear` (respectively
`B.finiteLengthMapFromGeneralLinear`) of
[`Smooth.FiniteLengthGrothendieckFunctor`](../Smooth/FiniteLengthGrothendieckFunctor.md),
applied to the actual functor together with:

- finite-length preservation: the clause `.1 n B` (respectively `.2 n B`) of
  the published `normalizedParabolicFiniteLength.{uF, max uF uV} F T`;
- exactness: the published
  `FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact F T B`
  (respectively `normalizedJacquetFunctor_preservesShortExact`).

These are the same three inputs from which the published proof of
`normalizedParabolicGrothendieck` obtains its maps.

Theorems about the induction map (the Jacquet map has the same four theorems,
with `normalizedJacquetK0_*` names, `GeneralLinear.finiteLengthClass` as input
and `B.finiteLengthClass` as output):

- `normalizedInductionK0_hasFiniteLength`: for every actual
  `A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)` of finite length, the
  actual induced representation has finite length (the published theorem).
- `normalizedInductionK0_finiteLengthClass`: for every such `A`, `hA`, and
  **every** proof `hOut` that the output has finite length,
  `normalizedInductionK0 F T B (B.finiteLengthClass F.Carrier A hA) =
  GeneralLinear.finiteLengthClass n F.Carrier
  ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A) hOut`.
  Thus any choice of output-length proof gives the same class.
- `normalizedInductionK0_spec`: the generator property of the published clause,
  `∀ A hA, ∃ hOut, …`, holds for the named map.
- `normalizedInductionK0_eq_iff`: an integer-linear map `i` with the same domain
  and codomain equals `normalizedInductionK0 F T B` if and only if it has that
  generator property. The reverse direction is the uniqueness clause of the
  published `normalizedParabolicGrothendieck.{uF, uV} F T`; in particular the
  named map is the unique map of that theorem.

## The alternating operator (namespace `Langlands.Aubert`)

```lean
def alternatingOperator (n : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  letI : Fintype (GeneralLinear.BlockShape n) := Fintype.ofFinite _
  ∑ B : GeneralLinear.BlockShape n,
    ((-1 : ℤ) ^ (n - B.length)) •
      (normalizedInductionK0.{uF, uV} F T B).comp (normalizedJacquetK0.{uF, uV} F T B)
```

The enumeration is `Fintype.ofFinite` of the published instance
`GeneralLinear.BlockShape.finiteBlockShape` from
[`CuspidalSupport.FiniteBlockShapes`](../CuspidalSupport/FiniteBlockShapes.md);
no new finiteness assumption is made. The sum runs over `Finset.univ`, so every
actual ordered positive block shape occurs exactly once. The scalar
multiplication and sum are those of the integer module of linear endomorphisms
of the Grothendieck group.

Rank zero is included. Every block shape of rank zero has length zero
(`length_le`), so the empty shape is the only term, with exponent `0 - 0 = 0`
and coefficient `1`. Its Levi is the empty product. No further statement about
the rank-zero operator is proved here.

Theorems exposing the definition:

- `alternatingOperator_eq_sum`: for **any** instance
  `[Fintype (GeneralLinear.BlockShape n)]`, the operator equals the displayed
  sum; the enumeration choice is irrelevant (`Fintype` is a subsingleton).
- `alternatingOperator_apply`: for every virtual class `x`,
  `alternatingOperator F T n x = ∑ B, (-1)^(n - B.length) •
  normalizedInductionK0 F T B (normalizedJacquetK0 F T B x)`.
- `normalizedInductionJacquet_hasFiniteLength`: for every actual finite-length
  `A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)` and every
  `B`, the actual representation
  `(T.normalizedParabolicInductionFunctor B).obj ((T.normalizedJacquetFunctor B).obj A)`
  has finite length (the published finite-length theorem applied twice).
- `alternatingOperator_finiteLengthClass_of_hasFiniteLength`: for every such
  `A`, `hA` and every family `hOut B` of output finite-length proofs,

  ```lean
  alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
    ∑ B, ((-1 : ℤ) ^ (n - B.length)) •
      GeneralLinear.finiteLengthClass n F.Carrier
        ((T.normalizedParabolicInductionFunctor B).obj
          ((T.normalizedJacquetFunctor B).obj A)) (hOut B)
  ```

  with both functors at `.{uF, max uF uV}`.
- `alternatingOperator_finiteLengthClass`: the same formula with the output
  proofs supplied by `normalizedInductionJacquet_hasFiniteLength`.

Proof of the generator formula: expand by `alternatingOperator_apply`, then
rewrite each summand with the Jacquet generator formula (output proof from the
published finite-length theorem) and the induction generator formula (output
proof `hOut B`).

## Provenance

The alternating formula and its sign are Aubert's Definition 1.5, translated
to ordered block shapes of `GL_n` as explained above. The named maps, their
generator formulas, the uniqueness assertion and the generator formula of the
operator are internal consequences of the published actual K0 theorem
`Langlands.Parabolic.normalizedParabolicGrothendieck` and of the published
generic construction, finite-length theorem and exactness theorems from which
that theorem is proved. Their exact Lean formulation (existential or arbitrary
output-length proofs, universes, enumeration) is internal and is not
attributed verbatim to the literature.

Not established here: Aubert's Theorem 1.7 (involutivity, commutation with
induction, Jacquet restriction and contragredients), the sign-adjusted
operator, images of irreducibles, an irreducible basis, and segment
socle-to-special-quotient comparisons. These require later units.

## Imports and independence

Direct imports: `Langlands.Representation.Parabolic.FiniteLengthGrothendieckProof`
and `Langlands.Representation.CuspidalSupport.FiniteBlockShapes`. No existing
Library file is edited; the group, functor, preservation and K0 proof pairs are
reused unchanged.

The recursive project import closure, computed from actual import lines at
Library base `5265467bd3fd94308df2e30a20d91abedd90f413`, has 599 modules.
`FiniteBlockShapes` already lies in the closure of
`FiniteLengthGrothendieckProof`, so this module adds no project dependency
beyond the closure of the published K0 proof, which Worker 320 audited against
the exclusions below. A text search of all 599 closure sources finds none of
the target declarations or target statement modules of the excluded tasks:
analytic segment classification `aca8805b-054f-4d56-8045-12db7f623404`;
special-head multisegment exhaustion `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`;
ordered strong-head existence `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`;
quotient coverage `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; tempered block
uniqueness `52e97845-36bb-457d-b76f-70753334b88c`;
`SquareIntegrableLanglandsClassification` /
`1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion
`cd8ab97c-0b78-4bce-97c4-d307a28159a4`; and regular exhaustion
`bf433f0a-921a-428c-b0c0-6475438125ac`. The searched names were
`segmentEssentialSquareIntegrableClassification`,
`multisegmentHeadExhaustion`, `orderedMultisegmentHeadExistence`,
`orderedMultisegmentQuotientExhaustion`, `temperedBlockUniqueness`,
`squareIntegrableLanglandsClassification`,
`SquareIntegrableLanglandsClassification`,
`squareIntegrableLanglandsExhaustion`, `glRegularLanglandsExhaustion`,
`MultisegmentClassificationStatement`, `SegmentSquareIntegrability`,
`TemperedBlockStatement`, `RegularLanglandsStatement` and
`MultisegmentQuotientExhaustionStatement`.

## Development validation

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
module with zero errors and zero warnings (diagnostic
`98082296-3990-4d6b-8e9a-862de8e81fd8`). Inspection of
`Langlands.Aubert.alternatingOperator` reports kind `definition`, level
parameters `["uF", "uV"]`, and only `propext`, `Classical.choice` and
`Quot.sound` as axioms. Compilation is not acceptance; independent semantic
review and Library publication are separate requirements.
