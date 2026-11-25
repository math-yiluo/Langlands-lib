# Canonical Grothendieck maps for the actual normalized parabolic functors

This internal derived statement module defines exactly three
transparent propositions in `Langlands.Parabolic`. It constructs no map and
proves neither clause.

## Parameters, categories and groups

The outer parameters are exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. The two clause definitions install only
`letI := T.topology`; the combined definition is their conjunction.
Thus `T` is any supplied topological realization of the p-adic field, rather
than a specialization to its canonical realization. The induced matrix-unit
and product topologies on `GeneralLinear n F.Carrier` and `B.Levi F.Carrier`
are definitionally the topologies used by the published functors.

Every representation carrier is in `Type (max uF uV)`. The categories are
the actual complex smooth representation categories
`SmoothRep.{0, uF, max uF uV} ℂ G` from
`Langlands.Representation.Category.Basic`. Smoothness means open vector
stabilizers; no topology is imposed on a representation carrier.
`A.HasFiniteLength` means
`IsFiniteLength ℂ[G] A.representation.asModule`, finite composition length over
the group algebra.

The groups and their class maps are imported from
[`Smooth.FiniteLengthGrothendieck`](../Smooth/FiniteLengthGrothendieck.md):

| Actual group | Exact Grothendieck group | Canonical class |
| --- | --- | --- |
| `GeneralLinear n F.Carrier` | `GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier` | `GeneralLinear.finiteLengthClass n F.Carrier A hA` |
| `B.Levi F.Carrier` | `B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier` | `B.finiteLengthClass F.Carrier A hA` |

These are the integral free modules on genuine isomorphism classes of
finite-length smooth objects, quotiented by the relations from all actual
short exact sequences. Nonsplit sequences are included. Finite length here
does not mean finite complex dimension. The product Levi consists of actual
families of invertible block matrices; its representations are arbitrary
smooth representations of that product.

## The two quantified assertions

`NormalizedInductionGrothendieckStatement.{uF, uV} F T` says that for every
`n : ℕ` and `B : GeneralLinear.BlockShape n` there exists a unique

```lean
i : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
  GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier
```

with the following property. For every actual
`A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)` and every
`hA : A.HasFiniteLength`, there exists a proof

```lean
hOut : ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A).HasFiniteLength
```

such that

```lean
i (B.finiteLengthClass F.Carrier A hA) =
  GeneralLinear.finiteLengthClass n F.Carrier
    ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A) hOut
```

`NormalizedJacquetGrothendieckStatement.{uF, uV} F T` says that for every
`n : ℕ` and `B : GeneralLinear.BlockShape n` there exists a unique

```lean
r : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
  B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier
```

such that for every actual
`A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)` and every
`hA : A.HasFiniteLength`, there exists a proof

```lean
hOut : ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A).HasFiniteLength
```

satisfying

```lean
r (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
  B.finiteLengthClass F.Carrier
    ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A) hOut
```

In both clauses the nesting is
`∀ n B, ∃! map, ∀ A hA, ∃ hOut, generator_equality`.
Uniqueness is among all integer-linear maps satisfying this entire property,
including the existential output-length witness for each input. It does not
fix a chosen family of witnesses in advance. Proof irrelevance makes the
canonical class independent of either finite-length proof, so different
witnesses do not change the asserted values.

`NormalizedParabolicGrothendieckStatement.{uF, uV} F T` is exactly

```lean
NormalizedInductionGrothendieckStatement.{uF, uV} F T ∧
  NormalizedJacquetGrothendieckStatement.{uF, uV} F T
```

Each conjunct quantifies rank and shape internally. The combined declaration
has only `p`, primality, `F` and `T` as outer parameters.

## Actual functors and normalization

The induction output is `Functor.obj` of the existing
`T.normalizedParabolicInductionFunctor` from
[`Induction.Parabolic`](../Induction/Parabolic.md). For the standard upper
block parabolic `P`, its inducing functions satisfy

`f(p g) = δ_P(m(p))^(1/2) • σ(m(p)) (f g)`,

where `m = B.leviProjection F.Carrier`. The group acts by right translation,
`(g · f)(x) = f(x g)`. This is smooth induction with the positive half of the
explicit block modulus `T.leviModulus B`, as expressed by
`T.normalizedParabolicInduced_covariant` and `B.normalizedInducedOf_apply`.

The Jacquet output is `Functor.obj` of the existing
`T.normalizedJacquetFunctor` from
[`Jacquet.Parabolic`](../Jacquet/Parabolic.md). It is the actual quotient by
upper unipotent coinvariant relations, with Levi action

`m · [v] = δ_P(m)^(-1/2) • [ρ(B.leviEmbedding F.Carrier m) v]`.

The formulas are `T.normalizedJacquet_mk` and
`T.normalizedJacquet_mk_eq_inv_halfModulus`. The scalar is the inverse of the
induction half-modulus. The statements therefore use the published upper
parabolic functors directly. No ordinary contragredient or opposite-parabolic
construction intervenes.

## All ranks and independent universes

Every `n : ℕ` and every block shape is included, with no positivity
hypothesis on rank. In particular the statement includes rank zero and its
empty block shape, whose Levi is an empty product, as well as zero
representations in every category. It assumes no admissibility,
irreducibility, central character, tensor factorization or finite dimension.
There are no finite-length-preservation or exactness hypotheses, or
theorem-bearing parameters supplying those conclusions. The existential
`hOut` is part of each conclusion.

The field level `uF` and carrier parameter `uV` remain independent.
Both functors are explicitly applied at `.{uF, max uF uV}`. Induction's
output level is `max uF (max uF uV)`, definitionally `max uF uV`, so the
actual output is an object of the category used by the target class map.
Jacquet retains this saturated level. The specialized Grothendieck-group
universe argument order is `.{uV, uF}`; the groups themselves lie in
`Type (max (uF + 1) (uV + 1))`. No resizing, choice of a smaller
representative, or comparison between groups at different carrier levels
is used.

## Internal derived provenance and proof boundary

This is an internal derived interface for the published exact Grothendieck
presentation. Its precise all-rank formulation, existential witnesses and
universe choices are not attributed verbatim to literature. The referenced
Library pairs supply the definitions and normalization; this module adds no
literature theorem assertion. The broader project source boundary is recorded
in `notes/henniart/aubert-duality-route.md`.

The expected route of a proof uses
`SmoothRep.FiniteLengthGrothendieckGroup.map Φ hl hx` and
`map_ofRepresentation` from
[`Smooth.FiniteLengthGrothendieckFunctor`](../Smooth/FiniteLengthGrothendieckFunctor.md).
With actual finite-length preservation, the separately published
`Parabolic.normalizedInductionExactness` and
`Parabolic.normalizedJacquetExactness` are the intended exactness inputs.
The generic construction then supplies the maps and generator equalities;
`SmoothRep.FiniteLengthGrothendieckGroup.hom_ext_object` supplies uniqueness,
with proof irrelevance reconciling output witnesses. The universal-property
theorem `existsUnique_lift_iff` is also available in the imported group module.
This is an expected route, not a proof or evidence of either assertion.
The generic conditional map alone does not prove the unconditional clauses.
The proof of the combined declaration is
`Langlands.Parabolic.normalizedParabolicGrothendieck`, in
[`Parabolic.FiniteLengthGrothendieckProof`](FiniteLengthGrothendieckProof.md).

Actual all-smooth finite-length preservation is
`Langlands.Parabolic.normalizedParabolicFiniteLength`, in
`Parabolic.FiniteLengthFunctorProof`. The positive-rank admissible
product-induction and Jacquet finite-length results are separate.
This statement does not implement their proofs.

No irreducible-basis theorem, alternating operator, involutivity, Aubert
irreducibility, segment classification, or map construction is asserted or
proved here.

## Actual import audit

The direct imports are exactly `Induction.Parabolic`, `Jacquet.Parabolic`
and `Smooth.FiniteLengthGrothendieck` under
`Langlands.Representation`. The generic functor-map module, finite-length
preservation statements and proofs, and exactness proof modules are not imported.

Recursive inspection of actual import lines at Library base
`333fb3981b648b8ba9f29c1123c27ef3d8626c90` gives these 31 project dependencies,
grouped by prefix:

| Prefix | Module suffixes |
| --- | --- |
| `Langlands.Group.GL` | `Basic`, `BlockModulus`, `Blocks`, `NormalizedCharacter`, `Padic`, `PadicBlocks` |
| `Langlands.LocalField` | `Canonical`, `Definitions`, `Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`, `Topology` |
| `Langlands.Representation.Category` | `Basic` |
| `Langlands.Representation.Induction` | `Definitions`, `Parabolic` |
| `Langlands.Representation.Jacquet` | `Coinvariants`, `Normalized`, `Parabolic`, `PositiveCharacter`, `SmoothTwist` |
| `Langlands.Representation.Smooth` | `Definitions`, `FiniteLengthGrothendieck`, `SmoothPart.Definitions`, `Transfer.PullbackProof`, `Transfer.PullbackStatement`, `Transfer.SubquotientProof`, `Transfer.SubquotientStatement` |
| `Langlands.Representation.Twist` | `Definitions`, `SmoothProof`, `SmoothStatement` |
| `Langlands.VirtualRepresentation` | `Integral` |

All 31 existing Lean/Markdown pairs were checked byte for byte against that
Library base and are unchanged. The inherited infrastructure proofs concern
local-field normalization, smooth transfer and twisting. The closure contains
no project classification or exhaustion module. Consequently none of the
excluded conclusions or their proofs and transitive proof
dependencies supplies an input: analytic segment classification;
special-head multisegment exhaustion; ordered strong-head existence;
quotient coverage; tempered block uniqueness;
`SquareIntegrableLanglandsClassification`; square-integrable exhaustion;
and regular exhaustion.

## Development validation

A check with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`
compiled the complete statement module and inspected the exact combined
declaration successfully, with zero errors and warnings. Inspection reports kind `definition`,
level parameters `["uF", "uV"]`, `statement_returns_prop: true`, and only
`propext`, `Classical.choice` and `Quot.sound` in its assumptions.
The entire formulas elaborate at these independent universes, including the
induction output class at its saturated level. Compilation checks the
well-formed propositions, not their truth.
