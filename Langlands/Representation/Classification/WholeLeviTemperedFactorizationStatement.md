# Tempered block factorization of whole-Levi representations

Author: Worker 219. The target, its exact input predicate and its dependency
boundary were specified by task `45fb735a-dbfb-4b2f-9fea-5a2402894488` for the
whole-Levi recovery proof task `707cfa4e-a9aa-4748-8f7a-0074d8ee5a3d`
(Worker 545).

`Langlands.GLWholeLeviTemperedFactorizationStatement.{uF,uV}` is a closed
proposition definition. It is a derived theorem target. This pair does not
prove the factorization.

## Exact statement

Fix a prime `p`, an actual finite extension `F : PadicField.{uF} p`, supplied
topological data `T : F.TopologicalData`, a positive integer `n`, and an
arbitrary ordered block shape `B : GeneralLinear.BlockShape n`. Install
`T.topology`. Let

```text
σ : Rep.{uV} ℂ (B.Levi F.Carrier)
```

be an arbitrary representation of the actual product Levi
`B.Levi F.Carrier = ∀ i : Fin B.length, GL_(B.size i)(F)`. The two hypotheses are

1. `Representation.IsIrreducible σ.ρ`: Mathlib's algebraic irreducibility,
   which excludes the zero representation;
2. `RelativeRegularComparison.IsLeviTempered T B σ`: the existing whole-Levi
   analytic predicate. With `T.topology` and `T.leviTopologicalGroup B`
   installed, and `Z = B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)`
   the actual quotient by the full Levi center, it requires
   `IsTemperedModCenter σ.ρ μ` for every `[MeasurableSpace Z] [BorelSpace Z]`
   and every Haar measure `μ` on `Z`.

The conclusion is that there exists a family

```text
A : ∀ i : Fin B.length,
  SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)
```

such that

- `∀ i, Representation.IsIrreducible (A i).representation`;
- `∀ i, (A i).IsAdmissible`;
- `∀ i, T.IsTempered (A i).representation`;
- `Nonempty (σ.ρ.Equiv (B.blockTensor (fun i => (A i).representation)))`.

The four conclusions are conjoined in this order. The equivalence is an actual
`Representation.Equiv` from `σ.ρ` to the constructed external tensor; it is
asserted by `Nonempty`, and no particular choice or uniqueness of the factors
is claimed.

## Constructions and conventions

All constructions are existing Library ones, used by Lean name.

- `B.Levi F.Carrier` is the abstract product of the groups
  `GeneralLinear (B.size i) F.Carrier`, with the product of the units
  topologies coming from `T.topology`. This is the topology `T.leviTopology B`
  used inside `IsLeviTempered`. No block-diagonal embedding into `GL_n` enters.
- `SmoothRep.{0,uF,uV}` is the full subcategory of Mathlib's `Rep` cut out by
  smoothness; its carriers lie in `Type uV`. `(A i).representation` is the
  underlying actual action.
- `SmoothRep.IsAdmissible` is the published `Langlands.IsAdmissible`:
  smoothness together with finite-dimensional fixed spaces for every open
  subgroup.
- `T.IsTempered` is the published factor predicate in
  `Classification/Tempered`: for the canonical Borel measurable space on the
  actual central quotient of `GL_(B.size i)(F)`, every Haar measure `μ`
  satisfies `IsTemperedModCenter (A i).representation μ`. That predicate is
  admissibility together with the existence of a unitary central character for
  which every descended absolute smooth matrix coefficient lies in
  `L^(2+ε)` for every `ε > 0`.
- `B.blockTensor` is `FiniteTensor.external`: the `PiTensorProduct ℂ` of the
  factor carriers, on which a tuple `m` of block matrices acts on pure tensors
  by `⨂ᵢ vᵢ ↦ ⨂ᵢ (A i)(m i)(vᵢ)`.

## Universes and scope

The field universe `uF` and the carrier universe `uV` are independent. The
factor carriers lie in the same universe `uV` as the input carrier. There is no
universe equality, domination, `max` enlargement or other replacement
universe. Positivity of `n` forces `B.length ≥ 1`, because block sizes are
positive; the one-block case `B.length = 1` is included.

The only hypotheses on `σ` are irreducibility and `IsLeviTempered`. There is
no smoothness, admissibility, unitarity, central-character, cuspidal-support,
countability, classification-data or factorization hypothesis on the input.
Smoothness and admissibility of `σ` are consequences: the published
`RelativeRegularComparison.IsLeviTempered.isAdmissible` derives
`IsAdmissible σ.ρ` from `IsLeviTempered T B σ`, using the existence of a Borel
Haar measure on the actual central quotient, and admissibility contains
smoothness. The whole-Levi predicate is exactly the one in the consumer target
`Langlands.GLWholeLeviLanglandsRecoveryStatement`; it is not a condition
defined in terms of already supplied factors.

Admissibility of the factors is an additional conclusion. It is included
because the factor-level analytic comparison `GLBlockTensorTemperedStatement`
assumes irreducible admissible factors, and the algebraic factorization
supplies admissibility directly. Temperedness of each factor also implies its
admissibility (`IsTemperedModCenter` contains admissibility as its first
conjunct, and a Haar measure exists), but stating it separately avoids that
Haar-existence argument at each use.

## Provenance: a derived interface

This proposition is a derived interface. It is not an assertion that an
external source contains this exact dependent-type and universe formulation.
It combines three ingredients, each of which already has a published Library
interface.

1. **Algebraic admissible factorization.** The published theorem
   `Langlands.CuspidalSupport.padicLeviAdmissibleFactorization.{uF,uV}` in
   `Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` proves
   `PadicLeviAdmissibleFactorizationStatement`: an irreducible admissible
   smooth representation of `B.Levi F.Carrier` is equivalent to the external
   tensor of irreducible admissible factors in the same carrier universe. Its
   Markdown records the source correspondence: finite iteration of Flath's
   two-factor Theorem 1 (1.2) (`flath-1979-tensor-products`) along the
   product decomposition of Bernstein–Zelevinsky 1977 §2.2
   (`bernstein-zelevinsky-1977-induced-i`). It supplies no analytic
   information about the factors.
2. **Analytic transport.** The published
   `PadicField.TopologicalData.isLeviTempered_iff_of_equiv` in
   `Representation.Induction.InnerLeviTransport` transports `IsLeviTempered`
   across an actual representation equivalence between carriers in independent
   universes. Applied to the equivalence of step 1, it makes the external
   tensor itself whole-Levi tempered.
3. **Analytic tensor reflection.** The published proposition
   `Langlands.GLBlockTensorTemperedStatement.{uF,uV}` in
   `Representation.Classification.BlockTensorAnalyticStatement` states that,
   for irreducible admissible block factors, factorwise `T.IsTempered` is
   equivalent to temperedness of their external tensor for every Borel Haar
   measure on the actual Levi central quotient. Its reverse direction turns
   the conclusion of step 2 into `T.IsTempered` for every factor. Its Markdown
   records the analytic conventions (Kudla 1994 §2.2, Casselman 1995 §2.5) and
   explains that the finite-product comparison is itself derived content.

The intended proof route is: bundle `σ` as a smooth representation using the
smoothness obtained from `IsLeviTempered.isAdmissible`; apply step 1; transport
`IsLeviTempered` to the tensor by step 2; and apply the reverse direction of
step 3 to the irreducible admissible factors. This route uses no parameter
uniqueness, Langlands recovery, tempered classification or semistandard
conjugacy.

## The open analytic input

Steps 1 and 2 are closed published theorems. Step 3 is only a published
proposition: its exact proof task `ef5468e7-d124-4931-b938-d4757c2188c8`
(Worker 403) had not been completed when this pair was written. Only its
reverse direction, from temperedness of the tensor to temperedness of each
factor, is needed here. That direction still requires, among the obligations
listed in `BlockTensorAnalyticStatement.md`, the identification of the Levi
center and its central quotient with the products of the factor centers and
quotients, restriction of the tensor's unitary central character to each
factor, the description of smooth functionals and coefficients of the tensor,
the nonzero-factor reflection argument for `L^(2+ε)` integrability, and the
comparison over all Borel Haar realizations. A proof of the present target
must use a proved and published closing theorem of
`GLBlockTensorTemperedStatement` (or prove that analytic content itself); it
must not take that proposition, or the present one, as a hypothesis.

The implementer checked privately, outside this submission, that the route
above type-checks as a conditional reduction from `GLBlockTensorTemperedStatement.{uF,uV}`
to this proposition, in the same universes, using only the three published
interfaces above. That reduction is not part of this pair, is not a proof of
the target, and confers no evidence about the open analytic input.

## Dependencies

The imports are `Representation.Classification.RelativeRegularComparisonStatement`
(the predicate `IsLeviTempered`), `Representation.Classification.Tempered`
(`T.IsTempered`) and `Representation.Induction.BlockFactors`
(`BlockShape.blockTensor` and, transitively, `SmoothRep`). No imported file is
changed. Neither this file nor its import closure depends on
`SemistandardLanglandsStatement` or on any downstream recovery or
classification conclusion. The environment is Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Compilation and declaration inspection
show only that this is a well-formed closed proposition with level parameters
`uF` and `uV`; independent semantic review and publication are required, and
a separate proof of this exact target is a later task.
