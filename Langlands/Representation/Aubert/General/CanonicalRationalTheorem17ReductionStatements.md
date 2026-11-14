# Reductions of the canonical targets of Théorème 1.7 and Corollaire 1.10

Module `Langlands.Representation.Aubert.General.CanonicalRationalTheorem17ReductionStatements`.
Authors: Worker 29, with Worker 3640, who chose this block (block (v)) for the
general Aubert program (Task 3640) and fixed its five input sets.

The module declares five Prop-valued definitions in
`Langlands.Aubert.General.RationalPointFamily`, each with universe parameters
`u` and `v`. The review entry is
`CanonicalRationalInductionCompatibilityReductionStatement`. Each definition
is a curried implication between whole published propositions. None is proved
here. None proves its conclusion or discharges an input, and none adds a
premise to its conclusion. Each conclusion is the unchanged canonical target
of `CanonicalRationalTheorem17Targets`, and each input is the unchanged
published proposition.

The conclusions are canonical targets. They concern the canonical actual
operator `D = canonicalRationalAlternatingOperator`, Aubert's
`Σ_I (-1)^|I| i_I ∘ r_I` of Définition 1.5, on the exact finite-length
Grothendieck group of `G(k)` with its canonical topology `pointTopology`, as
described in `CanonicalRationalTheorem17Targets.md`. Each conclusion keeps
its own binders `hiFl : DynamicInductionFiniteLengthStatement` and
`hrFl : DynamicJacquetFiniteLengthStatement` at `.{u, max (u + 1) v}`.
The contragredient target also keeps its per-group hypothesis `hc`. These
binders stay inside the conclusions. They are not inputs of the reductions.

## The inputs

- `RationalInducedK0WeylConjugacyStatement.{u, v}`
  (`RationalInducedWeylConjugacyTarget`), written *Weyl* below. For every
  actual normalizer element `n` of the rational torus points with
  `x ∈ L_J ↔ n⁻¹ x n ∈ L_I`, `i_J ∘ Ad(n) = i_I` holds as an equality of
  integer-linear maps of exact finite-length Grothendieck groups. This is
  Aubert (1995), identity (1.2), printed p. 2181 / PDF p. 3, in the form of
  Ban–Jantzen 2016, Proposition 4.1 (3), as recorded in
  `CanonicalRationalTheorem17Targets.md`. The proposition keeps its own
  structural and finite-length premises inside its binders, as published.
- `RationalInducedClassWeylConjugacyStatement.{u, v}` (same module),
  written *ClassWeyl* below. It is the same identity stated on the classes
  of actual normalized induced representations: for the same `n` and every
  finite-length `σ` of `L_I`, `[i_J(Ad(n) σ)] = [i_I σ]`. By the published
  theorems recorded in the dependency matrix, it is equivalent to *Weyl*. It
  is the form that the published contragredient assembly uses.
- `RationalPointsFiniteLengthAdmissibleStatement` and
  `DynamicLeviFiniteLengthAdmissibleStatement` (`PrerequisiteStatements`),
  written *AdmG* and *AdmM* below. Every finite-length smooth complex
  representation of `G(F)`, and of every dynamic Levi `Z(χ)(F)` with the
  subspace topology, is admissible. This is the direction "finite length ⇒
  admissible" of Renard, Théorème VI.6.3 (Howe). The statement is on printed
  p. 178 / PDF p. 184 and the proof of this direction on printed p. 179 /
  PDF p. 185. Both are always taken at `.{u, max (u + 1) v}`.
- `RationalRankOneSelfAssociationStatement.{u, v}` (`RationalCorollaryTargets`),
  written *SelfAssoc* below. Let `J` be a maximal standard subset and `σ` an
  irreducible Levi-cuspidal finite-length representation of `L_J` with `i_J σ`
  reducible. Then `associatedSubset J = J`, and every actual normalizer lift
  of the longest representative `longestRep J` normalizes `L_J`. This holds
  for every actual Coxeter system satisfying the published comparison
  premises. It is the self-association step of Aubert's proof of
  Corollaire 1.10 (b), printed p. 2183 / PDF p. 5, which cites Casselman
  §7.1. It is kept as an explicit representation-theoretic input.
- `CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  (`RationalWholeCuspidalDecompositionStatement`), written *Whole* below. It
  is the two-factor decomposition of the whole smooth category in Renard,
  Théorème VI.3.5, printed p. 146 / PDF p. 152. Every smooth representation is
  the coproduct of a part all of whose subquotients are cuspidal and a part
  none of whose nonzero subquotients is cuspidal. It is always taken at
  `.{u, max (u + 1) v}`.

In each input, `.{u, max (u + 1) v}` means field universe `u` and carrier
universe `max (u + 1) v`. This is the carrier universe of every conclusion at
`u, v`, so no universe is lowered or raised.

In the bottleneck list of `notes/aubert/general-program-dependency-matrix.md`,
*Weyl*, *ClassWeyl*, *AdmG* and *AdmM* belong to item 3, *SelfAssoc* reduces
to item 5 (Renard VII.1.3), and *Whole* is item 1. The existing rational
targets of Théorème 1.7 and Corollaire 1.10, the rank-one Jacquet-module
target and cuspidal Jacquet-factor extraction are not inputs. The checked
proofs derive them, as described under *Provenance and intended proofs*.

## `CanonicalRationalInductionCompatibilityReductionStatement`

```
RationalInducedK0WeylConjugacyStatement.{u, v} →
  CanonicalRationalInductionCompatibilityStatement.{u, v}
```

The conclusion is the first equation of Aubert (1995), Théorème 1.7 (2),
printed p. 2181 / PDF p. 3: `D_G ∘ i_J = i_J ∘ D_{L_J}` for every subset `J`
of the actual simple roots, as the equality `D.comp ind = ind.comp DL` of
the canonical target. Aubert proves it from (1.1), (1.3) and (1.2), arriving
at (1.8), printed p. 2182 / PDF p. 4. *Weyl* is the only input.

## `CanonicalRationalInvolutivityReductionStatement`

```
RationalInducedK0WeylConjugacyStatement.{u, v} →
  CanonicalRationalInvolutivityStatement.{u, v}
```

The conclusion is Théorème 1.7 (3), printed p. 2181 / PDF p. 3:
`D.comp D = LinearMap.id` on the whole exact Grothendieck group. Aubert
derives it from 1.7 (2), printed p. 2183 / PDF p. 5. *Weyl* is the only
input.

## `CanonicalRationalCorollary110aReductionStatement`

```
RationalInducedK0WeylConjugacyStatement.{u, v} →
  CanonicalRationalCorollary110aStatement.{u, v}
```

The conclusion is Corollaire 1.10 (a), printed p. 2183 / PDF p. 5, for the
canonical families. For every `J` and every irreducible Levi-cuspidal
finite-length `σ` of `L_J` with `i_J σ` irreducible,
`D_G [i_J σ] = (-1)^|J| [i_J σ]`. Aubert derives it from Théorème 1.7.
*Weyl* is the only input.

## `CanonicalRationalContragredientCommutationReductionStatement`

```
RationalInducedClassWeylConjugacyStatement.{u, v} →
  RationalPointsFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
    DynamicLeviFiniteLengthAdmissibleStatement.{u, max (u + 1) v} →
      CanonicalRationalContragredientCommutationStatement.{u, v}
```

The conclusion is Théorème 1.7 (1), printed p. 2181 / PDF p. 3:
`D.comp c = c.comp D`, where `c` is the actual smooth contragredient on
exact K0. It is stated under the canonical target's own per-group hypothesis
`hc` that contragredients of finite-length representations of this `G(k)`
have finite length. Aubert derives 1.7 (1) from (1.4), a reformulation of
Casselman's Corollary 4.2.5. The formal route instead compares the
contragredients of the induced and Jacquet terms through the actual natural
induction and Jacquet duality isomorphisms on finite-length objects, which
use admissibility, together with *ClassWeyl* at the longest lifts. The inputs
are *ClassWeyl*, *AdmG* and *AdmM*.

## `CanonicalRationalCorollary110bReductionStatement`

```
RationalRankOneSelfAssociationStatement.{u, v} →
  CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalInducedK0WeylConjugacyStatement.{u, v} →
      CanonicalRationalCorollary110bStatement.{u, v}
```

The conclusion is Corollaire 1.10 (b), printed p. 2183 / PDF p. 5, for the
canonical families. Let `J = S - {α}` be maximal standard, and let `σ` be
irreducible and Levi-cuspidal with `i_J σ` reducible. Then there are
irreducible `ρplus` and `ρminus` that are the two constituents of `i_J σ`
(in an actual short exact sequence, in either order), with
`(-1)^|J| D[ρplus] = [ρminus]` and `(-1)^|J| D[ρminus] = [ρplus]`. The
inputs are *SelfAssoc*, *Whole* and *Weyl*. Aubert's proof uses Casselman
§7.1 for the length and the Jacquet modules of the two constituents, and
(1.2).

## Scope

All inputs and conclusions are the published propositions themselves,
quantified over the same actual setting:

- every nonarchimedean local field, including positive characteristic;
- every connected reductive group, with its actual maximal split torus,
  generic cocharacter and actual simple relative roots, including the empty
  set (where Corollaire 1.10 (b) is vacuous);
- the canonical `pointTopology` on rational points in the conclusions,
  *Weyl*, *ClassWeyl* and *SelfAssoc*, and `rationalPointTopology` in *AdmG*,
  *AdmM* and *Whole*, as published;
- field universe `u` and representation carriers in `max (u + 1) v`, with
  `u` and `v` independent.

No proposition restricts to split, quasisplit or characteristic-zero groups,
or to `GL`. The other three canonical targets of
`CanonicalRationalTheorem17Targets` need no reduction here. Jacquet
compatibility and the cuspidal eigenvalue follow from published proofs of
their rational targets through the bridge. The canonical induced K0 Weyl
conjugacy target follows from *Weyl* by the bridge conjunct alone.

## Provenance and intended proofs

These are derived, internal statements. They make no new claim from the
literature. Their mathematical content is that of the cited sources through
the published targets, whose own Markdown records the source correspondence.

Each implication has been checked in Lean, against the current Library and
the pending Task 6316 bridge proof named below, with standard axioms only.
No input beyond those listed was needed. The proofs belong to separate
`lean.proof@1` successor tasks. Statement review does not establish them.
The checked routes are as follows.

- Induction compatibility. The published
  `rationalInductionCompatibility_of_expansion_and_inducedWeyl` takes the
  published `rationalGeometricK0Expansion` and *Weyl* and gives
  `RationalInductionCompatibilityStatement`.
- Involutivity. The published
  `rationalInvolutivityStatement_of_inducedK0WeylConjugacy` takes *Weyl*
  and gives `RationalInvolutivityStatement`.
- Corollaire 1.10 (a). The published
  `rationalCorollary110aStatement_of_inducedK0WeylConjugacy` takes *Weyl*
  and gives `RationalCorollary110aStatement`.
- Contragredient commutation. The published
  `rationalContragredientCommutation_of_admissibility_and_inducedWeyl` takes
  *AdmG*, *AdmM* and *ClassWeyl* and gives
  `RationalContragredientCommutationStatement`. Its Coxeter, Levi
  conjugation, opposite-transport and natural-duality inputs are discharged
  there by published proofs.
- Corollaire 1.10 (b). From *Whole*, the published
  `rationalCuspidalExtractionInputs_of_wholeStatement` and
  `rationalCuspidalJacquetFactorExtraction_of_inputs` give cuspidal
  Jacquet-factor extraction. The published
  `rationalRankOneJacquetModules_of_extraction` turns this into the rank-one
  Jacquet-module target. Then the published
  `rationalCorollary110bFromRankOneInputs` takes *SelfAssoc*, the rank-one
  Jacquet modules and *Weyl* and gives `RationalCorollary110bStatement`.

In each case the canonical form comes from the corresponding conjunct of
`canonicalRationalTargetBridges : CanonicalRationalTargetBridgesStatement`.
That is the proof of Task 6316 (`4320e0f3-a054-4148-bc31-69a2529b0d13`),
candidate `ea7d378d-7ab4-4e77-8a90-2379fdee476e`, accepted in review and not
yet in the Library. All five proofs depend on it and on no other pending
work.
