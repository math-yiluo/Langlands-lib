# Reducing the irreducibility of `E#` to the class formula and Theorem 1.7

Module `Langlands.Representation.Aubert.General.SharpIrreducibleReduction`.

Authors: Worker 4220 and Worker 36, for Task 4220
(`44d0ed8c-18a6-44f8-8836-dc351694e9d9`). The proof development comes from the
shared draft of this task (revision 2, by Worker 4220, which builds on
revision 1 by a previous instance's executor of the same task). Worker 36
added the reduction statement `RationalSharpIrreducibleReductionStatement` and
its proof, and this documentation.

This module states and proves one implication between published propositions.
It does **not** prove `RationalSharpIrreducibleStatement`. Its main theorem is
conditional on five published propositions that are not yet proved; they are
listed below.

## The statement

`Langlands.Aubert.General.RationalPointFamily.RationalSharpIrreducibleReductionStatement.{u, v} : Prop`
is the implication

```lean
DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
  DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
    RationalInductionCompatibilityStatement.{u, v} →
      RationalInvolutivityStatement.{u, v} →
        RationalSharpClassFormulaStatement.{u, v} →
          RationalSharpIrreducibleStatement.{u, v}
```

Every proposition in it is a published Library statement, used unchanged:

- `Langlands.Aubert.General.DynamicInductionFiniteLengthStatement` and
  `DynamicJacquetFiniteLengthStatement`
  (`Aubert/General/PrerequisiteStatements`): the actual normalized induction
  and Jacquet functors of every dynamic parabolic `P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)`
  preserve finite length (Renard VI.6.2 and VI.6.4). They are taken at carrier
  universe `max (u + 1) v`. That is the carrier universe of the
  representations in the conclusion.
- `RationalPointFamily.RationalInductionCompatibilityStatement`
  (`Aubert/General/RationalInductionTarget`): `D_G ∘ i_J = i_J ∘ D_{L_J}` on
  the exact finite-length Grothendieck groups (Aubert, Théorème 1.7 (2)).
- `RationalPointFamily.RationalInvolutivityStatement`
  (`Aubert/General/RationalInvolutivityTarget`): `D_G ∘ D_G = id` (Aubert,
  Théorème 1.7 (3)).
- `RationalPointFamily.RationalSharpClassFormulaStatement`
  (`Aubert/General/RationalSharpConsequenceTargets`): the signed class formula
  `D_G [E] = (-1)^{|I|} [E#]` (Aubert, Corollaire 3.9 (a), extended to
  finite-length `E` in `Alg({I})`).
- The conclusion `RationalPointFamily.RationalSharpIrreducibleStatement`
  (same module) is Aubert's Corollaire 3.9 (b): for every `E` in the actual
  cuspidal series of `L_I`, the actual terminal cokernel `E#` is irreducible,
  hence nonzero.

The universes `u` (field and group) and `v` (representation carriers) stay
independent.

Provenance: this is a derived statement. Aubert's proof of Corollaire 3.9 (b)
(1995, printed p. 2189) uses assertion (a) and assertions (2) and (4) of
Théorème 1.7. The Lean argument below also uses involutivity (Théorème 1.7
(3)) to show that `E#` is nonzero, and it needs finite length of `i_J`, `r_J`
and `E#` to form classes in the exact finite-length Grothendieck group. Finite
length of `E#` is derived inside the proof from the two dynamic finite-length
statements (see the abstract closer below), so the published
`RationalSharpFiniteLengthStatement` is not an input. The statement records
exactly the published propositions that the implemented proof consumes.

`rationalSharpIrreducibleReduction` proves the statement by applying
`rationalSharpIrreducibleStatement_of_inputs`, described below.

## Source

Aubert, *Dualité dans le groupe de Grothendieck de la catégorie des
représentations lisses de longueur finie d'un groupe réductif p-adique*
(1995), Corollaire 3.9 (b) and its proof, printed p. 2189. Aubert's claim is
that `E#` is irreducible for every `E` in the cuspidal series `𝔈(I)`. The
proof is a length count. On `Alg({I})`, the operator `(-1)^{|I|} D_G` acts as
`E ↦ E#` on classes. This operator is involutive, and it fixes `[i_I σ]` for
an irreducible Levi-cuspidal `σ`. The Lean route below follows this argument.
It uses the integer-valued composition length on the exact finite-length
Grothendieck group in place of positivity of classes.

## Generic length lemmas (`Langlands.SmoothRep.FiniteLengthGrothendieckGroup`)

- `exists_compositionLength_ofRepresentation`: for an actual finite-length
  `A`, `compositionLength [A]` is the natural number `repLength A`. The
  proof uses `chosenSeries`, `repLength_eq_of_hasSimpleFactors` and
  `compositionLength_of_series`.
- `compositionLength_ofRepresentation_eq_one_iff`: `compositionLength [A] = 1`
  exactly when `A` is irreducible, by `repLength_eq_one_iff`.
- `one_le_compositionLength_of_ne_zero`: a nonzero actual class has length
  at least one. Length zero forces a subsingleton carrier
  (`repLength_eq_zero_iff`), whose class is zero
  (`ofRepresentation_eq_zero_of_subsingleton`).
- `compositionLength_le_of_irreducible`: let `C` be a class of complex smooth
  representations closed under actual subquotients. Let `F` be a ℤ-linear
  endomorphism of the finite-length Grothendieck group that sends the class
  of every irreducible member of `C` to an element of length at least one.
  Then `compositionLength [A] ≤ compositionLength (F [A])` for every
  finite-length `A` in `C`. The proof writes `[A]` as the sum of the classes
  of the graded pieces of `chosenSeries` (`realize_seriesClass`,
  `realizeIrreducibles_generator_irreducibleIsoClass`). Each graded piece is
  an actual subquotient of `A`, so it lies in `C`. The bound then holds term
  by term.

## Levi eigenvalue and cuspidal induction (`Langlands.Aubert.General`)

- The published `CuspidalEmbedding.leviIndex_univ` from
  `RationalLeviCuspidalJacquet` supplies `leviIndex J Finset.univ = J`.
- `leviAlternatingOperator_cuspidal`: this is Theorem 1.7 (4) for the Levi
  operator of a standard Levi `M J`. If `σ` is an actual irreducible
  `IsLeviCuspidal` representation of `M J`, then
  `leviAlternatingOperator [σ] = (-1)^{|J|} [σ]`. The proof expands the
  operator with `alternatingOperator_ofRepresentation`. Every proper index
  `I` has a subsingleton Jacquet module by cuspidality, so its term vanishes
  (`inductionK0_ofRepresentation`). For the full index, `P ∩ M J = M J` and
  `U ∩ M J = ⊥`, which are derived from the semidirect decomposition. The
  modulus is then trivial, and `inductionJacquetClass_of_top_bot` returns
  `[σ]`.
- `alternatingOperator_cuspidalInduction`: for an irreducible Levi-cuspidal
  `σ` of `M I`, `D_G [i_I σ] = (-1)^{|I|} [i_I σ]`. This uses an
  `InductionCompatibilityStatement` (Theorem 1.7 (2), `D_G ∘ i_I =
  i_I ∘ D_{M_I}`) together with `leviAlternatingOperator_cuspidal`.

## Abstract closer

`sharpIrreducibleTarget_of_classFormula` proves `SharpIrreducibleTarget` for
an abstract standard family. It takes one finite-length proof `hfl`
together with the following inputs:

- `hinv`: involutivity of `D_G`;
- `hrefl`: reflexivity of the association at the identity;
- `hCF`: `SharpClassFormulaTarget`, i.e. `D_G [Y] = (-1)^{|I|} [Y#]` for
  finite-length `Y` in `Alg({I})` with finite-length `Y#`;
- `hcusp`: the identity `D_G [i_I σ] = (-1)^{|I|} [i_I σ]`.

Finite length of `Y#` is not an input. The closer derives
`SharpFiniteLengthTarget` from `hfl` with the published
`sharpFiniteLengthTarget_of_inductionJacquet` (module
`Langlands.Representation.Aubert.General.SharpFiniteLength`). Its premise, that
each induction-Jacquet composite preserves finite length, is supplied by the
published `inductionJacquet_hasFiniteLength` applied to `hfl`.

The proof sets `F = (-1)^{|I|} D_G`, so `F ∘ F = id`. By `hCF` and this
derived finite length,
`F [Y] = [Y#]` for every finite-length `Y` in `Alg({I})`. If `τ` is
irreducible in `Alg({I})`, then `[τ#] ≠ 0`: otherwise
`[τ] = F (F [τ]) = 0`, and `[τ]` has length one. So `F` satisfies the
hypothesis of `compositionLength_le_of_irreducible` for the subquotient-closed
class `IsInSupportCategory … I` (`IsInSupportCategory.of_isSubquotient`).

Take `E` in the cuspidal series, with `E ≅ S/T` for `T ≤ S ≤ X = i_I σ`.
`X` lies in `Alg({I})` by `isInSupportCategory_cuspidalInduction`. Two
actual short exact sequences (`subtype_mkQ_isShortExact`,
`ofRepresentation_shortExact`) give `[X] = [T] + [E] + [X/S]`. Since
`F [X] = [X]`, applying the length and the bound to `T` and `X/S` gives
`compositionLength (F [E]) ≤ 1`. Also `F [E] = [E#]` has length at least
one. Hence `compositionLength [E#] = 1`, and `E#` is irreducible, which
includes nonzero.

## Conditional rational theorem

`RationalPointFamily.rationalSharpIrreducibleStatement_of_inputs` derives
`RationalSharpIrreducibleStatement.{u, v}` from exactly these inputs:

| Input | Owner task |
| --- | --- |
| `DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}` | 174d2de0-fa21-41b4-b091-f1b86481790b |
| `DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}` | 73e60be8-481a-4cea-b464-eed3bd89be7f |
| `RationalInductionCompatibilityStatement.{u, v}` | 475f7a39-11ad-4748-87b3-cfaef16a59cb |
| `RationalInvolutivityStatement.{u, v}` | 2f01b264-fb0e-4029-901c-009044feaa97 |
| `RationalSharpClassFormulaStatement.{u, v}` | 13e2abdc-2be7-4191-b74b-9eae99a56fcc |

Published proofs supply the remaining data:

- `rationalWeylComparison` supplies `hN` and `hZ`, which give the
  association `rootAssociation` and its identity law `rootAssociation_one`.
- `rationalLeviFiniteLengthStatement` supplies finite length inside the
  standard Levis.
- `isClosed_standard_parabolic`, `continuous_standard_projection` and
  `levi_isClosed` supply closedness and continuity.
- `standard_induction_preservesFiniteLength` and
  `standard_jacquet_preservesFiniteLength` turn the dynamic statements into
  the standard-family preservation premises, which assemble into
  `standardParabolicFiniteLength`.
- `inductionCompatibilityStatement_of_rational` turns the rational
  compatibility into the abstract `InductionCompatibilityStatement`.
- `sharpFiniteLengthTarget_of_inductionJacquet` and
  `inductionJacquet_hasFiniteLength` give finite length of `E#` inside the
  closer. So `RationalSharpFiniteLengthStatement` (task
  0da1c37e-a39a-42e1-b90d-135db6c6e5c3) is not needed as an input.

The theorem keeps every binder of the target, at independent universes `u`
and `v`. It adds no premise inside the proposition, but it has the five
theorem-valued parameters above. Once proofs of those five are published,
applying it (or `rationalSharpIrreducibleReduction`) to them proves the
target. Until then this module does not prove the target.

## Dependency ledger

No Langlands classification, character independence, geometric-lemma or
adjointness theorem is invoked in this module. The published helpers it
applies are `rationalWeylComparison` (`RationalWeylComparisonProof`),
`rootAssociation_one` (`RootAssociationLaws`),
`rationalLeviFiniteLengthStatement` (`RationalLeviFiniteLengthProof`), and
`sharpFiniteLengthTarget_of_inductionJacquet` with
`inductionJacquet_hasFiniteLength` (`SharpFiniteLength`). Their own Markdown
records that they invoke none of these theorems. The
Levi-finite-length chain uses only the explicit evaluation and covariance
formulas of `FirstAdjointness`, not an adjunction theorem. The five inputs
enter only as hypotheses of the implication. Whatever their eventual proofs
use (for example the geometric lemma behind induction compatibility and
involutivity) is recorded with those proofs by their owner tasks. Aubert's
Proposition 3.2 and its original application are not used.
