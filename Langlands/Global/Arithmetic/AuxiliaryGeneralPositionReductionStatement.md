# Auxiliary characters to Harris general position

Author: Worker 84.

`Langlands.Global.AuxiliaryGeneralPositionReductionStatement.{u}` states
the derived implication

```lean
AuxiliaryCharacterStatement.{u, u} → HarrisGeneralPositionStatement.{u}
```

It is a proposition definition, with no proof in this module.

## The retained existence premise

`AuxiliaryCharacterStatement` is the existing field-side existence input.
For compatible finite p-adic fields `F` and `M` with `M/F` Galois, it
supplies continuous finite-order characters of any intermediate field
`L`, nontrivial at arbitrarily large canonical depth, whose norm
pullbacks have the exact stabilizer already on norm-one units of `M`.
The characters, norms, Galois actions and unit groups are the actual
Library and Mathlib constructions.

The reduction assumes this entire statement. It does not supply its
witnesses or prove its truth. Its two field universes are specialized
to the same arbitrary universe `u`. This is sufficient for a p-adic
field and the finite normal closure of an extension in the same
algebraic closure. It does not restrict the choice of the universe,
prime, extension degree or intermediate field.

## The conclusion

The conclusion is the unchanged existing `HarrisGeneralPositionStatement`.
It is the conjunction of three local statements:

- `GeneralPositionOfExactStabilizerStatement`: the exact Weil stabilizer
  implies general position, including a cyclic prime-step tower and
  irreducibility of every specified Mackey constituent at every level.
- `ExactStabilizerCharacterStatement`: for every normalized common-closure
  reciprocity family and every conductor threshold, there is a continuous
  finite-order field character meeting that threshold whose associated
  Weil character has the exact stabilizer.
- `GeneralPositionCharacterStatement`: for every such family and threshold,
  there is a finite-order field character meeting the threshold and in
  general position.

The first statement is itself an implication and has no
auxiliary-character existence requirement. The latter two use the
explicit auxiliary premise of this reduction. Their reciprocity family
is supplied and satisfies `NormalizedReciprocity`; its existence is not
asserted. Conductors are the actual `fieldData` multiplicative conductors.
All common-closure fields, Weil subgroups, conjugations and induced
representations remain the original objects.

The reduction covers every prime, including two, and preserves the same
character's finite order, conductor bound and stabilizer or general
position. No odd-prime, degree bound, ramified compatibility or local
Langlands correspondence hypothesis is added.

## Provenance and remaining obligations

Harris 1998, Definition 4.5 and Lemma 4.7 on printed p.201, define general
position and assert the existence of characters of arbitrarily large
conductor with that property. The proof on pp.204–206 first reduces to
the exact stabilizer (4.12), then constructs the characters.
This target is an internal reduction between the existing Library
formulations. It separates the field-side existence problem from the
topology, depth, reciprocity and Mackey comparisons needed by the local
general-position statement. The displayed implication is not asserted
verbatim in the article.

The retained original is Michael Harris, *The local Langlands conjecture
for GL(n) over a p-adic field, n < p*, Invent. Math. 134 (1998), 177–210;
source `harris-1998-local-langlands`, SHA256
`7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.
The cited passages are printed p.201 and pp.204–206 / one-based PDF
pp.25 and 28–30, especially Definition 4.5, Lemma 4.7 and (4.12).

The existence premise, including the characteristic-two issue documented
in `AuxiliaryCharacterStatement.md`, remains a separate proof obligation.
This reduction supplies no global field or Hecke character, weak
automorphic induction, geometric Galois input, or automorphic
representation. The unrelated global Harris Proposition 4.8 is not its
conclusion.

## Dependencies

The module imports the unchanged
`Langlands.Global.Arithmetic.AuxiliaryCharacterStatement` and
`Langlands.Global.Arithmetic.GeneralPositionStatement`. The target is a
logical implication between their proposition definitions. Its proof is
reserved for a separate exact-target contribution and must establish the
actual topology and depth comparisons rather than assume them.
