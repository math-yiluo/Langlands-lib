# Actual finite-series and multiplicity transport

`Langlands.MultiplicityTransportStatement` bundles four proposition
definitions. This pair states the transport assertions; it proves none of
them. The field universe `uK`, acting-group universes `uG` and `uH`, and
representation-carrier universes `uA`, `uB`, `uT` and `uU` are independent.

## Pullback along a group equivalence

`GroupEquivFiltrationMultiplicityTransportStatement` works over any field
`k` and groups `G` and `H`, with an actual group equivalence `e : H ≃* G`.
For any representations `A` and `τ` of `G` and every supplied actual
filtration `s : ObjectRepFiltration A n`, it asserts the existence of an
actual filtration `t` of `Rep.of (A.ρ.comp e.toMonoidHom)`, of the same
length `n`, with all of these properties:

- For each `i : Fin (n + 1)`, its underlying vector submodule equals that
  of `s` at `i`.
- `s.HasSimpleFactors` if and only if `t.HasSimpleFactors`.
- For each `i : Fin n`, the pullback along `e` of the actual quotient
  representation `s.gradedRepresentation i` is equivalent as a
  representation to `t.gradedRepresentation i`.
- The exact natural-number counts satisfy
  `t.factorMultiplicity (Rep.of (τ.ρ.comp e.toMonoidHom)) = s.factorMultiplicity τ`.

The initial filtration need not have simple factors, and `τ` need not be
irreducible. The actual chain, its quotient-equivalence witnesses and the
count equality are conclusions. Pullback changes only the acting group:
the vector space and all chain submodules stay the same. Surjectivity of
`e` makes invariance under the two actions equivalent, including on the
successive quotients. Applying the same construction to `e.symm` gives
reverse transport; no extra series-existence assumption is present.

## Ambient and constituent equivalences

`EquivCompositionSeriesMultiplicityTransportStatement` concerns one fixed
monoid `G` over any field `k`. Its inputs are representations `A`, `B`, `τ`
and `υ` in four independent carrier universes, actual representation
equivalences `φ : A.ρ.Equiv B.ρ` and `ψ : τ.ρ.Equiv υ.ρ`, and a supplied
composition series `s` of `A`. It asserts an actual composition series `t`
of `B` of the same length, actual equivalences from each graded factor of
`s` to the factor of `t` at the identical index, and the exact equality
`t.factorMultiplicity υ = s.factorMultiplicity τ`.

The published `Langlands.jordanHolderSeriesTransport` in
`Langlands.Representation.Filtration.JordanHolderTransportProof` already
constructs the actual image series and its graded equivalences for `φ`.
A later proof of this statement can reuse that theorem. The additional
count assertion follows by comparing the factor predicates at each
index: an equivalence from the original factor to `τ` composes with the
inverse graded equivalence and `ψ` to give one from the transported factor
to `υ`; composing in the opposite direction gives the reverse implication.
Thus the identity on indices restricts to an equivalence of the two finite
counting subtypes. Their `Nat.card` values, which define
`factorMultiplicity`, are equal. This comparison counts repeated factors
at their separate indices. It does not use irreducibility of `τ` or `υ`.

## Multiplicity consequences and scope

`GroupEquivJordanHolderMultiplicityTransportStatement` asserts the
corresponding equivalence between `HasJordanHolderMultiplicity A τ m` and
the predicate on both group pullbacks, with the same natural number `m`.
`EquivJordanHolderMultiplicityTransportStatement` asserts the equivalence
between `HasJordanHolderMultiplicity A τ m` and
`HasJordanHolderMultiplicity B υ m` under `φ` and `ψ`, again with exactly
the same `m`. These are consequences to be proved by transporting the
actual series witnesses in each direction. They accompany the supplied
filtration assertions and do not replace them. No arbitrary representation
is assumed or asserted to have a composition series.

All lengths, zero representations and empty series are included. The
assertions supply no additivity theorem, exactness of a functor,
finite-length theorem for induction, tensor factorization, Jacquet
comparison, analytic continuation or classification result. They introduce
no chosen total multiplicity function and leave existing Library pairs
unchanged.

## Provenance

This is an internal elementary transport interface for the Library's actual
invariant-subspace filtrations, quotient representations,
`Representation.Equiv`, `factorMultiplicity` and existential
`HasJordanHolderMultiplicity`. It is derived from those constructions and
the elementary preservation of invariant subspaces under a bijective change
of acting group, and from composition of actual representation
equivalences. The published Jordan–Hölder series transport and multiplicity
independence proofs provide related existing finite-series machinery.
There is no attribution of this exact Lean interface to an external
literature theorem. The concrete intended application uses
`Geometric.flattenedLeviEquiv` to pass between the actual flattened product
Levi and the common refined Levi subgroup; that application adds no premise
to these algebraic assertions.
