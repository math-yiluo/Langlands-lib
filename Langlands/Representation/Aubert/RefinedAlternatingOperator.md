# Exact refined K0 maps and the alternating operator on product Levis

Author: Worker 320.

This is an internal specialization of the published conditional construction
in `Aubert.RefinedAlternatingConstruction`. It supplies its preservation
argument with the proved theorem
`Parabolic.normalizedRefinedFiniteLengthExactness` from
`Parabolic.RefinedFiniteLengthFunctorProof`. Both imported pairs are
unchanged. No new assertion from the literature is transcribed here.

## Actual maps and universes

For arbitrary `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)` and
`T : F.TopologicalData`, the definitions
`Parabolic.normalizedRefinedInductionK0.{uF,uV} F T B S` and
`Parabolic.normalizedRefinedJacquetK0.{uF,uV} F T B S` give integer-linear
maps between the exact finite-length Grothendieck groups of the actual
product Levi `B.Levi F.Carrier` and its actual refined Levi
`Geometric.refinedLevi F.Carrier B S`. They use `T.topology`.
The first goes from the refined Levi to the product Levi; the second
has the reverse direction.

The two carrier universes `uF` and `uV` are independent. Both groups use
representation carriers in `Type (max uF uV)` so the induction functor
is an endofunctor on that universe. The preservation theorem is applied
at `.{uF, max uF uV}`. The exact quotient retains every actual short
exact sequence, including nonsplit ones. These are the existing normalized
refined induction and Jacquet functors, with positive half-modulus and
right translation for induction, and inverse half-modulus on the actual
unipotent coinvariants for Jacquet. No abstract substitute functor or
split finite-dimensional quotient is introduced.

Each `_finiteLengthClass` theorem computes the map on an actual object
as the class of the actual output. The input finite-length proof and any
chosen output finite-length proof appear only to form these classes.
The maps themselves have no preservation premise: all four required
preservation clauses are supplied by the published theorem.

## Alternating sum and evaluations

`Aubert.alternatingOperatorOnLevi.{uF,uV} F T B` is the integer-linear
endomorphism of the product-Levi exact group

```text
∑ S : Geometric.BlockRefinement B,
  (-1)^(∑ i, (B.size i - (S i).length)) •
    normalizedRefinedInductionK0 F T B S ∘
      normalizedRefinedJacquetK0 F T B S.
```

It is definitionally the published `alternatingOperatorOnLeviOf` with
the proved preservation argument. The exponent is the existing
`refinementSignExponent B S`; its published theorem identifies it with
`n - ∑ i, (S i).length`. The sum ranges over every actual ordered refinement,
using the existing finiteness instance; the definition needs no externally
chosen enumeration. This is the unadjusted sign convention, without an
irreducible-dependent sign.

`alternatingOperatorOnLevi_eq_sum` permits any `Fintype` instance on
refinements, and `alternatingOperatorOnLevi_apply` evaluates the sum on
an arbitrary class. Both follow directly from their conditional versions.
`refinedInductionJacquet_hasFiniteLength` composes the proved Jacquet and
induction finite-length clauses. The theorem
`alternatingOperatorOnLevi_finiteLengthClass` evaluates on the class of
an actual finite-length product-Levi representation, using these proved
output lengths. Its proof specializes the conditional generator theorem.

All ranks, including zero, and all positive ordered outer shapes and
refinements are included. No admissibility, tensor factorization,
irreducibility, central character or positive-rank premise is used.

## Scope and independence

The construction discharges the explicit preservation argument of the
previous conditional maps and operator. It supplies no Jacquet compatibility,
induction compatibility, equality with the GL operator under a group
comparison, involutivity, irreducible image, or analytic classification.
Those require further mathematical arguments. The host segment
classification remains unchanged.

Its only new dependency beyond the conditional construction is the
published refined preservation proof. That proof derives finite length
from the all-rank standard theorem through flattening, transitivity and
actual Jacquet evaluation quotients, and proves exactness directly on
the actual maps. Its paired Markdown documents the lower inputs and
independence. No excluded segment, special-head, quotient-exhaustion,
tempered-uniqueness, square-integrable-classification or regular-exhaustion
conclusion is used here.
