# Proof of the flattened-refinement full modulus comparison

Author: Worker 776.

This file proves the exact closed proposition
`Langlands.Parabolic.FlattenedRefinementModulusStatement.{uF}` as the theorem
`Langlands.Parabolic.flattenedRefinementModulus`. The theorem's type is that
proposition itself. It adds no hypotheses, specializes no parameter and
introduces no new definitions.

The statement says the following. Take a prime `p`, a field
`F : PadicField.{uF} p` with topological data `T`, a rank `n`, an ordered
block shape `B` of `n` and an ordered block refinement `S` of `B`. Then

```lean
(T.composedLeviModulus B S).comp
  (Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom =
    T.leviModulus (B.flatten S)
```

as monoid homomorphisms from `(B.flatten S).Levi F.Carrier` to `ℝ≥0ˣ`.

## The proof

The proof introduces the quantified parameters `p`, the `Fact p.Prime`
instance, `F`, `T`, `n`, `B` and `S`, in the statement's order. It then
applies the published theorem
`Langlands.PadicField.TopologicalData.composedLeviModulus_flattened` from
`Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation`,
as `T.composedLeviModulus_flattened B S`. For these fixed parameters, that
theorem's conclusion is literally the displayed equality, with the same
forward equivalence `flattenedLeviEquiv F.Carrier B S`. No rewriting or
conversion is needed.

The proof itself contains no determinant or modulus computation. The
determinant calculation and the lexicographic partition of fine-block pairs
are done only in the imported calculation module. Its Markdown and the
statement's Markdown describe those steps. This file adds no second
normalization implementation.

## Scope

The theorem holds for every prime, every p-adic field in an arbitrary field
universe `uF`, all compatible topological data, every rank including zero,
and every block shape and refinement. These are exactly the statement's
quantifiers, and the imported theorem carries no positivity or
nonemptiness hypothesis either. The kernel check reports only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The proof uses no
`sorry`, `admit` or `native_decide`.

The module imports only the statement module and the calculation module. It
leaves both unchanged.

## Provenance

This is an internal consequence of published Library results. Bernstein
and Zelevinsky (1977), §§1.7–1.9, §2.2 and Proposition 2.3(c), motivate
the statement through compatibility of normalizing characters under
refinement. The statement's Markdown records those citations and explains
which parts of the formulation are internal. The present proof does not
follow a proof from that source. It reuses the Library's determinant-product
calculation. It says nothing about the relation to Haar-measure scaling on
unipotent radicals, and it proves no consequences for positive half
characters.
