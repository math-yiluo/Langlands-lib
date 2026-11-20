# Proof of the multiplicative-unipotent decomposition (Milne 16.13)

The theorem `Langlands.GroupScheme.commutativeMultiplicativeUnipotentDecomposition`
proves the Library statement
`Langlands.GroupScheme.CommutativeMultiplicativeUnipotentDecompositionStatement`
(Milne, *Algebraic Groups* (2017), Theorem 16.13). Let `k` be a field and `G` a
commutative group scheme over `Spec k` that is affine and locally of finite type.

## Route

The proof only assembles results from four companion units in
`Langlands/GroupScheme/Commutative/`. All of them live in the namespace
`Langlands.GroupScheme.CommutativeDecomposition`.

1. **Part (a).** `exists_characteristic_multiplicativePart`
   (`MultiplicativePartCharacteristic`) gives every clause of part (a):
   - a closed subgroup `s : S ⟶ G` of multiplicative type that contains every
     closed subgroup of multiplicative type;
   - for every `k`-algebra `R` and automorphism `α` of `G_R`, the equality
     `range (s_R ≫ α) = range s_R`;
   - an fppf quotient `q : G ⟶ Q` by the range of `s`, with `Q` unipotent.

   That unit builds on `exists_multiplicativePart`
   (`MultiplicativePartExistence`).
2. **Part (b), existence.** Assume `k` is perfect.
   `exists_multiplicativeUnipotentDecomposition`
   (`MultiplicativeUnipotentSplitting`) gives a unipotent closed subgroup
   `u : U ⟶ G` and a closed subgroup `s : S ⟶ G` of multiplicative type such
   that `subgroupMultiplication u s` is an isomorphism.
3. **Part (b), uniqueness.** Take any decomposition `(U, S, u, s)` with the
   properties listed in the statement. `range_le_of_isUnipotent`
   (`MultiplicativeUnipotentUniqueness`) shows that the range of `u` contains
   every unipotent closed subgroup. It uses that `S` is of multiplicative type
   and that the multiplication map is an isomorphism.
   `range_le_of_isMultiplicativeType` shows that the range of `s` contains
   every closed subgroup of multiplicative type. It uses that `u` is a closed
   subgroup, that `U` is unipotent, and that the multiplication map is an
   isomorphism. Neither lemma needs `k` to be perfect.

The isomorphism hypothesis is passed to the uniqueness lemmas as an instance
(`let := hiso`).

## Provenance

The statement and its parts follow Milne, *Algebraic Groups* (2017),
Theorem 16.13 (printed p. 328). The companion units' Markdown files give the
proof routes and say where they depart from Milne's proof. This module adds
no mathematics of its own.
