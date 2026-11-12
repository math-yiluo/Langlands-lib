# Derived subgroups are annihilated by commutative targets: proof of the conjunction

This module proves the published proposition
`Langlands.GroupScheme.DerivedAnnihilationStatement` of
[`AnnihilationStatement`](AnnihilationStatement.md):

- `Langlands.GroupScheme.derivedAnnihilation : DerivedAnnihilationStatement.{u}`.

The statement is by definition the conjunction
`DerivedCommutativeAnnihilationStatement.{u} ∧ DerivedCharacterAnnihilationStatement.{u}`:
after any scalar extension `R` of a field `k`, every homomorphism from `G_R` to the base
change `H_R` of a commutative affine locally finite type group scheme `H` is trivial on
the actual derived inclusion `d_R`, and every rational character of `G_R` restricts to
zero on `d_R`.

The source is J. S. Milne, *Algebraic Groups* (2017), Corollary 6.19(d), printed p.129 /
PDF p.145, registered as `milne-2017-algebraic-groups`.

## Proof

The anonymous constructor pairs the two published theorems below; no other argument is
used. Their own proofs (described in their paired Markdown) use the Library's field base
change of the derived subgroup in place of Milne's local commutator generation of
6.19(c).

## Published inputs

- `Langlands.GroupScheme.derivedCommutativeAnnihilation`
  (module `Langlands.GroupScheme.Derived.AnnihilationCommutativeProof`).
- `Langlands.GroupScheme.derivedCharacterAnnihilation`
  (module `Langlands.GroupScheme.Derived.AnnihilationCharacterProof`).

The axiom inspection of `derivedAnnihilation` reports only `propext`, `Classical.choice` and
`Quot.sound`.
