# Lattice tori as corepresented group functors

Author: Worker 1178.

This internal module works with group-valued functors `F` on commutative
`R`-algebras, corepresented by an algebra `B` (the published
`Corepresented` interface, with the `pt`/`cls`/`comul` notation of
`Corepresented.LinearEmbedding`). Its `classify` and `antipode` reuse the
published `Corepresented.classify` and `Corepresented.antipode`; the
comultiplication and antipode compatibility proofs reuse the corresponding
results in `CorepresentedComultiplication`. It has two parts.

## Natural homomorphisms and their classifying maps

For corepresentations `e` of `F` by `B` and `d` of `F'` by `B'`, and a
natural homomorphism `α : F ⟶ F'`:

- `classify e d α : B' ⟶ B` is the algebra map classifying the image of the
  universal point `pt e (𝟙 B)`;
- `app_eq`: `α.app S x = pt d (classify e d α ≫ cls e x)`, by naturality of
  `α` at `cls e x`; hence `nat_ext` (equal classifying maps give equal
  natural homomorphisms) and `classify_comp` (contravariant composition);
- `classify_comul`: multiplicativity of `α` on the two universal points over
  `B ⊗ B` gives `classify ≫ comul e = comul d ≫ pair (classify ≫ inl) (classify ≫ inr)`;
- `classify_antipode`: with `antipode e := cls e (pt e (𝟙 B))⁻¹` and
  `cls_inv : cls e x⁻¹ = antipode e ≫ cls e x`, `α` commutes with the
  antipodes;
- `ofClassify ψ hψ`: conversely, an algebra map `ψ : B' ⟶ B` compatible with
  the comultiplications defines the natural homomorphism
  `x ↦ pt d (ψ ≫ cls e x)`; multiplicativity uses the Library's `cls_mul` and
  `pt_mul`. `classify_ofClassify` recovers `ψ`.

## Lattice tori

For an abelian group `Λ`, `latticeFunctor R Λ` sends `A` to the group
`Multiplicative Λ →* Aˣ` of characters of `Λ` with values in units, with
pointwise multiplication. The functor, algebra, universal character,
corepresentation and restriction map reuse `Diagonalizable.functor`,
`algebra`, `monomialUnits`, `grpCorepresentation` and `restrict` from
`Torus/Diagonalizable`, with the same pointwise formulas.
`latticeCorep R Λ` corepresents it by the group
algebra `latticeAlgebra R Λ = R[Λ]` (`AddMonoidAlgebra R Λ`): an algebra map
`f` corresponds to `m ↦ f [m]`, inversely through `AddMonoidAlgebra.lift`.
The lemmas compute the corepresentation on the basis `[m]`: the
comultiplication is `[m] ↦ [m] ⊗ [m]` and the antipode is `[m] ↦ [-m]`.
For `l : Λ →+ Λ'`, `latticeMap l` restricts characters along `l`; it is
classified by `[m] ↦ [l m]`.

## Provenance

These are internal constructions on the published `Corepresented` interface
and Mathlib's `AddMonoidAlgebra`; they are the usual dictionary between
diagonalizable groups and group algebras, used here only in the generality
that the split-component proof needs.
