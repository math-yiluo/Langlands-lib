# An endomorphism with invertible rational Tate map is surjective

`Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. For every algebraically closed field `k : Type u` of characteristic zero, every abelian scheme `A` over `Spec k`, every prime `p` and every endomorphism `α : A ⟶ A`: if `LinearMap.det (Tate.PrimeAdic.rationalMap (Over.mk (𝟙 _)) p α) ≠ 0`, then the underlying scheme morphism `hom α` is surjective (Mathlib's `Surjective`).

## Provenance

This is a derived statement. It is the contrapositive of the non-isogeny case of the chain in the proof of Milne, *Abelian Varieties*, author revision 2022 (registered source `milne-abelian-varieties-1986-author-2022`), Proposition 12.9, p. 23. Together with `FieldSurjectiveEndomorphismIsogenyStatement` it gives: if `α` is not an isogeny, then `det(V_p α) = 0`. Milne sets `deg α = 0` there (p. 21).

The expected proof is internal. If `V_p α` is invertible, then `α` is surjective on the `p`-power torsion `k`-points. The image of `α` is closed because `α` is proper. In characteristic zero the `p`-power torsion points are dense: this is the published `PrimePowerTorsion.dense_locus` (module `Langlands/AbelianScheme/Tate/PrimePowerTorsionDensity.lean`), whose source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, Theorem (5.30). So the image is everything.

## Scope

The characteristic-zero hypothesis matches the published density theorem. This is one of the four inputs of `IsogenyDegreeTateDeterminantNormReductionStatement` (Task 7330).
