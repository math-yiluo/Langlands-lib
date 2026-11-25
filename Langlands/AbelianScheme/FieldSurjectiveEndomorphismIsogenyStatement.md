# Surjective endomorphisms of abelian varieties are isogenies

`Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyStatement` is a proposition. This file proves nothing.

## Statement

Fix a universe `u`. For every algebraically closed field `k : Type u` (of any characteristic), every abelian scheme `A` over `Spec k` and every endomorphism `α : A ⟶ A`: if the underlying scheme morphism `hom α` is surjective (Mathlib's `Surjective`), then `IsIsogeny α`, that is, `hom α` is finite, flat and surjective.

## Source

The source is Milne, *Abelian Varieties*, author revision of January 2, 2022 (registered source `milne-abelian-varieties-1986-author-2022`). Printed page numbers equal PDF page numbers.

- p. 12, Proposition 8.1: for a homomorphism `f : A → B` of abelian varieties, (b) `dim A = dim B` and `f` surjective, is equivalent to (d) `f` finite, flat and surjective. Milne derives (b) ⇒ (c) (finite kernel) from the theorem on the dimension of fibres, and (c) ⇒ (d) by translations and local freeness.

The proposition is (b) ⇒ (d) for endomorphisms, where `dim A = dim B` is automatic. The Library proves (c) ⇒ (d) for endomorphisms over any field (`GroupScheme.fieldFiniteKernelIsogeny`); the further step is (b) ⇒ (c). The proposition itself is proved by `fieldSurjectiveEndomorphismIsogeny` (module `Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyProof`), by a route through flatness.

## Scope

The field is assumed algebraically closed. This is one of the four inputs of `IsogenyDegreeTateDeterminantNormReductionStatement` (module `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormReduction`).
