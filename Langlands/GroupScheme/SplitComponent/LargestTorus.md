# The largest central lattice torus

Author: Worker 1178.

This internal module proves `exists_universal`: if `F'` is corepresented by an
algebra of finite type over a field `k`, there are a finite type `J` and a
central natural homomorphism
`j : latticeFunctor k (FreeAbelianGroup J) ⟶ F'` with surjective classifying
map such that every central homomorphism `α` from the lattice torus of a free
`ℤ`-module `Λ` of finite rank factors as `latticeMap l ≫ j` for some
`l : FreeAbelianGroup J →+ Λ`.

## Auxiliary constructions

- `lmap l` is the algebra map classifying `latticeMap l`, with `lmap_comp`,
  `lmap_id`, and `latticeMap_comp`.
- `trivialNat` is the trivial homomorphism; it is central.
- `mulNat β₀ β hβ` is the pointwise product of two natural homomorphisms
  when `β` is central (centrality makes the product multiplicative). For
  `α₀` on `Λ₀` and central `α` on `Λ`, the product
  `α' = mulNat (latticeMap inl ≫ α₀) (latticeMap inr ≫ α)` on `Λ₀ × Λ`
  restricts to `α₀` along `fst` and to `α` along `snd`
  (`latticeMap_fst_mulNat`, `latticeMap_snd_mulNat`).
- `imageSubgroup_latticeMap_comp`: the image lattice of `latticeMap l ≫ α` is
  the image under `l` of the image lattice of `α`.

## Maximal rank

`exists_maxRank`: by `exists_rank_bound`, the ranks of image lattices of
central homomorphisms are bounded; `Nat.findGreatest` gives a central `α₀` on
some `Λ₀` whose image lattice `M₀` has maximal rank (the trivial homomorphism
on `PUnit` realizes some rank).

## Proof of `exists_universal`

Choose a basis of `M₀` (`Submodule.basisOfPid`), giving
`E : FreeAbelianGroup J ≃+ M₀` with `J = ULift (Fin n)`, and put
`j = latticeMap E.symm ≫ imageHom d α₀`. It is central, and its classifying
map `imageClassify d α₀ ≫ lmap E.symm` is surjective.

Given a central `α` on `Λ`, form the product `α'` on `Λ₀ × Λ` and its image
lattice `M'`. Then `M₀ = fst(M')`, so restricting `fst` gives a surjection
`ρ : M' → M₀`. Maximality gives `rank M' ≤ rank M₀`, and surjectivity the
converse inequality; with an isomorphism `M₀ ≅ M'` of free modules of equal
rank (`LinearEquiv.ofFinrankEq`), the Orzech property
(`OrzechProperty.injective_of_surjective_endomorphism`) makes `ρ`
injective. With `l₀ = snd ∘ (M' ↪ Λ₀ × Λ) ∘ ρ⁻¹ : M₀ → Λ`, the classifying
maps satisfy `imageClassify α₀ = imageClassify α' ≫ lmap ρ` (cancel the
injective `incl M₀`) and then
`imageClassify α₀ ≫ lmap l₀ = classify α`; so
`latticeMap l₀ ≫ imageHom d α₀ = α`, and `l = l₀ ∘ E` works for `j`.

## Provenance

Internal. Mathematically: a central split torus of maximal rank contains every
central split torus, since the product of the two has image of the same rank.
