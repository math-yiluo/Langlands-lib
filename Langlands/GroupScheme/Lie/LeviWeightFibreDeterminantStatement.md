# Determinant characters of weight spaces of a central split torus

**Exact target.** `Langlands.GroupScheme.LeviWeightFibreDeterminantStatement`.

Let `k` be a field, `G` an affine group scheme locally of finite type over `Spec k`, `M` an affine group scheme over `Spec k` with a homomorphism `l : M ⟶ G`, and `a : A ⟶ M` a central homomorphism (`IsCentral a`) from a commutative group scheme whose underlying group is a split torus. Let `K` be a field with a `k`-algebra structure, `f = algebraBaseMap k K` and `BC = GroupScheme.baseChange f`.

For every character `β` of `A` the statement asserts a rational character `χ` of `M` over `k` with the following property. For every commutative group scheme `S` over `K` whose underlying group is a split torus, every homomorphism `s : S ⟶ M_K`, and every homomorphism `j : A_K ⟶ S` with `j ≫ s = BC.map a`, the restriction to `S` of the base change of `χ` (read in the character lattice of `S` through `rationalCharacters.equivCharacterLattice`) is

```
∑ᶠ α with j ≫ α = β_K ,  dim_K (weightSpace (s ≫ BC.map l) α) • α ,
```

where `β_K = characterLattice.baseChange f A β` and `weightSpace` is the actual adjoint weight space in the Lie algebra of `G_K`. The sum is a `finsum`; only finitely many `α` have a nonzero weight space.

The intended character is the determinant of `M` acting on the `β`-weight space `𝔤_β` of `A` in `Lie G`. Since `A` is central in `M`, the adjoint action of `M` preserves `𝔤_β`, so this determinant is a rational character over `k`. After base change, `𝔤_β ⊗ K` is the `β_K`-weight space of `A_K` in `Lie G_K`; since `A_K` acts through `S`, it is the direct sum of the `S`-weight spaces for the characters `α` over `β_K`, and the determinant of the split torus `S` on it is the displayed dimension-weighted sum. The statement asks for the existence of such a character; it does not single out the determinant.

**Provenance.** Derived. The weighted sums are Arthur's sums `∑_{α ∈ Σ(β)} m_α α` over the roots restricting to a given root, with `m_α` the multiplicity, in the definition of a special subspace: J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7, printed p.355 (PDF p.33), `arthur-1988-invariant-trace-formula-I`. The statement records that these sums are restrictions of rational characters of `M` defined over the smaller field. No finiteness, separability or Galois hypothesis on `K/k`, and no reductivity of `G` or `M`, is assumed.

This file states the proposition and does not prove it.
