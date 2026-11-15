# Torsion-free permutation coinvariants and injectivity by a norm argument

This module proves two facts about integral group representations and their
coinvariants. Both are used in the proof of
`Langlands.Geometry.Building.Kottwitz.InducedCentralTorusInertiaInjectivityStatement`
(module `Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityProof`).
The module works with Mathlib's `Representation.Coinvariants ρ`, the quotient of
`V` by the integral span of all `ρ g x - x`. The namespace is
`Langlands.CoinvariantsNorm`. Throughout, `G` is a group and the modules are
`ℤ`-modules with arbitrary `Module ℤ` instances.

## Provenance

Both results are standard facts of elementary group cohomology. They are
written out here because the Library has no version of them. They replace the
homological argument of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), proof of Lemma 11.1.10, printed p. 425 / PDF p. 456. That proof bounds
the kernel of `X_*(T₁)_I → X_*(T₂)_I` by the finite group `H₁(I, X_*(T₃))`
after replacing `I` by a finite quotient through which it acts, and then uses
the torsion-freeness of `X_*(T₁)_I`. The norm argument below gives the same
conclusion without homology and without exactness in the middle.

## `orbitSetoid`

For a representation `ρ` and a basis `b : Module.Basis ι ℤ V`, `orbitSetoid ρ b`
is the relation `i ~ j ↔ ∃ g, ρ g (b i) = b j` on the index type. It is an
equivalence relation for every representation: reflexivity uses `g = 1`,
symmetry uses `g⁻¹`, and transitivity uses the product. It is an orbit relation
when `ρ` permutes the basis.

## `eq_zero_of_smul_eq_zero_of_permuted`

**Statement.** Suppose that `ρ` permutes `b`: for every `g` and `i` there is a
`j` with `ρ g (b i) = b j`. Let `n : ℕ` be nonzero and let `x` be a class in
`Coinvariants ρ` with `n • x = 0`. Then `x = 0`. In other words, the
coinvariants of a permutation lattice are torsion-free. The multiple is a
natural number (`nsmul`). This avoids comparing the given `Module ℤ` structure
on the coinvariants with the canonical one.

**Proof.** Choose a representative `rep i` of the orbit class of each index
(`Quotient.out`). Define `φ : V →ₗ[ℤ] V` on the basis by `φ (b i) = b (rep i)`
(`Module.Basis.constr`).

1. `v - φ v` lies in the augmentation submodule `Coinvariants.ker ρ` for every
   `v`. By `Submodule.map_span_le` it suffices to check this on basis vectors.
   There `b i - b (rep i) = ρ g (b (rep i)) - b (rep i)` for some `g`, because
   `rep i ~ i`.
2. `φ ∘ ρ g = φ` for every `g`. On a basis vector, `ρ g (b i) = b j` with
   `i ~ j`, so both sides give `b (rep i) = b (rep j)`. Hence `φ` descends to
   `Coinvariants.lift ρ φ`.
3. Write `x = mk v`. Then `mk (n • v) = n • x = 0`, so `φ (n • v) = 0` by the
   descended map. Since `V` has a basis, it is torsion-free
   (`Module.Basis.smul_eq_zero`), so `φ v = 0`. By step 1,
   `x = mk (v - φ v) = 0`.

## `injective_of_finite_range`

**Statement.** Let `ρM` and `ρN` be representations of `G` on `M` and `N`, and
let `j : M →ₗ[ℤ] N` be injective and equivariant. Assume:

- the set of operators `Set.range ρN` is finite;
- the coinvariants of `M` are torsion-free, in the `nsmul` form above.

Then every linear map `m : Coinvariants ρM → Coinvariants ρN` with
`m (mk x) = mk (j x)` is injective.

**Proof.** Let `S` be the finite set of operators `ρN g` and define the norm
`Nm_N = Σ_{f ∈ S} f`.

1. `Nm_N ∘ ρN g = Nm_N`. Right multiplication by `ρN g` permutes `S`, with
   inverse right multiplication by `ρN g⁻¹` (`Finset.sum_nbij'`). Hence `Nm_N`
   descends to the coinvariants and vanishes on the augmentation submodule of
   `N`.
2. Choose for each `f ∈ S` an element `sec f` of `G` with `ρN (sec f) = f`. Set
   `Nm_M = Σ_{f ∈ S} ρM (sec f)`. Equivariance gives `j ∘ Nm_M = Nm_N ∘ j`.
3. `Nm_M x - |S| • x = Σ_{f ∈ S} (ρM (sec f) x - x)` lies in the augmentation
   submodule of `M`.
4. If `m (mk x) = 0`, then `mk (j x) = 0`, so `Nm_N (j x) = 0` by step 1.
   Hence `j (Nm_M x) = 0` and `Nm_M x = 0`, because `j` is injective. By step
   3, `|S| • mk x = 0`. Since `S` contains `ρN 1`, `|S| ≠ 0`, and torsion-freeness
   gives `mk x = 0`.

Exactness of `M → N → N/M` is not used; only the injectivity of `j` is.
