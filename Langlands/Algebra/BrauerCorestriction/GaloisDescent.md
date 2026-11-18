# Galois descent for semilinear actions of a finite Galois group

Let `K` be a field and `N/K` a finite Galois extension (`[FiniteDimensional K N] [IsGalois K N]`). Write `G = N ≃ₐ[K] N`. This module proves Galois descent for vector spaces and algebras with a semilinear action of `G`. For algebras it also proves that the fixed algebra of a central simple `N`-algebra is central simple over `K`. The fields and the module or algebra have independent universes. There is no restriction on the characteristic. The fields need not be infinite.

The module is the descent step for the Brauer corestriction construction. There `G` acts semilinearly on a tensor product of conjugate scalar extensions, and the corestriction representative is the fixed algebra.

## Public declarations

Everything is in the namespace `Langlands.GaloisDescent`.

Auxiliary linear algebra over the Galois group:

- `galBasis K N : Module.Basis G K N` is a `K`-basis of `N` indexed by `G`. It exists because `|G| = [N : K]` (`IsGalois.card_aut_eq_finrank`). Classical choice selects it, and only its basis property is used.
- `galMatrix K N` is the `G × G` matrix `g, h ↦ g (galBasis K N h)` with entries in `N`. `galMatrix_isUnit` and `galMatrix_det_isUnit` say that it is invertible.
- `galCoeff K N h` is the entry `(galMatrix K N)⁻¹ h 1`. `sum_galBasis_mul_galCoeff` states `∑ h, g (b h) * galCoeff h = if g = 1 then 1 else 0`, and `sum_inv_mul_galBasis` is the entrywise form of `M⁻¹ M = 1`.

Vector spaces:

- `SemilinearAction K N V`, for an `N`-module `V`, is a structure. It consists of additive maps `act g : V →+ V` for `g : G` with `act 1 = id`, `act (g * h) = act g ∘ act h`, and the semilinearity law `act g (x • v) = g x • act g v` for `x : N`.
- For `ρ : SemilinearAction K N V`, with `V` also a `K`-module via a scalar tower `K → N → V`, `ρ.fixed : Submodule K V` is the space of vectors fixed by every `act g` (`mem_fixed`). `act_algebraMap_smul` shows that each `act g` is `K`-linear.
- `ρ.descentMap : N ⊗[K] ρ.fixed →ₗ[N] V` is the comparison map `x ⊗ v ↦ x • v` (`descentMap_tmul`).
- `ρ.trace` is the additive map `v ↦ ∑ g, act g v` (`trace_apply`), and `trace_mem_fixed` says that it takes values in the fixed space. `eq_sum_galCoeff_smul_trace` writes every vector as `v = ∑ h, galCoeff h • trace (galBasis h • v)`. `act_smul_of_mem_fixed` is the semilinearity law on fixed vectors.
- `bijective_liftBaseChange` is the general form of descent. Let `F` be a `K`-module and `ι : F →ₗ[K] V` an injective `K`-linear map whose range is `ρ.fixed`. Then the `N`-linear extension `N ⊗[K] F → V` is bijective.
- `descentMap_bijective` and `descentEquiv : N ⊗[K] ρ.fixed ≃ₗ[N] V` give Galois descent for vector spaces. `descentEquiv_tmul` computes it on pure tensors.

Algebras:

- `SemilinearAlgAction K N A`, for an `N`-algebra `A`, extends `SemilinearAction K N A` with `act g 1 = 1` and `act g (x * y) = act g x * act g y`. `act_algebraMap` computes the action on scalars.
- `ρ.fixedSubalgebra : Subalgebra K A` has the fixed vectors as carrier (`mem_fixedSubalgebra`).
- `ρ.descentAlgHom : N ⊗[K] ρ.fixedSubalgebra →ₐ[N] A` is the comparison algebra homomorphism `x ⊗ a ↦ x • a` (`descentAlgHom_tmul`). `descentAlgHom_toLinearMap` identifies its underlying linear map with the scalar extension of the inclusion.
- `descentAlgHom_bijective` and `descentAlgEquiv : N ⊗[K] ρ.fixedSubalgebra ≃ₐ[N] A` give effective Galois descent for algebras, an actual `N`-algebra isomorphism (`descentAlgEquiv_tmul`).
- `mem_span_fixedSubalgebra` says that the fixed algebra spans `A` over `N`.
- `finrank_fixedSubalgebra` states `finrank K A^G = finrank N A`. `finiteDimensional_fixedSubalgebra` gives finite dimensionality when `A` is finite-dimensional over `N`.
- `isCentral_fixedSubalgebra` proves `Algebra.IsCentral K A^G` when `A` is nontrivial and central over `N`.
- `isSimpleRing_fixedSubalgebra` proves `IsSimpleRing A^G` when `A` is a simple ring.

The last two theorems need no finite dimensionality of `A`. With `finiteDimensional_fixedSubalgebra` they show that the fixed algebra of a finite-dimensional central simple `N`-algebra is a finite-dimensional central simple `K`-algebra of the same dimension. The two structures are plain data with their laws as fields. No typeclass instance is installed.

## Implemented proof

**Galois matrix.** Dedekind's lemma in Mathlib (`linearIndependent_toLinearMap`) says that the automorphisms in `G`, viewed as `K`-linear maps `N → N`, are linearly independent over `N`. A relation among the rows of `galMatrix` gives an `N`-combination of these maps that vanishes on the basis `galBasis`, so by basis extensionality it vanishes everywhere. Hence the rows are linearly independent, and `Matrix.linearIndependent_rows_iff_isUnit` makes the matrix a unit. The two coefficient identities are entries of `M M⁻¹ = 1` and `M⁻¹ M = 1`.

**Surjectivity.** Expanding the trace and using semilinearity gives `∑ h, galCoeff h • trace (b h • v) = ∑ g, (∑ h, g (b h) * galCoeff h) • act g v`. The inner sum is `1` for `g = 1` and `0` otherwise, so the right side is `v`. Every trace is fixed: applying `act g` reindexes the sum by left multiplication by `g`. Hence `v` is the image of `∑ h, galCoeff h ⊗ f h`, where `ι (f h) = trace (b h • v)`.

**Injectivity.** By `TensorProduct.eq_repr_basis_left`, every element of `N ⊗[K] F` is `∑ h, b h ⊗ f h` for some `f`. If its image `∑ h, b h • ι (f h)` is zero, apply `act g` to get `∑ h, g (b h) • ι (f h) = 0` for every `g`, since each `ι (f h)` is fixed. Multiply by the row `h'` of `M⁻¹` and sum over `g`. The identity `M⁻¹ M = 1` then gives `ι (f h') = 0`, so `f h' = 0` by injectivity of `ι`.

**Algebra version.** The action fixes `1` and is multiplicative, so the fixed space is a `K`-subalgebra. Scalars from `K` are fixed because `g` is `K`-linear. The comparison map is `Algebra.TensorProduct.lift` of the structure map of `A` and the inclusion of the fixed algebra; their images commute because scalars from `N` are central. Its underlying linear map is the scalar extension of the inclusion, so the general bijectivity theorem applies. The dimension formula is `Module.finrank_baseChange` transported along the isomorphism.

**Centrality.** Let `z` be central in `A^G`. Because `A^G` spans `A` over `N`, `z` commutes with all of `A`. Centrality of `A` over `N` then gives `z = algebraMap N A x`. Applying `act g` shows `g x = x` for all `g`. Galois theory (`IsGalois.mem_bot_iff_fixed`) puts `x` in `K`, so `z` lies in the image of `K`.

**Simplicity.** Let `I` be a two-sided ideal of `A^G` and `P` the `N`-span of `I` in `A`. Since `A^G` spans `A`, an induction over both spans shows that `P` is stable under left and right multiplication by `A`, so `P` is a two-sided ideal of `A`. If `P = 0` then `I = 0`. If `P = A`, an induction over the span shows that for every `p ∈ P` and `y : N`, the trace of `y • p` lies in `I`. On a generator `i ∈ I` the trace is `trace_{N/K}(y) • i` by `trace_eq_sum_automorphisms`, which lies in `I`. Choose `y` with `trace_{N/K}(y) = 1` (`Algebra.trace_surjective`, using separability). The trace of `y • 1` is `trace_{N/K}(y) • 1 = 1`, so `1 ∈ I` and `I = A^G`.

## Sources and scope

The original statement is the Galois descent lemma of M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), Lemma (18.1), printed p. 279 / PDF p. 302, with its proof on printed p. 280 / PDF p. 303. The algebra version is the paragraph after the proof, also on printed p. 280 / PDF p. 303. KMRT state the lemma for the absolute Galois group acting continuously on an `F_sep`-vector space. This module proves the special case of a finite Galois extension acting through its finite Galois group. For a continuous action every vector is fixed by an open subgroup, which is how KMRT reduce to a finite Galois extension. That reduction is not formalized here.

The surjectivity proof follows KMRT: a Galois-matrix inversion by Dedekind's lemma. The injectivity proof differs. KMRT use a minimal linear relation; here the same inverse Galois matrix is applied to the coordinates in the Galois-indexed basis. The descent of centrality and simplicity is an internal derivation. Simplicity uses the trace, so it uses separability of `N/K` through the surjectivity of the field trace.

The consumer of this module is the tensor descent of conjugate algebras in J. Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un corps quelconque* (1971), §5.3, printed p. 208 / PDF p. 13. Tits forms the fixed algebra of a semilinear Galois permutation action, and this module provides the corresponding descent isomorphism and central simplicity over a finite Galois closure.
