# Decomposition homomorphisms and embeddings of closures at the places

`Langlands/Galois/RestrictedRamification/PlaceEmbeddings.lean`, namespace `Langlands.Galois`.

**Decomposition homomorphisms.** Let `E / K` be a normal extension, `K → Kv → Ωv` a tower of fields
and `ι : E →ₐ[K] Ωv` an embedding. An automorphism `σ` of `Ωv` over `Kv` maps `ι(E)` to itself
(normality), so it defines `decompositionHom Kv ι σ ∈ Gal(E / K)` with `ι ∘ decompositionHom Kv ι σ =
σ ∘ ι`. This is a continuous homomorphism `Gal(Ωv / Kv) → Gal(E / K)`; replacing `ι` by `ι ∘ g`,
`g ∈ Gal(E / K)`, conjugates it by `g`, and any two embeddings differ in this way.

**Embeddings at the places.** `PlaceEmbeddings K Ω`, for a number field `K` and a field `Ω` over
`K`, bundles one `K`-embedding of `Ω` into `AlgebraicClosure (v.adicCompletion K)` for every finite
place `v` and into `AlgebraicClosure w.Completion` for every infinite place `w` (Neukirch–Schmidt–
Wingberg's fixed choice of embeddings `i_p : k̄ → k̄_p`). Such a choice exists when `Ω` is a
separable closure of `K`. For `Ω = AlgebraicClosure K`, `PlaceEmbeddings.standard K` is the choice
made by Mathlib's `Field.absoluteGaloisGroup.map (algebraMap K Kv)`: its decomposition
homomorphisms are Mathlib's maps of absolute Galois groups.

```lean
noncomputable def decompositionHom (Kv : Type*) [Normal K E] (ι : E →ₐ[K] Ωv) : Gal(Ωv/Kv) →ₜ* Gal(E/K)
theorem decompositionHom_apply [Normal K E] (ι : E →ₐ[K] Ωv) (σ : Gal(Ωv/Kv)) (x : E) :
    ι (decompositionHom Kv ι σ x) = σ (ι x)
theorem decompositionHom_comp [Normal K E] (ι : E →ₐ[K] Ωv) (g : Gal(E/K)) (σ : Gal(Ωv/Kv)) :
    decompositionHom Kv (ι.comp (g : E →ₐ[K] E)) σ = g⁻¹ * decompositionHom Kv ι σ * g
theorem exists_eq_comp_of_normal [Normal K E] (ι ι' : E →ₐ[K] Ωv) : ∃ g : Gal(E/K), ι' = ι.comp (g : E →ₐ[K] E)
structure PlaceEmbeddings (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω] where
  finite : ∀ v : HeightOneSpectrum (𝓞 K), Ω →ₐ[K] AlgebraicClosure (v.adicCompletion K)
  infinite : ∀ w : InfinitePlace K, Ω →ₐ[K] AlgebraicClosure w.Completion
instance [IsSepClosure K Ω] : Nonempty (PlaceEmbeddings K Ω)
noncomputable def PlaceEmbeddings.standard (K) : PlaceEmbeddings K (AlgebraicClosure K)
theorem decompositionHom_standardEmbedding {L : Type*} [Field L] [Algebra K L]
    (σ : Gal(AlgebraicClosure L/L)) :
    decompositionHom L (standardEmbedding (K := K) (L := L)) σ = Field.absoluteGaloisGroup.map (algebraMap K L) σ
```

## Outline of the proofs

- `decompositionHom` is Mathlib's `AlgEquiv.restrictNormalHom E` after `AlgEquiv.restrictScalarsHom K`,
  for the algebra structure on `Ωv` over `E` given by `ι`. Continuity at `1`: an open neighbourhood
  of `1` in `Gal(E / K)` fixes a finite `L ≤ E`; the subgroup of `Gal(Ωv / Kv)` fixing the images of
  a basis of `L` is open (finitely many algebraic elements) and maps into it.
- Conjugation and comparison of two embeddings follow from the characterization
  `decompositionHom_eq_iff` and `AlgHom.restrictNormal'`.
- *Mathlib's choice.* `Field.absoluteGaloisGroup.map f` uses the algebra structure `f.toAlgebra`
  and the embedding `IsAlgClosed.lift : AlgebraicClosure K → AlgebraicClosure L` for it. For
  `f = algebraMap K L` this algebra structure is not definitionally Mathlib's instance (their scalar
  actions differ), so `standardEmbedding` is defined from the underlying ring homomorphism
  (`standardEmbeddingRingHom`), with the commutation proved through `IsScalarTower`. The agreement
  `decompositionHom_standardEmbedding` is then the defining property of `restrictNormal`, applied
  with the algebra structures `map` uses.

## Declarations

- `decompositionMonoidHom Kv ι` with `decompositionMonoidHom_apply`, `decompositionMonoidHom_eq_iff`,
  `continuous_decompositionMonoidHom`; `decompositionHom Kv ι` with
  `decompositionHom_toMonoidHom`, `decompositionHom_apply`, `decompositionHom_eq_iff`;
  `exists_eq_comp_of_normal`, `decompositionHom_comp`, `decompositionHom_comp_val` (restriction to a
  normal subextension `N`), `nonempty_algHom_of_isSepClosed`.
- `standardEmbeddingRingHom K L i`, `standardEmbeddingRingHom_algebraMap`, `standardEmbedding`,
  `standardEmbedding_map`, `decompositionHom_standardEmbedding`.
- `PlaceEmbeddings` (fields `finite`, `infinite`), its `Nonempty` instance for a separable closure,
  `PlaceEmbeddings.standard`, `PlaceEmbeddings.decompositionHom_standard_finite`,
  `PlaceEmbeddings.decompositionHom_standard_infinite`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file
`src/GroundTheory/ProfiniteCohomology/RestrictedRamification/LocalMaps.lean`, section `DecompHom`
(lines 11–97) and lines 203–213 (`nonempty_algHom_adicCompletion`,
`nonempty_algHom_infinitePlace_completion`, which become the `Nonempty` instance). The repository
has no licence file; its text is used with attribution
(`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source's `decompHom` (a `→*`, with
`continuous_decompHom` beside it) is bundled as the continuous homomorphism `decompositionHom`;
universes are independent; `PlaceEmbeddings` replaces the families `ιs : ∀ v : S, …` and
`ιr : ∀ v : {v // v.IsReal}, …` that the source passes separately; `standardEmbedding` and the
agreement with `Field.absoluteGaloisGroup.map` are new. The sections `Conj` and `Local` of
`LocalMaps.lean` (cohomology) are not in this file (see `GG1-LEFT-OUT.tsv`).

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VIII, §1, p. 427 (the fixed choice of `k`-embeddings
  `i_p : k̄ → k̄_p` and the decomposition groups `G_p(K | k) = G(K_p | k_p)`).
- J. Neukirch, *Algebraic Number Theory* (translated by N. Schappacher, Springer 1999), chapter II,
  §8, Extension Theorem (8.1), pp. 161–162 (every extension of a valuation comes from an embedding
  into `K̄_v`; two embeddings give the same extension if and only if they are conjugate over `K_v`).
