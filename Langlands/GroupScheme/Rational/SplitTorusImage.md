# Images of split tori in affine group schemes over a field

Author: Worker 228.

## Main theorem

`Langlands.GroupScheme.IsSplitTorus.exists_factor_isSplitSubtorus`: let `k` be a field
(`k : Type u`), `D` a commutative group scheme over `Spec k` whose underlying group scheme is a
split torus (`IsSplitTorus D.toGrp`), `H` a group scheme over `Spec k` with affine structure
morphism (`IsAffineHom H.X.hom`), and `φ : D.toGrp ⟶ H` a homomorphism. Then there are a
commutative group scheme `D'` and homomorphisms `π : D.toGrp ⟶ D'.toGrp` and
`i : D'.toGrp ⟶ H` with

* `IsSplitSubtorus i`: `D'` is a split torus and `i` is a closed immersion, in the sense of the
  published [`Rational/SplitTorus`](SplitTorus.md);
* `π ≫ i = φ`;
* `IsCentral φ → IsCentral i`, with the published all-test centrality of
  [`Rational/Characters`](Characters.md).

Informally, `i` is the image of `φ`: this is the classical fact that over a field the image
of a homomorphism from a split torus to an affine group scheme is a closed split subtorus. The theorem also records that centrality passes from `φ` to its image, which uses
the flatness of everything over a field. The theorem asserts no uniqueness, and makes no claim
about `π` beyond the factorization.

## Proof

The proof is a Hopf-algebra argument written entirely in terms of group-valued functors on
`k`-algebras. It uses [`CorepresentedComultiplication`](../CorepresentedComultiplication.md)
and [`Torus/Diagonalizable`](../Torus/Diagonalizable.md).

1. **Coordinates.** The published adapter `AffineCoordinates.groupSchemeIso`
   ([`AffineCorepresented`](../AffineCorepresented.md)) presents `H` as a corepresented group
   scheme with coordinate algebra `A`. The split torus `D ≅ splitTorus I` is identified with
   `D(ℤ^I) = Spec k[ℤ^I]` by `Diagonalizable.splitIso`. Under these isomorphisms `φ` becomes a
   homomorphism `φ₀` of corepresented group schemes. Let `β := pointsTrans φ₀` be its natural
   transformation, so that `groupSchemeMap β = φ₀`.
2. **The classifying map.** `classifying e β : A ⟶ k[Λ]` (here `Λ = ℤ^I`) classifies the image
   of the universal character. By `classify_comul`, it intertwines the comultiplications.
3. **Coefficient extraction.** `extract γ : k[Λ] ⊗ k[Λ] → k[Λ]` is the linear map
   `p ⊗ q ↦ q_γ • p`. `extract_comul` shows that it sends the comultiplication of `p` to
   `p_γ • single γ 1`. `extract_tensorLift` shows that after `ψ ⊗ ψ` it factors through `ψ`.
   Hence (`coeff_smul_single_mem`) for every `a ∈ A` and every `γ`, the monomial term
   `ψ(a)_γ • single γ 1` lies in the range of `ψ`. Over a field, if this coefficient is nonzero,
   then `single γ 1` itself lies in the range (`mem_lattice_of_coeff_ne_zero`).
4. **The image lattice.** `latticeSubgroup e β` is the set of `γ` with `single γ 1` in the
   range of `ψ`. It contains `0` since `1 = single 0 1`, and it is closed under addition since
   `single γ 1 * single δ 1 = single (γ + δ) 1`. It is closed under negation by
   `classify_antipode` and `antipode_single`. `lattice e β` is the same subgroup as a
   `ℤ`-submodule `L`.
   `range_le_latticeIncl` and `latticeIncl_range_le` show that the range of `ψ` is exactly the
   image of the injective algebra map `latticeIncl : k[L] → k[Λ]`. The first expands `ψ(a)`
   into its monomials (step 3); the second uses that the range is a subalgebra. Hence `ψ`
   factors as `corestrict e β ≫ latticeIncl` with `corestrict` surjective (`corestrict_surjective`).
5. **The image homomorphism.** Over a field, `latticeIncl ⊗ latticeIncl` is injective
   (`tensorLift_injective`, from `TensorProduct.map_injective_of_flat_flat`). With `comul_incl`,
   this gives `corestrict_comul`: `corestrict` intertwines the comultiplications. Therefore
   `imageTrans e β : Hom(L, Sˣ) → H(S)`, `χ ↦ e(corestrict ≫ lift χ)`, is a natural group
   homomorphism (via `homEquiv_symm_mul`, using the published
   `Corepresented.LinearEmbedding.comul`). `restrict_imageTrans` proves that restriction to `L`
   followed by `imageTrans` is `β`. `classify_imageTrans` identifies its classifying map with
   `corestrict`, so `isClosedImmersion_imageTrans` follows from
   `IsClosedImmersion.spec_of_surjective`.
6. **Centrality.** `commute_imageTrans` assumes that every value of `β` commutes with all
   points of `H`, and proves the same for `imageTrans`. By naturality it suffices to treat the
   universal pair over `k[L] ⊗ A`: the universal character of `L` and the universal point of
   `H`. Pushing forward along the injective map `latticeIncl ⊗ id : k[L] ⊗ A → k[Λ] ⊗ A`
   (`tensorLift_injective` again) is injective on points of `H`. It turns the image of the
   universal character into a value of `β`, which commutes by hypothesis.
7. **Assembly.** `L` is a submodule of `ℤ^I`, hence free of finite rank
   (`Submodule.basisOfPid`). A basis indexed by `Fin n`, transported to `ULift (Fin n)`, gives
   `isSplitTorus` for `D' := D(L)`. Then `π` is `D ≅ D(ℤ^I)` followed by the restriction
   homomorphism `D(ℤ^I) → D(L)`, and `i` is `groupSchemeMap (imageTrans e β)` followed by
   `AffineCoordinates.groupSchemeIso`. The closed-immersion property, the factorization (by
   `groupSchemeMap_comp`, `restrict_imageTrans` and `groupSchemeMap_pointsTrans`), and the
   transfer of centrality (by `IsCentral.comp`, `IsCentral.comp_iso`,
   `IsCentral.commute_pointsTrans` and `isCentral_groupSchemeMap`) follow.

All other declarations are in `Langlands.GroupScheme.SplitTorusImage`; they are the
intermediate steps named above.

## Provenance

The statement is the standard structure of images of diagonalizable groups over a field: the
image of a split torus is a closed split torus whose character group is a sublattice. The
Lean proof is self-contained, using the published coordinate adapter and Mathlib's group
algebras, tensor products, flatness over fields, and submodules of free modules over a PID.
It is a prerequisite for the split-component arguments of tasks
`62edef35-527b-463b-99e8-144240046a95` (Levi split components) and
`fe540c1a-3c81-44ed-b16d-9acf125e1489` (existence and uniqueness of split components).
