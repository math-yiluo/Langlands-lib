# Vanishing of cohomology by induction on the dimension of the support

Author: Worker 921.

This helper module contains the main induction of the proof of
`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.Modules.NoetherianVanishing`.

- `isAffineHom_fromSpec [X.IsSeparated] (hV : IsAffineOpen V) : IsAffineHom hV.fromSpec`.
  The composite `Spec Γ(X, V) ⟶ X ⟶ ⊤_ Scheme` is a morphism of affine schemes, hence affine,
  and `X ⟶ ⊤_ Scheme` is separated. So Mathlib's `IsAffineHom.of_comp` applies.
- `isZero_relativeCohomology_pushforward_fromSpec [X.IsSeparated] (hV : IsAffineOpen V)
  (f : X ⟶ Spec R) (G : (Spec Γ(X, V)).Modules) [G.IsQuasicoherent] (q : ℕ)`:
  `IsZero ((DerivedSections.relativeCohomology f (q + 1)).obj (j_* G))`, where
  `j = hV.fromSpec`.
- `VanishesOn.bot`: every module vanishes on the empty open set, by the sheaf property for the
  empty cover (`TopCat.Sheaf.eq_of_locally_eq'`).
- `isZero_of_vanishesOn_top`: a module vanishing on `⊤` is zero.
- `isZero_relativeCohomology_of_isZero`: the cohomology of a zero module is zero. The proof
  writes the identity as the image of the zero morphism and uses the Library's
  `Langlands.Cohomology.DerivedPlus.rightDerived_map_zero`.
- `isZero_relativeCohomology_of_height [IsNoetherian X] [X.IsSeparated] (f : X ⟶ Spec R)
  (e : ℕ)`: for every closed `Z : Closeds X` and every `M : X.Modules` such that
  - `IsAffineLocallyQuasicoherent M` (module `QuasicoherentLocal.Closure`),
  - `VanishesOn M Z.compl` (`M` vanishes off `Z`, module `QuasicoherentLocal.Support`), and
  - `height T < e` for every irreducible closed `T ⊆ Z`,

  `IsZero ((DerivedSections.relativeCohomology f n).obj M)` holds for every `n ≥ e`.

## Proof of the pushforward vanishing

Write `j = hV.fromSpec`, an affine morphism by the first lemma. The Library's
`DerivedSections.isIso_pushforwardComparison` (module
`Langlands.AlgebraicGeometry.Modules.PushforwardComparison`) makes the comparison
`Hⁿ_R(Spec Γ(X, V), G) ⟶ Hⁿ_R(X, j_* G)` an isomorphism. It requires two inputs:

- vanishing of the higher direct images `R^(q+1) j_* G`, which is the Library's
  `AffineVanishing.isZero_higherDirectImage_of_isCechAcyclic` applied to
  `isCechAcyclic_of_isQuasicoherent G`;
- acyclicity of pushforwards of injective modules, which is the Library's
  `pushforwardInjectiveAcyclic`.

The source vanishes in positive degrees by the Library's
`affineQuasicoherentCohomologyVanishing` (module
`Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingProof`), applied to the
affine scheme `Spec Γ(X, V)` and the morphism `hV.fromSpec ≫ f`.

## Proof of the induction

The proof is an induction on `e`.

**Case `e = 0`.** No irreducible closed set has height `< 0`. The closure of a point of `Z`
would be one, so `Z` is empty. Then `M` vanishes on `⊤` and is zero, and so is its
cohomology.

**Case `e + 1`.** The proof is a noetherian induction on `Z`: `Closeds X` is well-founded,
because `X` is a noetherian space (Mathlib's `IsNoetherian.noetherianSpace`). Assume the
statement for every closed `Z' < Z` with the same bound `e + 1`. If `Z` is empty, `M` is
zero. Otherwise the steps are as follows.

1. `exists_irreducibleCloseds_inter_subset` gives an irreducible closed `T ⊆ Z`, an open `O₀`
   and a point `η ∈ O₀ ∩ Z` with `O₀ ∩ Z ⊆ T`. Choose an affine open `V` with
   `η ∈ V ⊆ O₀` (affine opens form a basis). Let `j = hV.fromSpec`, whose range is `V`.
2. Let `J = j_* (M.restrict j)` and let `φ = unitMap j M : M ⟶ J`. Factor `φ = p ≫ i`
   through its abelian image, with `p` an epimorphism and `i` a monomorphism (Mathlib's
   `Abelian.factorThruImage` and `Abelian.image.ι`). Then `kernel φ ≅ kernel p`
   (`kernelIsoOfEq` and `kernelCompMono`) and `cokernel φ ≅ cokernel i` (`cokernelIsoOfEq`
   and `cokernelEpiComp`).
3. Quasi-coherence. `M.restrict j` is quasi-coherent by the hypothesis on `M`, so `J` has the
   property by `IsAffineLocallyQuasicoherent.pushforward`. Hence `kernel p` and `cokernel i`
   have it, by `.kernel`, `.cokernel` and `.of_iso`.
4. The kernel. `kernel φ` vanishes off `Z` (since `M` does) and on `V`
   (`vanishesOn_kernel_unitMap`). So `kernel p` vanishes off `Z' = Z ∩ Vᶜ`, a closed set with
   `Z' < Z` because `η ∈ Z ∩ V`. Its irreducible closed subsets lie in `Z`, so the noetherian
   induction hypothesis gives `H^(m+1)(kernel p) = 0`.
5. The cokernel. For `W` disjoint from `T`, `j ''ᵁ j ⁻¹ᵁ W = V ⊓ W` is disjoint from `Z`,
   because `V ∩ Z ⊆ O₀ ∩ Z ⊆ T`. So `J` vanishes off `T` (`vanishesOn_pushforward_restrict`),
   and so does `cokernel φ` (`VanishesOn.cokernel_of_right`). Also `cokernel φ` vanishes on
   `V` (`vanishesOn_cokernel_unitMap`). Hence `cokernel i` vanishes off `T' = T ∩ Vᶜ`. An
   irreducible closed `T'' ⊆ T'` misses `η ∈ T`, so
   `height T'' + 1 ≤ height T ≤ e` (`height_add_one_le_of_subset`), that is,
   `height T'' < e`. The outer induction hypothesis at `e` gives `H^m(cokernel i) = 0` for
   `m ≥ e`.
6. `H^(m+1)(J) = 0` by `isZero_relativeCohomology_pushforward_fromSpec`.
7. Cohomology, with `n = m + 1 ≥ e + 1`. The short exact sequences
   `0 ⟶ kernel p ⟶ M ⟶ image ⟶ 0` and `0 ⟶ image ⟶ J ⟶ cokernel i ⟶ 0` (exact by
   `ShortComplex.exact_of_f_is_kernel` and `exact_of_g_is_cokernel`) give exact sequences
   from the Library's `Langlands.Cohomology.DerivedPlus.rightDerived_exact₁` and
   `rightDerived_exact₂`:
   - `H^m(cokernel i) ⟶ H^(m+1)(image) ⟶ H^(m+1)(J)` has zero ends, so
     `H^(m+1)(image) = 0`;
   - `H^(m+1)(kernel p) ⟶ H^(m+1)(M) ⟶ H^(m+1)(image)` has zero ends, so
     `H^(m+1)(M) = 0`.

   The middle term of an exact sequence with zero outer maps is zero
   (`ShortComplex.Exact.isZero_X₂_iff`).

## Provenance

This is an internal proof route. It proves the quasi-coherent case of Grothendieck's vanishing
theorem (Stacks Tag 02UZ) differently from the source. The source works with arbitrary abelian
sheaves and uses extension by zero and the sheaves `j_! ℤ_U`. This route stays inside
quasi-coherent modules: it uses the unit `M ⟶ j_*(M|_V)` for an affine open `V`, affine
vanishing and the affine pushforward comparison. That is why it needs `X` separated (so that
`V ⟶ X` is affine) and the quasi-coherence hypothesis.
