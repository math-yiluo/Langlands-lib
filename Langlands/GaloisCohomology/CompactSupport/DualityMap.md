# The duality map of cohomology with compact support

`Langlands/GaloisCohomology/CompactSupport/DualityMap.lean`, namespace `Langlands.GaloisCohomology`.

For a dualizing module `D` with a trace `t : H_c^m(G, D) → ℤ/n`, the duality map
`Hʳ(G, Hom(M, D)) → Hom(H_c^s(G, M), ℤ/n)` (`r + s = m`) is the cup product with evaluation followed
by `t` (`compactDualityMap`). This file defines it with the cup product `compactCupRes` (local
modules the restrictions), corestriction `compactCores` from an open subgroup, the hypothesis
structure `CompactDualityHypotheses` of the duality theorem, the functoriality of `H_c` in the
module (`compactSupportCohomologyResMap`) and the naturality of the duality map, and its
bijectivity for direct sums and biproducts.

```lean
noncomputable def compactCupRes {A B C : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]
    [IsSmoothRep C] (μ : A ⊗ B ⟶ C) {r s n : ℕ} (h : r + s = n) :
    compactSupportCohomologyRes φ A r →ₗ[k] cohomology B s →ₗ[k] compactSupportCohomologyRes φ C n
def compactDualityMap (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : compactSupportCohomologyRes φ D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] :
    cohomology M r →+ (compactSupportCohomologyRes φ (dualRep D M) s →+ ZMod n)
noncomputable def compactCores (V : OpenSubgroup G) (A : Rep.{u} k G) [IsSmoothRep A] (n : ℕ) :
    compactSupportCohomologyRes (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n ⟶
      compactSupportCohomologyRes φ A n
def zmodCompactDualityMap (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0) (U : OpenSubgroup G) {m r s : ℕ} (h : r + s = m)
    (t : compactSupportCohomologyRes φ D m →+ ZMod n) :
    cohomology (zmodRep.{u} (U : Subgroup G) n) r →+
      (compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) s →+ ZMod n)
   
structure CompactDualityHypotheses (n : ℕ) (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
    (t : compactSupportCohomologyRes φ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- `H_c^4` vanishes for finite modules killed by `n`. -/
  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (compactSupportCohomologyRes φ M 4)
  /-- The duality map for `ℤ/n` is bijective over every open subgroup below `U₀`. -/
  bijective_base : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3),
    Function.Bijective (zmodCompactDualityMap φ D
      (nsmul_eq_zero_of_nonempty_addEquiv nonempty_addEquiv) U h t)
theorem bijective_compactDualityMap_of_sum {J : Type*} [Fintype J] (X : J → Rep.{u} k G)
    [∀ j, IsSmoothRep (X j)] [∀ j, IsSmoothRep (dualRep D (X j))] (P : Rep.{u} k G)
    [IsSmoothRep P] [IsSmoothRep (dualRep D P)] (i : ∀ j, X j ⟶ P) (p : ∀ j, P ⟶ X j)
    (hsum : ∑ j, p j ≫ i j = 𝟙 P)
    (hX : ∀ j, Function.Bijective (compactDualityMap φ D h t (X j))) :
    Function.Bijective (compactDualityMap φ D h t P)
```

`zmodMulPairingRight_res θ n hD' hD f`: restriction along a topological isomorphism `θ : G ≃ₜ* G'`
carries the multiplication pairing `D' ⊗ ℤ/n → D'` (`zmodMulPairingRight`) to that of `D`, through a
morphism `f : Res_θ D' ⟶ D` and `zmodRepResIso`.

Its complete type, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.zmodMulPairingRight_res.{u} {G G' : Type u} [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] (θ : G ≃ₜ* G') (n : ℕ) {D' : Rep.{u, u, u} (ULift.{u, 0} ℤ) G'}
  {D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} (hD' : ∀ (d : ↑D'), n • d = 0) (hD : ∀ (d : ↑D), n • d = 0)
  (f : Rep.res (↑θ) D' ⟶ D) :
  CategoryTheory.CategoryStruct.comp ((Rep.resFunctor ↑θ).map (Langlands.GaloisCohomology.zmodMulPairingRight n D' hD'))
      f =
    CategoryTheory.CategoryStruct.comp
      (Langlands.ProfiniteCohomology.resTensorHom (↑θ) f (Langlands.ProfiniteCohomology.zmodRepResIso θ n).hom)
      (Langlands.GaloisCohomology.zmodMulPairingRight n D hD)
```

## Outline of the proofs

The duality map is the composite of the cup product `compactCupRes` with evaluation
(`dualEvalPairing`) and the trace. Naturality in `M` (`compactDualityMap_cohomologyMap`) follows from
the naturality of the Leibniz pairings of cup products (`LeibnizPairing.homology_homologyMap`,
`compactCupRes_compactSupportCohomologyResMap`); bijectivity for a direct sum follows from the
decomposition of the identity by the projections and inclusions.

## Declarations

``CompactDualityHypotheses``, `dualEvalPairing`, `dualEvalPairing_tmul`, `resFunctor_map_comp_id`, `compactCupRes`, `compactDualityMap`, `compactDualityMap_apply`, `isSmoothRep_resHom_coind_res`, `compactCores`, `zmodMulPairingRight`, `zmodCompactDualityMap`, `zmodCompactDualityMap_apply`, `CompactDualityHypotheses`, `LeibnizPairing.homology_homologyMap`, `compactSupportCochainsResMap`, `compactSupportCohomologyResMap`, `compactSupportCochainsResMap_add`, `compactSupportCochainsResMap_zero`, `compactSupportCochainsResMap_id`, `compactSupportCochainsResMap_comp`, `compactSupportCohomologyResMap_add`, `compactSupportCohomologyResMap_zero`, `compactSupportCohomologyResMap_id`, `compactSupportCohomologyResMap_comp`, `compactSupportCohomologyResMap_finsetSum`, `nsmul_compactSupportCohomologyRes_eq_zero`, `cupCochain_naturality`, `resFunctor_map_naturality`, `compactCupResLeibniz`, `compactCupRes_eq_homology`, `compactCupRes_compactSupportCohomologyResMap`, `tensorHom_dualEvalPairing`, `compactDualityMap_cohomologyMap`, `bijective_compactDualityMap_of_sum`, `bijective_compactDualityMap_biproduct`, `zmodMulPairingRight_res`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/PoincarePairs/IsDiscreteRepResHomCoindRes.lean` and `PoincarePairs/Natural.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
