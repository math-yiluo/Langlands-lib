# The duality theorem for cohomology with compact support

`Langlands/GaloisCohomology/CompactSupport/Duality.lean`, namespace `Langlands.GaloisCohomology`.

Dévissage: under `CompactGroupDualityHypotheses` (`D ≅ ℤ/n`, `H_c^4 = 0` for modules killed by `n`,
duality for the modules coinduced from `ℤ/n` on open subgroups below `U₀`) the duality map
`Hʳ(G, Hom(M, D)) → Hom(H_c^s(G, M), ℤ/n)` (`r + s = 3`) is bijective for every finite smooth
module `M` killed by `n` (`CompactGroupDualityHypotheses.bijective_compactDualityMap`), by
induction on the degree through the long exact sequences of an embedding of `M` into a sum of
coinduced modules. With Shapiro's lemma and corestriction the coinduced case reduces to `ℤ/n` over
open subgroups, which gives the theorem from `CompactDualityHypotheses`
(`CompactDualityHypotheses.bijective_compactDualityMap`).

```lean
structure CompactGroupDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep D] (t : compactSupportCohomologyRes φ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- `H_c^4` vanishes for finite modules killed by `n`. -/
  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (compactSupportCohomologyRes φ M 4)
  /-- The duality map is bijective for the modules coinduced from `ℤ/n` on open subgroups below `U₀`. -/
  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3),
    Function.Bijective (compactDualityMap φ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))
theorem CompactGroupDualityHypotheses.bijective_compactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t M)
theorem CompactDualityHypotheses.bijective_compactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactDualityMap φ D h t M)
```

Variables: `G` compact, `H_v` compact, `ι` finite, `n ≠ 0`, `D : Rep.{u} (ULift.{u} ℤ) G` smooth, `t : compactSupportCohomologyRes φ D 3 →+ ZMod n`, `U₀ : OpenSubgroup G`.

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@compactCores_mackeyCompactCohomologyIso : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] {ι : Type u_1} {Hv : ι → Type u_1}
  [inst_4 : (v : ι) → Group (Hv v)] [inst_5 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [inst_7 : ∀ (v : ι), CompactSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  {k : Type u_1} [inst_8 : CommRing k] (V : OpenSubgroup G) (A : Rep.{u_1, u_1, u_1} k G)
  [inst_9 : Langlands.IsSmoothRep A] (m : ℕ)
  (w : ↑(compactSupportCohomologyRes φ (Rep.coind.{u_1, u_1, u_1, u_1} (↑V).subtype (Rep.res (↑V).subtype A)) m)),
  (ModuleCat.Hom.hom (compactCores φ V A m))
      ((ModuleCat.Hom.hom (mackeyCompactCohomologyIso V φ (Rep.res (↑V).subtype A) m).hom) w) =
    (ModuleCat.Hom.hom (compactSupportCohomologyResMap φ (Langlands.ProfiniteCohomology.coindTrace (↑V) A) m)) w

@CompactGroupDualityHypotheses.bijective_compactDualityMap : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] {ι : Type u_1}
  {Hv : ι → Type u_1} [inst_4 : (v : ι) → Group (Hv v)] [inst_5 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (Hv v)] {φ : (v : ι) → Hv v →ₜ* G} {n : ℕ} [inst_7 : NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_8 : Langlands.IsSmoothRep D]
  {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n} {U₀ : OpenSubgroup G},
  CompactGroupDualityHypotheses φ n D t U₀ →
    ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
      (∀ (m : ↑M), n • m = 0) → ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective ⇑(compactDualityMap φ D h t M)

@CompactDualityHypotheses.bijective_compactDualityMap : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] {ι : Type u_1} {Hv : ι → Type u_1}
  [inst_4 : (v : ι) → Group (Hv v)] [inst_5 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [inst_7 : ∀ (v : ι), CompactSpace (Hv v)] {φ : (v : ι) → Hv v →ₜ* G}
  {n : ℕ} [NeZero n] {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_9 : Langlands.IsSmoothRep D]
  {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n} {U₀ : OpenSubgroup G},
  CompactDualityHypotheses φ n D t U₀ →
    ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_10 : Langlands.IsSmoothRep M] [inst_11 : Finite ↑M],
      (∀ (m : ↑M), n • m = 0) → ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective ⇑(compactDualityMap φ D h t M)
```

## Outline of the proofs

Dévissage (`CompactGroupDualityHypotheses.exists_devissage`): a finite smooth module `M`
killed by `n` embeds into a finite sum of modules `Coind_U^G(ℤ/n)` with `U ≤ U₀`
(`exists_injective_biproduct_coind_le`), with cokernel again finite and killed by `n`. The duality
maps of the long exact sequences commute up to sign with the connecting maps (`compactDualityMap_δ`),
so induction on the degree, starting from `r = 0` (injectivity and surjectivity are proved
separately, `injective_zero`, `surjective_zero`) and using `H_c^4 = 0`, gives bijectivity in all
degrees (`bijective_succ`). For `CompactDualityHypotheses`, the duality map of `Coind_U^G(ℤ/n)` is
that of `ℤ/n` over `U` (Shapiro with compact support, corestriction: `compactDualityMap_coind`).

## Declarations

`isSmoothRep_map_resFunctor_X₁`, `isSmoothRep_map_resFunctor_X₂`, `isSmoothRep_map_resFunctor_X₃`, `compactSupportδRes`, `compactRes_exact₂`, `compactRes_exact₃`, `compactRes_exact₁`, `eq_zero_of_neg_neg_one_pow_zsmul`, `neg_neg_one_pow_zsmul_zsmul`, `map_eq_of_add_neg_one_pow_smul_eq_zero`, `compactDualityMap_δ`, `exists_injective_biproduct_coind_le`, `CompactGroupDualityHypotheses`, `finite_D`, `nsmul_D`, `exists_devissage`, `injective_zero`, `surjective_zero`, `bijective_zero`, `injective_succ`, `surjective_succ`, `bijective_succ`, `bijective_compactDualityMap`, `LeibnizPairing.homologyMap_homology`, `compactSupportCohomologyResMap_compactCupRes`, `bijective_compactSupportCohomologyResMap_of_comp_eq_id`, `compactCores_mackeyCompactCohomologyIso`, `tensorHom_coindDualHom_dualEvalPairing`, `tensorHom_zmodDualIso_zmodMulPairingRight`, `coindDualCompactMap`, `bijective_coindDualCompactMap`, `compactDualityMap_coind`, `bijective_compactDualityMap_coind`, `compactGroupDualityHypotheses`, `bijective_compactDualityMap`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/PoincarePairs/Devissage.lean` and `PoincarePairs.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
