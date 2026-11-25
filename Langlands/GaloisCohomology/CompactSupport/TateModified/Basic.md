# Cohomology with compact support modified at a family of finite groups

`Langlands/GaloisCohomology/CompactSupport/TateModified/Basic.lean`, namespace `Langlands.GaloisCohomology`.

In addition to the family `(φ_v : H_v →ₜ* G)`, let `(ψ_w : F_w →ₜ* G)` be a family of finite groups
with modules `A_w` (for `G_S`: the decomposition groups `Gal(ℂ/ℝ)` at the real places). The global
term of the cocone becomes `C•(G, A) × ∏_w A_w` (the second factor in degree `0`) and the map to
the local term adds the norm cochains `m_w ↦ N_{F_w} m_w`; its cocone `tateCompactCochains` has
cohomology `Ĥ_c^n(G, A)`, in which degree `0` at the `F_w` is Tate's `Ĥ⁰` (`cohomologyTateZero`). The
long exact sequence `⋯ → Ĥ_c^n → Hⁿ(G) → ∏_v Hⁿ(H_v) × ∏_w Hⁿ(F_w) → Ĥ_c^{n+1} → ⋯` (for `n ≥ 1`;
in degree `0` with `H⁰(G) × ∏_w A_w`), the functoriality in the module and the connecting map of a
short exact sequence are proved as for ordinary compact support.

```lean
noncomputable def normClasses (A : Rep k G) [IsSmoothRep A] : Submodule k (cohomology A 0)
abbrev cohomologyTateZero (A : Rep k G) [IsSmoothRep A] : Type u
noncomputable def tateCompactRes : tateGlobalComplex A Aᵣ ⟶ tateLocalComplex Aᵥ Aᵣ
noncomputable def tateCompactCochains : CochainComplex (ModuleCat.{u} k) ℕ
noncomputable def tateCompactCohomology (n : ℕ) : ModuleCat.{u} k
noncomputable def tateGlobalToLocal (n : ℕ) :
    cohomology A n ⟶ ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n))
noncomputable def tateToGlobal (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ cohomology A n
noncomputable def tateLocalToCompact (n : ℕ) :
    ModuleCat.of k ((∀ v, cohomology (Aᵥ v) n) × (∀ w, cohomology (Aᵣ w) n)) ⟶
      tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1)
noncomputable def tateCompactδ (hS : S.ShortExact) (hSᵥ : ∀ v, (Sᵥ v).ShortExact)
    (hSᵣ : ∀ w, (Sᵣ w).ShortExact) (n : ℕ) :
    tateCompactCohomology φ ψ S.X₃ (fun v => (Sᵥ v).X₃) (fun v => (s v).τ₃) (fun w => (Sᵣ w).X₃)
        (fun w => (sr w).τ₃) n ⟶
      tateCompactCohomology φ ψ S.X₁ (fun v => (Sᵥ v).X₁) (fun v => (s v).τ₁)
        (fun w => (Sᵣ w).X₁) (fun w => (sr w).τ₁) (n + 1)
```

## Outline of the proofs

As for `Basic.lean` and `Functoriality.lean`: the long exact sequence of the cocone of
`tateCompactRes`, with the homology of the product complexes computed factorwise
(`prodHomologyIso`) and that of the complex concentrated in degree `0` explicitly
(`degZeroHomologyIso`); in degree `0` the norm cochains identify the cokernel with Tate's `Ĥ⁰`.

## Declarations

`normClasses`, `mem_normClasses_iff`, `cohomologyTateZero`, `prodComplex`, `prodComplex_d`, `prodComplex_d_hom_apply`, `prodComplex_d_hom_apply'`, `prodFst`, `prodSnd`, `prodLift`, `prodLift_prodFst`, `prodLift_prodSnd`, `prodMapCx`, `degZeroX`, `degZeroComplex`, `degZeroComplex_d`, `zeroCochain`, `cochainOf_zeroCochain`, `cochainOf_d_zeroCochain`, `d_zeroCochain_norm`, `normCochainsF`, `normCochainsF_zero_apply`, `normCochains`, `tateGlobalComplex`, `tateLocalComplex`, `tateCompactRes`, `tateCompactCochains`, `tateCompactCohomology`, `tateCompactCohomologyRes`, `prodHomologyToProd`, `prodHomologyToProd_bijective`, `prodHomologyIso`, `isIso_homologyMap_prodFst`, `isZero_degZeroComplex_homology_succ`, `degZeroHomologyIso`, `degZeroHomologyIso_hom_homologyπ`, `tateLocalCohomologyIso`, `tateLocalCohomologyIso_hom_apply`, `tateGlobalCohomologyIso`, `tateGlobalCohomologyIso_hom`, `tateGlobalCohomologyZeroIso`, `tateGlobalCohomologyZeroIso_hom_apply`, `tateCompactRes_prodFst`, `tateCompactRes_prodSnd`, `tateGlobalToLocal`, `tateGlobalToLocal_hom_apply`, `homologyMap_tateCompactRes_succ`, `tateToGlobal`, `tateLocalToCompact`, `tateToGlobal_succ`, `tateToGlobal_tateGlobalToLocal`, `tateGlobalToLocal_tateLocalToCompact`, `tateLocalToCompact_tateToGlobal`, `tateCompactCohomology_exact_global`, `tateCompactCohomology_exact_local`, `tateCompactCohomology_exact_compact`, `tateToGlobalZero`, `tateGlobalZeroToLocal`, `tateToGlobalZero_tateGlobalZeroToLocal`, `tateGlobalZeroToLocal_tateLocalToCompact`, `tateCompactCohomology_exact_localZero`, `normClass`, `localCohomologyIso_homologyMap_normCochains`, `tateGlobalZeroToLocal_hom_apply`, `degZeroMapF`, `degZeroMap`, `degZeroMap_f_zero_apply`, `degZeroMap_id`, `degZeroMap_comp`, `degZeroShortComplex`, `degZeroShortComplex_shortExact`, `prodShortComplex`, `prodShortComplex_shortExact`, `homologyMap_prodMapCx_prodHomologyIso_hom`, `piRepHom`, `piRepHom_apply`, `piRepShortComplex`, `piRepShortComplex_shortExact`, `normCochains_naturality`, `tateGlobalMap`, `tateLocalMap`, `tateCompactRes_naturality`, `tateCompactCochainsMap`, `tateCompactCohomologyMap`, `tateCompactCohomologyMap_id`, `tateCompactCohomologyMap_comp`, `tateCompactCohomologyMap_tateToGlobal`, `cohomologyMap_tateGlobalToLocal`, `homologyMap_tateLocalMap_tateLocalCohomologyIso_hom`, `tateLocalToCompact_tateCompactCohomologyMap`, `tateGlobalShortComplex`, `tateLocalShortComplex`, `tateResShortComplex`, `tateCompactCochainsMap₁₂`, `tateCompactCochainsMap₂₃`, `tateCompactCohomologyMap₁₂`, `tateCompactCohomologyMap₂₃`, `tateCompactCochainsMap₁₂_₂₃`, `tateCompactCohomologyMap_f_g`, `mapShortComplex_tateResShortComplex_f`, `mapShortComplex_tateResShortComplex_g`, `tateCompactCochains_shortExact`, `tateCompactδ`, `tateCompactCohomologyMap₂₃_tateCompactδ`, `tateCompactδ_tateCompactCohomologyMap₁₂`, `tateCompactCohomology_exact₂`, `tateCompactCohomology_exact₃`, `tateCompactCohomology_exact₁`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/ConeDefs.lean`, `RealPlaces/LocalCohomologyIsoHomologyMapNormCochains.lean`, `RealPlaces/ConeMap.lean` and the section `TateZero` of `RealPlaces/LocalDualityDefs.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. The norm classes are defined with the Library's `Langlands.Tate.normImage`. The source states this layer for `Type`; here it is stated for `Type u`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6: Theorem (8.6.9), p. 488 (the pairing of `Ш¹` and `Ш²`), and (8.6.10), pp. 489–490 (the nine-term sequence of Poitou–Tate, with Tate's modified groups at the archimedean places in `P⁰`).
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr. Mathematicians (Stockholm 1962), Inst. Mittag-Leffler 1963, pp. 288–295: §1, p. 288 (at the real and complex places `Hʳ` is Tate's modified cohomology `Ĥʳ`), and Theorem 3.1, p. 291 (the perfect pairing of `Ker²(k_S, M)` and `Ker¹(k_S, M')`, the nine-term exact sequence, `Hʳ(k_S, M) ≅ ∏_{P real} Hʳ(k_P, M)` for `r ≥ 3`).
