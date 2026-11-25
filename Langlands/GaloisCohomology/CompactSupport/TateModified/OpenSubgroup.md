# Tate-modified compact support and open subgroups

`Langlands/GaloisCohomology/CompactSupport/TateModified/OpenSubgroup.lean`, namespace `Langlands.GaloisCohomology`.

Forgetting the finite groups gives `Ĥ_c^n(G, A) → H_c^n(G, A)` (`tateForget`), an isomorphism when
the local modules at the `F_w` are cohomologically trivial with invariants the norms
(`tateForgetIso`). For an open subgroup `U` meeting the conjugates of the `F_w` trivially
(`FreeOnCosets`) the coinduced modules have no cohomology at the `F_w`, which gives
`Ĥ_c^{n+1}(G, Coind_U^G N) ≅ H_c^{n+1}(U, N)` (`tateCoindIso`) and the corestriction
`tateCompactCores`.

```lean
noncomputable def tateForget (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar n ⟶ compactSupportCohomology φ A Aᵥ a n
noncomputable def tateForgetIso (hcoh : ∀ w n, IsZero (cohomology (Aᵣ w) (n + 1)))
    (hnorm : ∀ w, ∀ x ∈ (Aᵣ w).ρ.invariants, ∃ m, (Aᵣ w).ρ.norm m = x) (n : ℕ) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar (n + 1) ≅ compactSupportCohomology φ A Aᵥ a (n + 1)
def FreeOnCosets (U : Subgroup G) : Prop
noncomputable def tateCoindIso (hU : FreeOnCosets ψ (U : Subgroup G)) (n : ℕ) :
    tateCompactCohomologyRes φ ψ (Rep.coind (U : Subgroup G).subtype N) (n + 1) ≅
      compactSupportCohomology (mackeyFamily U φ) N (mackeyCoeff U φ N) (fun _ => 𝟙 _) (n + 1)
noncomputable def tateCompactCores (hU : FreeOnCosets ψ (U : Subgroup G)) (A : Rep.{u} k G)
    [IsSmoothRep A] (n : ℕ) :
    compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype A) (n + 1) ⟶
      tateCompactCohomologyRes φ ψ A (n + 1)
```

## Outline of the proofs

The modified and the ordinary cocones sit in a morphism of short exact sequences whose
third terms are the complexes `∏_w A_w` and `∏_w C•(F_w, A_w)`; under the hypotheses of
`tateForgetIso` the norm map identifies them in homology, and the five lemma applies. For
`U` free on the cosets, the restriction of `Coind_U^G N` to each `F_w` is coinduced from the trivial
group, hence satisfies these hypotheses (`subsingletonCoindIso`).

## Declarations

`tateForgetCochains`, `tateForget`, `tateForget_compactToGlobal`, `tateLocalFst`, `tateLocalCohomologyIso_inv_homologyMap_prodFst`, `tateLocalToCompact_tateForget`, `prodInr`, `prodInr_f_hom_apply`, `prodSeq`, `prodSeq_shortExact`, `exists_normClass_eq`, `normCochains_prodInr`, `tateResSeqHom`, `tateForgetShortComplex_shortExact`, `isZero_homology_normCocone`, `isIso_tateForget`, `tateForgetIso`, `subsingletonCoindIso`, `isZero_cohomology_succ_of_subsingleton`, `InOutCoset`, `doubleCosetMk_mul_left`, `inOutCoset_mul_left_iff`, `exists_norm_eq_res_coind`, `FreeOnCosets`, `isZero_cohomology_res_coind`, `exists_norm_eq_res_coind'`, `tateCoindIso`, `tateCoindIso_hom`, `tateCompactCores`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/InducedDefs.lean`, `RealPlaces/InducedDropOut.lean` and `RealPlaces/Induced.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
