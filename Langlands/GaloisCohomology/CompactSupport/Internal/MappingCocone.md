# The mapping cocone of `ℕ`-indexed complexes (internal)

`Langlands/GaloisCohomology/CompactSupport/Internal/MappingCocone.lean`, namespace
`Langlands.GaloisCohomology`. Internal: no stability promise.

For a morphism `f : K ⟶ L` of `ℕ`-indexed cochain complexes of `k`-modules, the shifted complex
`L[-1]` has `0` in degree `0` and `L^n` in degree `n + 1` with differential `-d_L`, and the mapping
cocone `Cocone(f) = K ⊕ L[-1]` has differential `(x, y) ↦ (d x, f x - d y)`. The elements are
explicit pairs, because the cup products on cones (`Internal/LeibnizPairing.lean`,
`Internal/ConeSigns.lean`) are written on them.

```lean
noncomputable def mappingCoconeNat {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) :
    CochainComplex (ModuleCat.{u} k) ℕ
noncomputable def mappingCoconeNat.homologyδ (n : ℕ) : L.homology n ⟶ (mappingCoconeNat f).homology (n + 1)
theorem mappingCoconeNat.homology_exact₁ (n : ℕ) :          -- Hⁿ(K) ⟶ Hⁿ(L) ⟶ H^{n+1}(Cocone f)
    (ShortComplex.mk _ _ (homologyMap_homologyδ f n)).Exact
theorem mappingCoconeNat.homology_exact₂ (n : ℕ) :          -- Hⁿ(L) ⟶ H^{n+1}(Cocone f) ⟶ H^{n+1}(K)
    (ShortComplex.mk _ _ (homologyδ_homologyMap_fst f n)).Exact
theorem mappingCoconeNat.homology_exact₃ (n : ℕ) :          -- Hⁿ(Cocone f) ⟶ Hⁿ(K) ⟶ Hⁿ(L)
    (ShortComplex.mk _ _ (homologyMap_fst_homologyMap f n)).Exact
noncomputable def piComplex (K : ι → CochainComplex (ModuleCat.{u} k) ℕ) : CochainComplex (ModuleCat.{u} k) ℕ
noncomputable def piHomologyIso (n : ℕ) : (piComplex K).homology n ≅ ModuleCat.of k (∀ v, (K v).homology n)
```

## Outline of the proofs

- `L[-1] ⟶ Cocone(f) ⟶ K` is degreewise split exact (`mappingCoconeNat.shortExact`). Its connecting
  map is `Hⁿ(f)` followed by the isomorphism `shiftNegOneHomologyHom : Hⁿ(L) ⟶ H^{n+1}(L[-1])`
  (`δ_eq`), computed with Mathlib's `ShortExact.δ_eq` on the lift `x ↦ (x, 0)`. The long exact
  sequence of Mathlib then gives the three exactness statements after replacing
  `H^{n+1}(L[-1])` by `Hⁿ(L)`. In degree `0`, `L[-1]` is zero, so `H⁰(Cocone f) ⟶ H⁰(K)` is a
  monomorphism.
- A commutative square `f ≫ β = α ≫ f'` induces `map α β w` on cocones, compatible with the
  projections, the inclusions and the connecting maps; a morphism of short exact sequences of
  morphisms gives a short exact sequence of cocones (`shortExact_mapShortComplex`, checked
  degreewise on pairs).
- The homology of a product of complexes is the product of the homologies: the comparison map is
  bijective by choosing preimages factorwise (`piHomologyToPi_bijective`); products of short exact
  sequences are short exact.

## Declarations

- Shift: `shiftNegOneX`, `shiftNegOneD`, `shiftNegOneD_succ_apply`, `shiftNegOneD_comp`,
  `shiftNegOneD_shiftNegOneD_apply`, `shiftNegOne`, `shiftNegOne_d`, `shiftNegOneSucc`,
  `shiftNegOneSucc_apply`, `shiftNegOneSuccHom` (an isomorphism), `shiftNegOne_d_succ_hom_apply`,
  `shiftNegOneSuccHom_d`, `prevNat`, `up_prev_eq_prevNat`, `shiftNegOneτ₁`, `shiftNegOneψ`,
  `epi_shiftNegOneτ₁`, `mono_neg_shiftNegOneSuccHom`, `shiftNegOneHomologyHom`,
  `isIso_shiftNegOneHomologyHom`, `shiftNegOneHomologyIso`, `shiftNegOneHomologyIso_inv`,
  `shiftNegOneHomologyIso_symm_hom`, `iCycles_shiftNegOneSuccHom_d`,
  `homologyπ_shiftNegOneHomologyHom`.
- Cocone: `mappingCoconeNatX`, `mappingCoconeNatD`, `mappingCoconeNatD_apply`,
  `mappingCoconeNatD_comp`, `mappingCoconeNat`, `mappingCoconeNat_d`, `mappingCoconeNat.fst`,
  `mappingCoconeNat.inr`; in namespace `mappingCoconeNat`: `inr_fst`, `shortComplex`, `shortExact`,
  `inlX`, `inlX_fst`, `inlX_d`, `δ_eq`, `homologyδ`, `homologyMap_homologyδ`,
  `homologyδ_homologyMap_fst`, `homologyMap_fst_homologyMap`, `homology_exact₁`,
  `homology_exact₂`, `homology_exact₃`, `mono_homologyMap_fst_zero`.
- Maps: `shiftNegOneMapF`, `shiftNegOneMapF_succ_apply`, `shiftNegOneMapF_comm`, `shiftNegOneMap`,
  `shiftNegOneSuccHom_shiftNegOneMap_f`, `shiftNegOneMap_id`, `shiftNegOneHomologyHom_naturality`;
  `mappingCoconeNat.mapF`, `mapF_comm`, `map`, `map_id`, `map_comp`, `map_fst`, `inr_map`,
  `homologyδ_naturality`, `mapShortComplex`, `shortExact_mapShortComplex`.
- Products: `piComplex`, `piComplex_d`, `piComplex_d_hom_apply`, `piComplex_d_hom_apply'`, `piLift`,
  `piProj`, `piProj_f_hom_apply`, `piLift_piProj`, `piHomologyToPi`, `piHomologyToPi_hom_apply`,
  `piHomologyToPi_bijective`, `piHomologyIso`, `piHomologyIso_hom_apply`,
  `homologyMap_piLift_piHomologyIso_hom`, `piMap`, `piLift_piMap`, `piMap_piProj`,
  `homologyMap_piMap_piHomologyIso_hom`, `piShortComplex`, `piShortComplex_shortExact`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files under
`src/GroundTheory/ProfiniteCohomology/`: `CompactSupportCohomology/HomApplyHomApplyEqOfCompEq.lean`
(lines 22–167; the two evaluation lemmas of lines 11–20 are the foundations'
`hom_apply_hom_apply_of_comp_eq`, `hom_apply_hom_apply_eq_of_comp_eq`),
`CompactSupportCohomology/ShiftNegOneHomologyIsoSymmHom.lean`, `CompactSupportCohomology/ConeMap.lean`,
`CompactSupportCohomology/HomologyMapPiLiftPiHomologyIsoHom.lean` and the section `PiMap` of
`CompactSupportCohomology.lean` (lines 13–82). The repository has no licence file; its text is used
with attribution (`licenses/RiemannHypothesis/SOURCE.md`).
Names are the source's; the four files named after a lemma are merged into one file named for its
content. The source's `FilteredHomology` lemmas are the foundations'
(`Langlands/Cohomology/Profinite/Comparison/FilteredHomology.lean`).

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2,
  pp. 165–166 (cohomology with compact support defined as the translate `C•(u)[-1]` of the mapping
  cone of `u : C•(U, F) → ⊕_v S•(M_v)`, and its long exact sequences, Proposition 2.3 (a), (b)).
