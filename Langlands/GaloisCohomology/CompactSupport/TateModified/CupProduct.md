# Cup products with Tate-modified compact support

`Langlands/GaloisCohomology/CompactSupport/TateModified/CupProduct.lean`, namespace `Langlands.GaloisCohomology`.

The cup product `Ĥ_c^r(G, A) × Hˢ(G, B) → Ĥ_c^{r+s}(G, C)` (`tateCompactCup`): the pairing on the
modified cocone is the cone pairing of `Internal/ConeSigns.lean` corrected by a homotopy, because
the norm cochains are compatible with cup products only up to the homotopy `normHomotopy`. The
cup product is compatible with the connecting maps of two short exact sequences, as in
`CupProduct.lean`.

```lean
noncomputable def LeibnizPairing.coconeLeftHtpy
    (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
      shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
        shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
          η (by omega) ((K.d r (r + 1)).hom x) z +
          (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f')
noncomputable def normHomotopy {s m : ℕ} (h : s = m + 1) :
    X →ₗ[k] (cochains Y).X s →ₗ[k] (cochains Z).X m
noncomputable def tateCompactCup {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar r →ₗ[k] cohomology B s →ₗ[k]
      tateCompactCohomology φ ψ C Cᵥ c Cᵣ cr n
```

## Outline of the proofs

The norm cochains commute with cup products only up to the homotopy `normHomotopy`
(the norm of `a ∪ b` against `N(a) ∪ b`), so the cone pairing is built with `coconeLeftHtpy`, which
allows a homotopy in the compatibility condition; the Leibniz rule is checked on components, and
the compatibility with connecting maps is `LeibnizPairing.homology_δ_add_homology_δ` for the
modified cone pairings.

## Declarations

`prod`, `prod_μ_apply`, `prodLeft`, `prodLeft_μ_apply`, `degZeroμ`, `degZeroμ_succ`, `degZero`, `coconeLeftHtpyμ`, `coconeLeftHtpyμ_apply`, `coconeLeftHtpy`, `coconeLeftHtpy_homology_homologyδ`, `consTuple`, `consTuple_rfl`, `continuous_consTuple`, `normHomotopyFun`, `normHomotopyFun_add_left`, `normHomotopyFun_smul_left`, `normHomotopyFun_add_right`, `normHomotopyFun_smul_right`, `sum_ρ_μ_tmul_ρ_inv`, `normHomotopyFun_d_add`, `normHomotopyFun_d_zero`, `isLocallyConstant_normHomotopyFun`, `normHomotopy`, `cochainOf_normHomotopy`, `cochainOf_cupPairingCochains_zeroCochain`, `d_normHomotopy_add`, `normHomotopy_d_zero`, `tateLocalResB`, `zeroCochainValue`, `tateExtraPairingAt`, `tateExtraPairing`, `tateExtraPairing_apply`, `tateGlobalCup`, `tateLocalCup`, `tateNormHomotopy`, `tateCupHomotopyL`, `tateCupHomotopyL_apply`, `tateCupHomotopy`, `normCochains_f_succ_apply'`, `tateCupHomotopy_succ_left`, `tateCupHomotopy_zero_zero`, `tateCupHomotopy_zero_succ`, `tateCupHomotopy_spec`, `LeibnizPairing.homologyMap_prodFst_prod_homology`, `LeibnizPairing.homologyMap_prodSnd_prod_homology`, `tateCompactCupLeibniz`, `tateCompactCup`, `tateCompactCup_tateLocalToCompact`, `normHomotopy_compat_left`, `normHomotopy_compat_right`, `tateCompactCup_tateCompactδ_add_tateCompactCup_δ`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/ConeHomotopy.lean`, `RealPlaces/NormHomotopy.lean`, `RealPlaces/HomologyMapProdFstProdLeftHomology.lean` and `RealPlaces/CupSequence.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter I, §4, Propositions (1.4.1), p. 36, and (1.4.3), pp. 38–39 (cup products of cochains and their compatibility with connecting maps).
