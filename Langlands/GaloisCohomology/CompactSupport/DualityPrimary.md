# Reduction of the duality to prime-power modules

`Langlands/GaloisCohomology/CompactSupport/DualityPrimary.lean`, namespace `Langlands.GaloisCohomology`.

If the duality map is bijective for modules killed by each prime power `q` dividing `n` (with the
dualizing module `D_q = D[q]`), it is bijective for modules killed by `n`
(`bijective_compactDualityMap_of_primePow`): a module killed by `n = q₀ q₁` with coprime factors is
the direct sum of the images of multiplication by `q₁` and by `q₀`.

```lean
abbrev smulSubrep : Rep.{u} k G
theorem bijective_compactDualityMap_of_level
    (htj : ∀ z, zmodToQZ N (t ((compactSupportCohomologyResMap φ j 3).hom z)) = zmodToQZ q (tq z))
    (hD : Nonempty (D ≃+ ZMod N)) (hDq : Nonempty (Dq ≃+ ZMod q)) (hj : Function.Injective j.hom)
    (hM : ∀ m : M, q • m = 0) {r s : ℕ} (h : r + s = 3)
    (hq : Function.Bijective (compactDualityMap φ Dq h tq M)) :
    Function.Bijective (compactDualityMap φ D h t M)
theorem bijective_compactDualityMap_of_primePow (hD : Nonempty (D ≃+ ZMod N))
    (hDp : ∀ p ∈ N.primeFactors, Nonempty (Dp p ≃+ ZMod (p ^ N.factorization p)))
    (hjp : ∀ p ∈ N.primeFactors, Function.Injective (jp p).hom)
    (htp : ∀ p ∈ N.primeFactors, ∀ z, zmodToQZ N (t ((compactSupportCohomologyResMap φ (jp p) 3).hom z)) =
      zmodToQZ (p ^ N.factorization p) (tp p z))
    (hφp : ∀ p ∈ N.primeFactors, ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
      (∀ m : M, p ^ N.factorization p • m = 0) → ∀ {r s : ℕ} (h : r + s = 3),
        Function.Bijective (compactDualityMap φ (Dp p) h (tp p) M))
    (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] (hM : ∀ m : M, N • m = 0) {r s : ℕ}
    (h : r + s = 3) : Function.Bijective (compactDualityMap φ D h t M)
```

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@bijective_compactDualityMap_of_primePow : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  (φ : (v : ι) → Hv v →ₜ* G) {N : ℕ} [NeZero N] (D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G)
  [inst_7 : Langlands.IsSmoothRep D] (t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod N)
  (Dp : ℕ → Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_8 : ∀ (p : ℕ), Langlands.IsSmoothRep (Dp p)]
  (tp : (p : ℕ) → ↑(compactSupportCohomologyRes φ (Dp p) 3) →+ ZMod (p ^ N.factorization p)) (jp : (p : ℕ) → Dp p ⟶ D),
  Nonempty (↑D ≃+ ZMod N) →
    (∀ p ∈ N.primeFactors, Nonempty (↑(Dp p) ≃+ ZMod (p ^ N.factorization p))) →
      (∀ p ∈ N.primeFactors, Function.Injective ⇑(Rep.Hom.hom (jp p))) →
        (∀ p ∈ N.primeFactors,
            ∀ (z : ↑(compactSupportCohomologyRes φ (Dp p) 3)),
              (Langlands.ProfiniteCohomology.zmodToQZ N)
                  (t ((ModuleCat.Hom.hom (compactSupportCohomologyResMap φ (jp p) 3)) z)) =
                (Langlands.ProfiniteCohomology.zmodToQZ (p ^ N.factorization p)) ((tp p) z)) →
          (∀ p ∈ N.primeFactors,
              ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
                (∀ (m : ↑M), p ^ N.factorization p • m = 0) →
                  ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective ⇑(compactDualityMap φ (Dp p) h (tp p) M)) →
            ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
              (∀ (m : ↑M), N • m = 0) → ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective ⇑(compactDualityMap φ D h t M)
```

## Outline of the proofs

For `n = q₀ q₁` with coprime factors, `M = q₁M ⊕ q₀M` (`sum_smulSubrepPairProj_incl`) and
`q₁M` is killed by `q₀`; the duality map is bijective on a direct sum when it is on the summands
(`bijective_compactDualityMap_biproduct`), and for a module killed by `q` the duality map for `D`
factors through that for `D[q]` (`bijective_dualRepPost`).

## Declarations

`nsmul_dualRep_eq_zero_of_nsmul`, `dualRepPost`, `dualRepPost_hom_apply`, `tensorHom_dualRepPost_dualEvalPairing`, `bijective_dualRepPost`, `smulSubrep`, `smulSubrepProj`, `smulSubrepIncl`, `smulSubrepProj_smulSubrepIncl`, `exists_eq_smul_of_smulSubrep`, `smulSubrepPair`, `smulSubrepPairIncl`, `smulSubrepPairProj`, `sum_smulSubrepPairProj_incl`, `finite_smulSubrep`, `isSmoothRep_smulSubrep`, `isSmoothRep_smulSubrepPair`, `finite_smulSubrepPair`, `nsmul_smulSubrep_eq_zero`, `bijective_compactDualityMap_of_level`, `bijective_compactDualityMap_of_primePow`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/PoitouTate/Primary.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. The smoothness of `smulSubrep` is proved from the foundations' `vectorStabilizer`.

## References

- None: the file decomposes a finite module into the parts killed by coprime factors of `n`, an elementary step that the literature does not state separately.
