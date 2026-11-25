# The Mackey isomorphism and cup products

`Langlands/GaloisCohomology/CompactSupport/OpenSubgroupCup.lean`, namespace `Langlands.GaloisCohomology`.

The isomorphism `H_c^n(G, Coind_V^G N) ≅ H_c^n(V, N)` of `OpenSubgroup.lean` is compatible with cup
products (`mackeyCompactCohomologyIso_compactCupRes`): coinduced pairings
`Coind N₁ ⊗ Coind N₂ → Coind N₃` correspond to the pairings of the Mackey family. The proof compares
the conjugation homotopies of the foundations with cup products of cochains.

```lean
def coindPairing :
    Rep.coind V.subtype N₁ ⊗ Rep.coind V.subtype N₂ ⟶ Rep.coind V.subtype N₃
theorem mackeyCompactCohomologyIso_compactCupRes {r s n : ℕ} (h : r + s = n)
    (y : compactSupportCohomologyRes φ (Rep.coind (V : Subgroup G).subtype N₁) r)
    (x : cohomology (Rep.coind (V : Subgroup G).subtype N₂) s) :
    (mackeyCompactCohomologyIso V φ N₃ n).hom.hom
        (compactCupRes φ (coindPairing (V : Subgroup G) μ) h y x) =
      compactCupRes (mackeyFamily V φ) μ h ((mackeyCompactCohomologyIso V φ N₁ r).hom.hom y)
        ((shapiroMap V N₂ s).hom x)
```

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@mackeyCompactCohomologyIso_compactCupRes : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [inst_4 : CompactSpace G] {ι : Type u_1}
  {Hv : ι → Type u_1} [inst_5 : (v : ι) → Group (Hv v)] [inst_6 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_7 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [inst_8 : ∀ (v : ι), CompactSpace (Hv v)] (V : OpenSubgroup G)
  (φ : (v : ι) → Hv v →ₜ* G) {N₁ N₂ N₃ : Rep.{u_1, u_1, u_1} k ↥↑V} [inst_9 : Langlands.IsSmoothRep N₁]
  [inst_10 : Langlands.IsSmoothRep N₂] [inst_11 : Langlands.IsSmoothRep N₃]
  (μ : CategoryTheory.MonoidalCategoryStruct.tensorObj N₁ N₂ ⟶ N₃) {r s n : ℕ} (h : r + s = n)
  (y : ↑(compactSupportCohomologyRes φ (Rep.coind.{u_1, u_1, u_1, u_1} (↑V).subtype N₁) r))
  (x : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.coind.{u_1, u_1, u_1, u_1} (↑V).subtype N₂) s)),
  (ModuleCat.Hom.hom (mackeyCompactCohomologyIso V φ N₃ n).hom) (((compactCupRes φ (coindPairing (↑V) μ) h) y) x) =
    ((compactCupRes (mackeyFamily V φ) μ h) ((ModuleCat.Hom.hom (mackeyCompactCohomologyIso V φ N₁ r).hom) y))
      ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.shapiroMap V N₂ s)) x)
```

## Outline of the proofs

On cochains, Shapiro's map carries the cup product along a coinduced pairing to the cup
product along the original pairing (`shapiroCochains_cupPairingCochains`), and the conjugation
homotopy is compatible with cup products up to explicit correction terms
(`mackeyLocalHomotopy_cup`, using `conjHomotopyFun_cupCochain` of `Internal/ConeHomotopy.lean`);
the comparison of cone pairings under maps of cocones defined by homotopies
(`homologyMap_mapOfHomotopy_coconeLeft`) then gives the statement in cohomology.

## Declarations

`coindPairingFun`, `coindPairing`, `coindPairing_tmul_apply`, `shapiroCochains_cupPairingCochains`, `coindPairing_cupCochain_apply`, `mackeyHomotopy_hom_succ`, `mackeyLocalHomotopy_hom_apply`, `coindLocalCup`, `mackeyLocalCup`, `mackeyLocalMap_pi_cup`, `cupCochain_comp_monoidHom`, `hom_conjHomotopyFun`, `cupCochain_neg_left`, `cupCochain_neg_right`, `coindPairing_cupCochain_comp_apply`, `conjCochainFun_comp_apply`, `neg_conjHomotopyFun_coindPairing_apply`, `neg_conjHomotopyFun_coindPairing_apply_zero_left`, `neg_conjHomotopyFun_coindPairing_apply_zero_right`, `mackeyLocalHomotopy_hom_eq`, `mackeyLocalHomotopy_cup`, `mackeyLocalHomotopy_cup_zero_left`, `mackeyLocalHomotopy_cup_zero_right`, `mackeyCompactCohomologyIso_compactCupRes`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/PoincarePairs/MackeyCup.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. `mackeyHomotopy_hom_succ` is new: the foundations' `mackeyHomotopy` is built with `Homotopy.trans` and `Homotopy.compRightId`, whose components carry terms `0 + ·` and `· + 0`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter I, §4, Propositions (1.4.1), p. 36, and (1.4.3), pp. 38–39 (cup products of cochains and their compatibility with connecting maps).
