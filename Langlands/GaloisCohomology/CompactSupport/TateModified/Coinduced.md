# The Tate-modified duality map for coinduced modules

`Langlands/GaloisCohomology/CompactSupport/TateModified/Coinduced.lean`, namespace `Langlands.GaloisCohomology`.

For `M = Coind_U^G(ℤ/n)` with `U` meeting the conjugates of the finite groups trivially, the
Tate-modified duality map of `G` is the duality map of `U` with the corestricted trace
(`tateCompactDualityMap_coind`), hence bijective when the latter is
(`bijective_tateCompactDualityMap_coind`); corestriction in degree `3` is surjective
(`surjective_tateCompactCores_three`).

```lean
def tateCoindDualCompactMap (s : ℕ) :
    tateCompactCohomologyRes φ ψ
        (dualRep D (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n))) (s + 1) →+
      compactSupportCohomologyRes (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D) (s + 1)
theorem bijective_tateCompactDualityMap_coind (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) {r s : ℕ}
    (h : r + (s + 1) = 3)
    (hb : Function.Bijective (compactZmodDualityMap (mackeyFamily U φ) (Rep.res (U : Subgroup G).subtype D)
      hD (tateCoresTrace φ ψ U hU t) h)) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))
theorem surjective_tateCompactCores_three (D : Rep (ULift.{u} ℤ) G) [IsSmoothRep D] [Finite D] {n : ℕ}
    (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (tateCompactCohomologyRes φ ψ M 4)) :
    Function.Surjective (tateCompactCores φ ψ U hU D 2).hom
```

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@bijective_tateCompactDualityMap_coind : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] {ι : Type u_1} {Hv : ι → Type u_1}
  [inst_4 : (v : ι) → Group (Hv v)] [inst_5 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [inst_7 : ∀ (v : ι), CompactSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  {κ : Type u_1} {F : κ → Type u_1} [inst_8 : (w : κ) → Group (F w)] [inst_9 : (w : κ) → TopologicalSpace (F w)]
  [inst_10 : ∀ (w : κ), IsTopologicalGroup (F w)] [inst_11 : (w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G)
  (U : OpenSubgroup G) (hU : FreeOnCosets ψ ↑U) {n : ℕ} [inst_12 : NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_13 : Langlands.IsSmoothRep D] (hD : ∀ (d : ↑D), n • d = 0)
  (t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n) {r s : ℕ} (h : r + (s + 1) = 3),
  Function.Bijective
      ⇑(compactZmodDualityMap (mackeyFamily U φ) (Rep.res (↑U).subtype D) hD (tateCoresTrace φ ψ U hU t) h) →
    Function.Bijective
      ⇑(tateCompactDualityMap φ ψ D h t
          (Rep.coind.{u_1, u_1, u_1, u_1} (↑U).subtype (Langlands.ProfiniteCohomology.zmodRep (↥↑U) n)))
```

## Outline of the proofs

`tateCoindIso` identifies `Ĥ_c^s(G, Hom(Coind_U^G(ℤ/n), D))` with `H_c^s(U, D)`, compatibly
with cup products and corestriction (`tateCoindIso_tateCompactCupRes`,
`tateCompactCores_tateCoindIso_hom`), so the duality map of `G` for the coinduced module is that of
`U`; surjectivity of corestriction in degree `3` follows from the trace sequence of
`BaseCase.lean`.

## Declarations

`tateCoindIso_tateCompactCupRes`, `tateCompactCores_tateCoindIso_hom`, `tateCoindDualCompactMap`, `tateCoindDualCompactMap_apply`, `bijective_tateCoindDualCompactMap`, `tateCoresTrace`, `tateCompactDualityMap_coind`, `bijective_tateCompactDualityMap_coind`, `surjective_tateCompactCores_three`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/PoitouTate/RealEvenCoind.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
