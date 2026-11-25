# Cohomology with compact support of an open subgroup

`Langlands/GaloisCohomology/CompactSupport/OpenSubgroup.lean`, namespace `Langlands.GaloisCohomology`.

Let `G` be compact, `(φ_v : H_v →ₜ* G)` a family with `H_v` compact, `V` an open subgroup and `N` a
smooth `V`-module. Restricting the family to `V` is done by the Mackey decomposition: the family of
`V` is indexed by `MackeyIndex V φ`, the pairs `(v, d)` with `d ∈ V \ G / φ_v(H_v)`, with local groups
`mackeyGroup V φ (v, d) = {h ∈ H_v | x φ_v(h) x⁻¹ ∈ V}` mapping to `V` by conjugation
(`mackeyFamily`). Shapiro's lemma holds with compact support:
`H_c^n(G, Coind_V^G N) ≅ H_c^n(V, N)` (`mackeyCompactCohomologyIso`), the cochain maps being
compatible up to an explicit homotopy (`mackeyLocalHomotopy`).

```lean
abbrev MackeyIndex : Type u
noncomputable abbrev mackeyGroup (p : MackeyIndex V φ) : Type u
noncomputable def mackeyFamily (p : MackeyIndex V φ) : mackeyGroup V φ p →ₜ* (V : Subgroup G)
noncomputable def mackeyCompactCohomologyIso (n : ℕ) :
    compactSupportCohomologyRes φ (Rep.coind (V : Subgroup G).subtype N) n ≅
      compactSupportCohomology (mackeyFamily V φ) N (mackeyCoeff V φ N) (fun _ => 𝟙 _) n
```

Variables: `G` compact, `H_v` compact, `φ : ∀ v, H v →ₜ* G`, `V : OpenSubgroup G`, `N : Rep.{u} k V` smooth.

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@isIso_homologyMap_mackeyCompactMap : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [inst_4 : CompactSpace G] {ι : Type u_1}
  {Hv : ι → Type u_1} [inst_5 : (v : ι) → Group (Hv v)] [inst_6 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_7 : ∀ (v : ι), IsTopologicalGroup (Hv v)] [inst_8 : ∀ (v : ι), CompactSpace (Hv v)] (V : OpenSubgroup G)
  (φ : (v : ι) → Hv v →ₜ* G) (N : Rep.{u_1, u_1, u_1} k ↥↑V) [inst_9 : Langlands.IsSmoothRep N] (n : ℕ),
  CategoryTheory.IsIso (HomologicalComplex.homologyMap (mackeyCompactMap V φ N) n)

@mackeyCompactCohomologyIso : {k G : Type u_1} →
  [inst : CommRing k] →
    [inst_1 : Group G] →
      [inst_2 : TopologicalSpace G] →
        [inst_3 : IsTopologicalGroup G] →
          [inst_4 : CompactSpace G] →
            {ι : Type u_1} →
              {Hv : ι → Type u_1} →
                [inst_5 : (v : ι) → Group (Hv v)] →
                  [inst_6 : (v : ι) → TopologicalSpace (Hv v)] →
                    [inst_7 : ∀ (v : ι), IsTopologicalGroup (Hv v)] →
                      [∀ (v : ι), CompactSpace (Hv v)] →
                        (V : OpenSubgroup G) →
                          (φ : (v : ι) → Hv v →ₜ* G) →
                            (N : Rep.{u_1, u_1, u_1} k ↥↑V) →
                              [inst_9 : Langlands.IsSmoothRep N] →
                                (n : ℕ) →
                                  compactSupportCohomologyRes φ (Rep.coind.{u_1, u_1, u_1, u_1} (↑V).subtype N) n ≅
                                    compactSupportCohomology (mackeyFamily V φ) N (mackeyCoeff V φ N)
                                      (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(mackeyFamily V φ x)) N)) n
```

## Outline of the proofs

The local cochains of `Coind_V^G N` over `H_v` decompose along the double cosets
(`mackeyLocalMap`, from the foundations' `mackeyCochainsMap`); Shapiro's map on global cochains and
this decomposition commute up to the foundations' conjugation homotopies (`mackeyLocalHomotopy`),
so the square of `localRes` commutes up to homotopy and induces a map of mapping cocones
(`mappingCoconeNat.mapOfHomotopy`). Shapiro's map and the Mackey map are isomorphisms in cohomology
(`isIso_homologyMap_shapiroCochains`, `isIso_homologyMap_mackeyLocalMap`), so by the five lemma the
map of cocones is too (`isIso_homologyMap_mackeyCompactMap`).

## Declarations

`piLiftHomotopy`, `for`, `isSmoothRep_res_coind_coe`, `MackeyIndex`, `mackeyGroup`, `mackeyFamily`, `mackeyCoeff`, `mackeyLocalMap`, `mackeyLocalHomotopy`, `mackeyCompactMap`, `isIso_homologyMap_shapiroCochains`, `isIso_homologyMap_mackeyLocalMap`, `isIso_homologyMap_mackeyCompactMap`, `mackeyCompactCohomologyIso`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, file `src/GroundTheory/ProfiniteCohomology/MackeyFormula/CompactSupport.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. The instance `isSmoothRep_res_coind_coe` is new (smoothness for the coercion form).

## References

- Shapiro's lemma for compact support is not stated in the literature in this form. For the Mackey decomposition see the page of `Langlands/Cohomology/Profinite/Mackey/Decomposition.lean`. J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
