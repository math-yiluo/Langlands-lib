# The Tate-modified duality theorem

`Langlands/GaloisCohomology/CompactSupport/TateModified/Duality.lean`, namespace `Langlands.GaloisCohomology`.

The duality map `Hʳ(G, Hom(M, D)) → Hom(Ĥ_c^s(G, M), ℤ/n)` (`tateCompactDualityMap`) and its
dévissage: under `TateCompactDualityHypotheses` it is bijective for `s ≥ 1` and every finite smooth
`M` killed by `n` (`TateCompactDualityHypotheses.bijective_tateCompactDualityMap`).

```lean
def tateCompactDualityMap (D : Rep.{u} k G) [IsSmoothRep D] {n m r s : ℕ} (h : r + s = m)
    (t : tateCompactCohomologyRes φ ψ D m →+ ZMod n) (M : Rep.{u} k G) [IsSmoothRep M]
    [IsSmoothRep (dualRep D M)] :
    cohomology M r →+ (tateCompactCohomologyRes φ ψ (dualRep D M) s →+ ZMod n)
structure TateCompactDualityHypotheses (n : ℕ) [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G)
    [IsSmoothRep D] (t : tateCompactCohomologyRes φ ψ D 3 →+ ZMod n) (U₀ : OpenSubgroup G) :
    Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- The Tate-modified `Ĥ_c^4` vanishes for finite modules killed by `n`. -/
  subsingleton_four : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (tateCompactCohomologyRes φ ψ M 4)
  /-- The Tate-modified duality map is bijective, for `s ≥ 1`, for the modules coinduced from `ℤ/n` on open subgroups below `U₀`. -/
  bijective_coind : ∀ (U : OpenSubgroup G), U ≤ U₀ → ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
    Function.Bijective (tateCompactDualityMap φ ψ D h t
      (Rep.coind (U : Subgroup G).subtype (zmodRep.{u} (U : Subgroup G) n)))
theorem TateCompactDualityHypotheses.bijective_tateCompactDualityMap (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (tateCompactDualityMap φ ψ D h t M)
```

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@TateCompactDualityHypotheses.bijective_tateCompactDualityMap : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : CompactSpace G] {ι : Type u_1}
  {Hv : ι → Type u_1} [inst_4 : (v : ι) → Group (Hv v)] [inst_5 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_6 : ∀ (v : ι), IsTopologicalGroup (Hv v)] {φ : (v : ι) → Hv v →ₜ* G} {κ : Type u_1} {F : κ → Type u_1}
  [inst_7 : (w : κ) → Group (F w)] [inst_8 : (w : κ) → TopologicalSpace (F w)]
  [inst_9 : ∀ (w : κ), IsTopologicalGroup (F w)] [inst_10 : (w : κ) → Fintype (F w)] {ψ : (w : κ) → F w →ₜ* G} {n : ℕ}
  [inst_11 : NeZero n] {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_12 : Langlands.IsSmoothRep D]
  {t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n} {U₀ : OpenSubgroup G},
  TateCompactDualityHypotheses φ ψ n D t U₀ →
    ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_13 : Langlands.IsSmoothRep M] [inst_14 : Finite ↑M],
      (∀ (m : ↑M), n • m = 0) →
        ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective ⇑(tateCompactDualityMap φ ψ D h t M)
```

The vanishing of `Ĥ_cⁿ` passes to extensions (`subsingleton_tateCompactCohomologyRes_of_shortExact`, by
the exact sequence `tateCompactRes_exact₂`) and to retracts (`subsingleton_tateCompactCohomologyRes_of_retract`,
by functoriality).

Complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.subsingleton_tateCompactCohomologyRes_of_shortExact.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {κ : Type u}
  {F : κ → Type u} [(w : κ) → Group (F w)] [(w : κ) → TopologicalSpace (F w)] [∀ (w : κ), IsTopologicalGroup (F w)]
  [(w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G) {S : CategoryTheory.ShortComplex (Rep.{u, u, u} k G)}
  [Langlands.IsSmoothRep S.X₁] [Langlands.IsSmoothRep S.X₂] [Langlands.IsSmoothRep S.X₃] (hS : S.ShortExact) (n : ℕ)
  (h₁ : Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ S.X₁ n))
  (h₃ : Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ S.X₃ n)) :
  Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ S.X₂ n)
Langlands.GaloisCohomology.subsingleton_tateCompactCohomologyRes_of_retract.{u} {k G : Type u} [CommRing k] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {κ : Type u}
  {F : κ → Type u} [(w : κ) → Group (F w)] [(w : κ) → TopologicalSpace (F w)] [∀ (w : κ), IsTopologicalGroup (F w)]
  [(w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G) {A B : Rep.{u, u, u} k G} [Langlands.IsSmoothRep A]
  [Langlands.IsSmoothRep B] (i : A ⟶ B) (p : B ⟶ A)
  (hip : CategoryTheory.CategoryStruct.comp i p = CategoryTheory.CategoryStruct.id A) (n : ℕ)
  (hB : Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ B n)) :
  Subsingleton ↑(Langlands.GaloisCohomology.tateCompactCohomologyRes φ ψ A n)
```

## Outline of the proofs

As in `Duality.lean`: naturality of the duality map, compatibility with the connecting
maps up to sign, dévissage through embeddings into sums of coinduced modules, and induction on the
degree for `s ≥ 1`.

## Declarations

`tateCompactCochainsResMap`, `tateCompactCohomologyResMap`, `tateCompactCochainsResMap_add`, `tateCompactCochainsResMap_zero`, `tateCompactCochainsResMap_id`, `tateCompactCochainsResMap_comp`, `tateCompactCohomologyResMap_add`, `tateCompactCohomologyResMap_zero`, `tateCompactCohomologyResMap_id`, `tateCompactCohomologyResMap_comp`, `tateCompactCohomologyResMap_finsetSum`, `nsmul_tateCompactCohomologyRes_eq_zero`, `tateCompactδRes`, `tateCompactRes_exact₂`, `tateCompactRes_exact₃`, `tateCompactRes_exact₁`, `tateCompactCupRes`, `tateCompactDualityMap`, `tateCompactDualityMap_apply`, `TateCompactDualityHypotheses`, `tateCompactCupResLeibniz`, `tateCompactCupRes_eq_homology`, `tateCompactCupResLeibniz_naturality`, `tateCompactCupRes_tateCompactCohomologyResMap`, `tateCompactDualityMap_cohomologyMap`, `bijective_tateCompactDualityMap_of_sum`, `bijective_tateCompactDualityMap_biproduct`, `tateCompactDualityMap_δ`, `finite_D`, `nsmul_D`, `exists_devissage`, `injective_zero`, `surjective_zero`, `bijective_zero`, `injective_succ`, `surjective_succ`, `bijective_succ`, `bijective_tateCompactDualityMap`, `subsingleton_tateCompactCohomologyRes_of_shortExact`, `subsingleton_tateCompactCohomologyRes_of_retract`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RealPlaces/DevissageDefs.lean`, `RealPlaces/DevissageNatural.lean` and `RealPlaces/Devissage.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`.

`subsingleton_tateCompactCohomologyRes_of_shortExact` and `subsingleton_tateCompactCohomologyRes_of_retract`
are ported from `src/GroundTheory/ProfiniteCohomology/RealPlaces/VanishingCriterion.lean` of the repository
`leanprover-community/riemann-hypothesis` (commit `f1f6d65`; source names
`eq_zero_tateCompactCohomologyRes_of_shortExact`, `eq_zero_tateCompactCohomologyRes_of_retract`, stated
there as the vanishing of every element).
The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`).

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter II, §2, pp. 165–166 (cohomology with compact support as the translate of a mapping cone, with complete resolutions at the real places; Proposition 2.3, its long exact sequences).
