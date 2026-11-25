# Reduction of the base case of the duality to four pairings

`Langlands/GaloisCohomology/CompactSupport/BaseCase.lean`, namespace `Langlands.GaloisCohomology`.

For `D ≅ ℤ/n` with trivial action, local traces `t_v : H²(H_v, D) → ℤ/n` and a global trace
`T : H_c^3(G, D) → ℤ/n`, the hypotheses `BaseDualityHypotheses` (perfectness of the local pairings
in degrees `(1, 1)` and `(2, 0)`, bijectivity of `T`, compatibility of `T` with the `t_v`, vanishing
of `H³`, finiteness, and the perfectness and symmetry of the global pairing between `H_c^2(G, D)`
and `H¹(G, ℤ/n)`) imply that the duality map `Hʳ(G, ℤ/n) → Hom(H_c^s(G, D), ℤ/n)` is bijective for
all `r + s = 3` (`BaseDualityHypotheses.bijective_compactZmodDualityMap`). This is the base case of
`CompactDualityHypotheses`. The file also has the trace sequence of a coinduced module
(`coindTraceShortComplex`), classes of invariant vectors in `H⁰` and the vanishing of `H_c^0`.

```lean
def compactZmodDualityMap {m r s : ℕ} (T : compactSupportCohomologyRes φ D m →+ ZMod n) (h : r + s = m) :
    cohomology (zmodRep.{u} G n) r →+ (compactSupportCohomologyRes φ D s →+ ZMod n)
structure BaseDualityHypotheses (t : ∀ v, cohomology (Rep.res (φ v : H v →* G) D) 2 →+ ZMod n)
    (T : compactSupportCohomologyRes φ D 3 →+ ZMod n) : Prop where
  /-- `G` acts trivially on `D`. -/
  triv : ∀ (g : G) (d : D), D.ρ g d = d
  /-- `D` is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- The local pairings `H¹(H_v, ℤ/n) × H¹(H_v, D) → ℤ/n` are surjective in the first variable. -/
  loc_one : ∀ v, Function.Surjective fun ξ : cohomology (Rep.res (φ v : H v →* G) (zmodRep.{u} G n)) 1 =>
    (t v).comp ((bilinAddHom (cupPairing (pairingRes (φ v : H v →* G)
      (zmodMulPairingRight n D hD)) (show 1 + 1 = 2 from rfl))).flip ξ)
  /-- The local pairings in degrees `(2, 0)` are perfect. -/
  loc_two : ∀ v, Function.Bijective fun ξ : cohomology (Rep.res (φ v : H v →* G) (zmodRep.{u} G n)) 2 =>
    (t v).comp ((bilinAddHom (cupPairing (pairingRes (φ v : H v →* G)
      (zmodMulPairingRight n D hD)) (show 0 + 2 = 2 from rfl))).flip ξ)
  /-- The global trace `T : H_c^3(G, D) → ℤ/n` is bijective. -/
  bijective_alt : Function.Bijective T
  /-- `T` restricts on the image of `∏_v H²(H_v, D)` to the sum of the local traces. -/
  T_localToCompact : ∀ ξ, T ((localToCompact φ D (fun v => Rep.res (φ v : H v →* G) D) (fun _ => 𝟙 _) 2).hom ξ) =
    ∑ v, t v (ξ v)
  /-- `H³(G, ℤ/n) = 0`. -/
  three_zmod : Subsingleton (cohomology (zmodRep.{u} G n) 3)
  /-- `H³(G, D) = 0`. -/
  three_D : Subsingleton (cohomology D 3)
  /-- `H¹(G, ℤ/n)` is finite. -/
  finite_one : Finite (cohomology (zmodRep.{u} G n) 1)
  /-- `H_c^2(G, D)` is finite. -/
  finite_two : Finite (compactSupportCohomologyRes φ D 2)
  /-- The pairing `H_c^2(G, D) × H¹(G, ℤ/n) → ℤ/n` has trivial left kernel. -/
  ker_left : ∀ x : cohomology (zmodRep.{u} G n) 1,
    (∀ y : compactSupportCohomologyRes φ D 2, T (compactCupRes φ (zmodMulPairingRight n D hD) (show 2 + 1 = 3 from rfl) y x) = 0) →
      x = 0
  /-- The pairing `H_c^2(G, D) × H¹(G, ℤ/n) → ℤ/n` has trivial right kernel. -/
  ker_right : ∀ y : compactSupportCohomologyRes φ D 2,
    (∀ x : cohomology (zmodRep.{u} G n) 1, T (compactCupRes φ (zmodMulPairingRight n D hD) (show 2 + 1 = 3 from rfl) y x) = 0) →
      y = 0
  /-- Symmetry of the pairings in degrees `(1, 2)` and `(2, 1)` through `H_c → H`. -/
  swap : ∀ (yc : compactSupportCohomologyRes φ D 1) (xc : compactSupportCohomologyRes φ (zmodRep.{u} G n) 2),
    T (compactCupRes φ (zmodMulPairingRight n D hD) (show 1 + 2 = 3 from rfl) yc
        ((compactToGlobal φ _ (fun v => Rep.res (φ v : H v →* G) (zmodRep.{u} G n)) (fun _ => 𝟙 _) 2).hom xc)) =
      T (compactCupRes φ (zmodMulPairing n D hD) (show 2 + 1 = 3 from rfl) xc
        ((compactToGlobal φ D (fun v => Rep.res (φ v : H v →* G) D) (fun _ => 𝟙 _) 1).hom yc))
theorem BaseDualityHypotheses.bijective_compactZmodDualityMap {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap φ D hD T h)
theorem subsingleton_compactSupportCohomologyRes_zero [Nonempty ι] (A : Rep.{u} k G) [IsSmoothRep A] :
    Subsingleton (compactSupportCohomologyRes φ A 0)
theorem injective_map_zero {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (ψ : K →ₜ* G) (A : Rep.{u} k G) [IsSmoothRep A] :
    Function.Injective (map ψ (𝟙 (Rep.res (ψ : K →* G) A)) 0).hom
def coindTraceShortComplex : ShortComplex (Rep.{u} k G)
theorem surjective_compactCores_three (V : OpenSubgroup G) (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
    [Finite D] {n : ℕ} (hD : ∀ d : D, n • d = 0)
    (hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
      Subsingleton (compactSupportCohomologyRes φ M 4)) :
    Function.Surjective (compactCores φ V D 3).hom
```

Variables of the main theorem: `G`, `H_v` compact and totally disconnected, `ι` finite and nonempty, `n ≠ 0`, `D : Rep.{u} (ULift.{u} ℤ) G` smooth with `hD : ∀ d : D, n • d = 0`, `t : ∀ v, cohomology (Rep.res (φ v : H v →* G) D) 2 →+ ZMod n`, `T : compactSupportCohomologyRes φ D 3 →+ ZMod n`, `hyp : BaseDualityHypotheses φ D hD t T`.

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@BaseDualityHypotheses.bijective_compactZmodDualityMap : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} [inst_3 : Fintype ι] [Nonempty ι] {H : ι → Type u_1}
  [inst_5 : (v : ι) → Group (H v)] [inst_6 : (v : ι) → TopologicalSpace (H v)]
  [inst_7 : ∀ (v : ι), IsTopologicalGroup (H v)] [∀ (v : ι), CompactSpace (H v)] {φ : (v : ι) → H v →ₜ* G} {n : ℕ}
  [NeZero n] {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_10 : Langlands.IsSmoothRep D]
  {hD : ∀ (d : ↑D), n • d = 0}
  {t : (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ ZMod n}
  {T : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n},
  BaseDualityHypotheses φ D hD t T → ∀ {r s : ℕ} (h : r + s = 3), Function.Bijective ⇑(compactZmodDualityMap φ D hD T h)
```

For the duality with coefficients `ℤ/n` (`D` killed by `n`):

* `surjective_localToCompact_two`: `∏_v H²(H_v, D) → H_c³(G, D)` is surjective when `H³(G, D) = 0`;
* `compactCupRes_zmodH0Class_of_surjective`: cup product with the class of `a ∈ ℤ/n` in degree `0` is
  multiplication by `a` on `H_c³(G, D)`, when `∏_v H²(H_v, D) → H_c³(G, D)` is onto;
* instance `isSmoothRep_dualRep_zmodRep`; `bijective_compactZmodDualityMap_of_compactDualityMap`: the
  duality map for `ℤ/n` is bijective when the general duality map is, for `M = ℤ/n`;
* `bijective_zmodCompactDualityMap_of`: the duality map for `ℤ/n` over an open subgroup `U` (with
  corestriction) is that of `U` with its Mackey family, for the trace composed with corestriction.

Their complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.surjective_localToCompact_two.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)]
  [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  [Langlands.IsSmoothRep D] (h3 : Subsingleton ↑(Langlands.ProfiniteCohomology.cohomology D 3)) :
  Function.Surjective
    ⇑(ModuleCat.Hom.hom
        (Langlands.GaloisCohomology.localToCompact φ D (fun v => Rep.res (↑(φ v)) D)
          (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) D)) 2))
Langlands.GaloisCohomology.compactCupRes_zmodH0Class_of_surjective.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)] [(v : ι) → TopologicalSpace (H v)]
  [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {n : ℕ} [NeZero n]
  (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] (hD : ∀ (d : ↑D), n • d = 0)
  (hsurj :
    Function.Surjective
      ⇑(ModuleCat.Hom.hom
          (Langlands.GaloisCohomology.localToCompact φ D (fun v => Rep.res (↑(φ v)) D)
            (fun x => CategoryTheory.CategoryStruct.id (Rep.res (↑(φ x)) D)) 2)))
  (h : 3 + 0 = 3) (a : ZMod n) (y : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3)) :
  ((Langlands.GaloisCohomology.compactCupRes φ (Langlands.GaloisCohomology.zmodMulPairingRight n D hD) h) y)
      (Langlands.ProfiniteCohomology.zmodH0Class a) =
    a.val • y
Langlands.GaloisCohomology.isSmoothRep_dualRep_zmodRep.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {n : ℕ} [NeZero n] (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] :
  Langlands.IsSmoothRep (Langlands.ProfiniteCohomology.dualRep D (Langlands.ProfiniteCohomology.zmodRep G n))
Langlands.GaloisCohomology.bijective_compactZmodDualityMap_of_compactDualityMap.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {H : ι → Type u} [(v : ι) → Group (H v)]
  [(v : ι) → TopologicalSpace (H v)] [∀ (v : ι), IsTopologicalGroup (H v)] (φ : (v : ι) → H v →ₜ* G) {n : ℕ} [NeZero n]
  (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] (hD : ∀ (d : ↑D), n • d = 0) {r s : ℕ}
  (h : r + s = 3) (T : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3) →+ ZMod n)
  (hb :
    Function.Bijective
      ⇑(Langlands.GaloisCohomology.compactDualityMap φ D h T (Langlands.ProfiniteCohomology.zmodRep G n))) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.compactZmodDualityMap φ D hD T h)
Langlands.GaloisCohomology.bijective_zmodCompactDualityMap_of.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [(v : ι) → Group (Hv v)]
  [(v : ι) → TopologicalSpace (Hv v)] [∀ (v : ι), IsTopologicalGroup (Hv v)] [∀ (v : ι), CompactSpace (Hv v)]
  (φ : (v : ι) → Hv v →ₜ* G) (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] {n : ℕ}
  (hD : ∀ (d : ↑D), n • d = 0) (U : OpenSubgroup G) {r s : ℕ} (h : r + s = 3)
  (t : ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes φ D 3) →+ ZMod n)
  [hDU : Langlands.IsSmoothRep (Rep.res (↑U).subtype D)] (hD' : ∀ (d : ↑(Rep.res (↑U).subtype D)), n • d = 0)
  (T :
    ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.mackeyFamily U φ)
          (Rep.res (↑U).subtype D) 3) →+
      ZMod n)
  (hT :
    ∀
      (y :
        ↑(Langlands.GaloisCohomology.compactSupportCohomologyRes (Langlands.GaloisCohomology.mackeyFamily U φ)
            (Rep.res (↑U).subtype D) 3)),
      T y = t ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactCores φ U D 3)) y))
  (hb :
    Function.Bijective
      ⇑(Langlands.GaloisCohomology.compactZmodDualityMap (Langlands.GaloisCohomology.mackeyFamily U φ)
          (Rep.res (↑U).subtype D) hD' T h)) :
  Function.Bijective ⇑(Langlands.GaloisCohomology.zmodCompactDualityMap φ D hD U h t)
```

## Outline of the proofs

Degree `(3, 0)`: `H³(G, ℤ/n) = 0` and `T` bijective. Degree `(0, 3)`: `H⁰(G, ℤ/n) = ℤ/n`
pairs with `H_c^3(G, D) ≅ ℤ/n` through `T` (`T_compactCupRes_zmodH0Class`). Degree `(1, 2)`:
injectivity from the left kernel hypothesis, surjectivity by counting with the finiteness
hypotheses and `bijective_of_injective_of_injective_flip`. Degree `(2, 1)`: injectivity and
surjectivity through the exact sequence `∏_v H¹(H_v) → H_c^2 → H²` and the local pairings
(`injective_two`, `surjective_two`), with the symmetry hypothesis `swap`. The trace sequence of a
coinduced module and `surjective_compactCores_three` (corestriction onto `H_c^3`) are used for
open subgroups.

`isSmoothRep_res_zmodRep_base`, the smoothness of `Rep.res (φ v : H v →* G) (ℤ/n)` (`isSmoothRep_res`,
which instance search does not find for this coercion), is a local instance of the two sections
that state `BaseDualityHypotheses` and prove its consequences, not a global one.

## Declarations

`coindTracePreimage`, `coindTrace_coindTracePreimage`, `surjective_coindTrace`, `coindTraceKer`, `coindTraceKer_le_comap`, `coindTraceShortComplex`, `coindTraceShortComplex_shortExact`, `inv_comp_hom_apply_base`, `surjective_compactCores_three`, `compactZmodDualityMap`, `compactZmodDualityMap_apply`, `bijective_of_injective_of_injective_flip`, `injective_map_zero`, `subsingleton_compactSupportCohomologyRes_zero`, `pairWithLinear`, `pairWith`, `pairWith_hom_apply`, `tensorHom_unitHom_comp`, `h0Class`, `map_h0Class`, `cupPairing_h0Class`, `isSmoothRep_zmodRep_base`, `pairingRes`, `pairingRes_zmodMulPairing`, `cupPairing_pairingRes_zmodMulPairing_one`, `cupPairing_pairingRes_zmodMulPairing_two_zero`, `cyclicToZMod`, `zmodToCyclic`, `cyclicToZMod_comp_zmodToCyclic`, `zmodToCyclic_comp_cyclicToZMod`, `zmodToCyclic_tensor_zmodMulPairingRight`, `isSmoothRep_res_zmodRep_base`, `BaseDualityHypotheses`, `pairWith_pairingRes_zmodMulPairingRight`, `localToCompact_two_surjective`, `T_compactCupRes_zmodH0Class`, `bijective_three`, `bijective_zero`, `bijective_one`, `T_compactCupRes_localToCompact_zero`, `T_compactCupRes_localToCompact_one`, `T_compactCupRes_localToCompact_two`, `compactCupRes_zmodMulPairing_eq`, `eq_zero_of_forall_compactCupRes_zmodMulPairing`, `nsmul_local_cohomology_D`, `injective_two`, `nsmul_cohomology_one_D`, `resFunctor_map_zmodToCyclic`, `surjective_two`, `bijective_compactZmodDualityMap`, `surjective_localToCompact_two`, `compactCupRes_zmodH0Class_of_surjective`, `isSmoothRep_dualRep_zmodRep`, `bijective_compactZmodDualityMap_of_compactDualityMap`, `bijective_zmodCompactDualityMap_of`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseFormal.lean` and `RestrictedRamification/BaseCores.lean` (without `surjective_gs_compactCores_three`, which is about `G_S`). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. `injective_cohomologyMapAlong_zero`, `cohomologyMapAlong_h0Class` (for `ψ : K →* G` with a continuity proof) are `injective_map_zero`, `map_h0Class` (for `ψ : K →ₜ* G`).

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 (the Poitou–Tate theorem: perfect pairing of `Ш¹(M)` and `Ш²(M^D)`, the nine-term exact sequence, and `H^r(G_S, M) ≅ ∏_{v real} H^r(K_v, M)` for `r ≥ 3`).
