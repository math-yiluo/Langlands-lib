# The nine-term sequence of Poitou–Tate with Tate's Ĥ⁰ (abstract form)

`Langlands/GaloisCohomology/CompactSupport/TateModified/NineTerm.lean`, namespace `Langlands.GaloisCohomology`.

The version of `NineTerm.lean` with a second family of finite groups `F_w`, at which degree `0` is
Tate's `Ĥ⁰`: under `TatePoitouTateHypotheses` the sequence
`0 → H⁰(M) → P̂⁰ → H²(M')^∨ → H¹(M) → P¹ → H¹(M')^∨ → H²(M) → P² → H⁰(M')^∨ → 0`, with
`P̂⁰ = ∏_v H⁰(H_v, M) × ∏_w Ĥ⁰(F_w, M)` and `Pʳ = ∏_v Hʳ(H_v, M) × ∏_w Hʳ(F_w, M)`, is exact
(`IsTateNineTermExact`, `TatePoitouTateHypotheses.isTateNineTermExact`), and `Ш¹(M)`, `Ш²(M')`
are finite and in perfect duality. As in `NineTerm.lean`, the connecting maps take no proof as
argument.

```lean
abbrev ptTLocal (r : ℕ) : Type u
abbrev ptTLocalHat : Type u
def ptTCompactDualMap {r s : ℕ} (h : r + s = 3) :
    tateCompactCohomologyRes φ ψ M r →+ (cohomology (dualRep D M) s →+ QZ)
noncomputable def ptTDualToGlobal {r s : ℕ} (h : r + s = 3) :
    (cohomology (dualRep D M) s →+ QZ) →+ cohomology M r
theorem ptTDualToGlobal_eq {r s : ℕ} (h : r + s = 3)
    (hb : Function.Bijective (ptTCompactDualMap φ ψ D M t h)) :
    ptTDualToGlobal φ ψ D t M h =
      (ptTToGlobal φ ψ M r).hom.toAddMonoidHom.comp
        (AddEquiv.ofBijective _ hb).symm.toAddMonoidHom
structure TatePoitouTateHypotheses : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- Tate-modified duality `Hʳ(G, M') ≅ Ĥ_c^s(G, M)^∨` for `r + s = 3`, `s ≥ 1`, and finite `M` killed by `n`. -/
  duality : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M], (∀ m : M, n • m = 0) →
    ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s → Function.Bijective (tateCompactDualityMap φ ψ D h t M)
  /-- `Hʳ(G, M)` is finite for `r ≤ 2` and finite `M` killed by `n`. -/
  finite_cohomology : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, r ≤ 2 → Finite (cohomology M r)
  /-- The trace restricts on the local terms in degree 2 to the sum of the local invariants (at both families). -/
  localToCompact_two : ∀ ξ : ptTLocal φ ψ D 2,
    zmodToQZ n (t ((ptTLocalToCompact φ ψ D 2).hom ξ)) = ∑ v, inv v (ξ.1 v) + ∑ w, invr w (ξ.2 w)
  /-- `H⁰(G, M) → ∏_v H⁰(H_v, M)` is injective. -/
  injective_res_zero : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M],
    Function.Injective fun (x : cohomology M 0) v => ptRes φ M v 0 x
  /-- The local pairings at the first family in degrees `(0, 2)` are surjective. -/
  surjective_localPairing_zero : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))
  /-- The local pairings at the first family in degrees `(2, 0)` are surjective. -/
  surjective_localPairing_two : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 2 + 0 = 2 from rfl))
  /-- The local pairings at the finite groups in degrees `(0, 2)` are surjective. -/
  surjective_realPairing_zero : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ w,
      Function.Surjective (ptLocalPairing ψ D M invr w (show 0 + 2 = 2 from rfl))
  /-- Every character of `H⁰(F_w, M')` vanishing on norms is a local pairing in degrees `(2, 0)`. -/
  surjective_realPairing_two : ∀ (M : Rep (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ w
      (χ : cohomology (Rep.res (ψ w : F w →* G) (dualRep D M)) 0 →+ QZ),
      (∀ x ∈ normClasses (Rep.res (ψ w : F w →* G) (dualRep D M)), χ x = 0) →
      ∃ ξ, ptLocalPairing ψ D M invr w (show 2 + 0 = 2 from rfl) ξ = χ
structure IsTateNineTermExact : Prop where
  injective_globalToLocalHat : Function.Injective (ptTGlobalToLocalHat φ ψ M)
  exact_globalToLocalHat :
    Function.Exact (ptTGlobalToLocalHat φ ψ M) (ptTLocalHatDualMap φ ψ D M inv invr)
  exact_localHatDualMap :
    Function.Exact (ptTLocalHatDualMap φ ψ D M inv invr)
      (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl))
  exact_dualToGlobal_one :
    Function.Exact (ptTDualToGlobal φ ψ D t M (show 1 + 2 = 3 from rfl))
      (ptTGlobalToLocal φ ψ M 1).hom
  exact_globalToLocal_one :
    Function.Exact (ptTGlobalToLocal φ ψ M 1).hom
      (ptTLocalDualMap φ ψ D M inv invr (show 1 + 1 = 2 from rfl))
  exact_localDualMap_one :
    Function.Exact (ptTLocalDualMap φ ψ D M inv invr (show 1 + 1 = 2 from rfl))
      (ptTDualToGlobal φ ψ D t M (show 2 + 1 = 3 from rfl))
  exact_dualToGlobal_two :
    Function.Exact (ptTDualToGlobal φ ψ D t M (show 2 + 1 = 3 from rfl))
      (ptTGlobalToLocal φ ψ M 2).hom
  exact_globalToLocal_two :
    Function.Exact (ptTGlobalToLocal φ ψ M 2).hom
      (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl))
  surjective_localDualMap_two :
    Function.Surjective (ptTLocalDualMap φ ψ D M inv invr (show 2 + 0 = 2 from rfl))
theorem TatePoitouTateHypotheses.isTateNineTermExact (hM : ∀ m : M, n • m = 0) :
    IsTateNineTermExact φ ψ D t inv invr M
def ptTShaPairing : ptTSha φ ψ M 1 →+ ptTSha φ ψ (dualRep D M) 2 →+ QZ
theorem TatePoitouTateHypotheses.bijective_ptTShaPairing (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptTShaPairing φ ψ D M t)
theorem TatePoitouTateHypotheses.bijective_ptTShaPairing_flip (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptTShaPairing φ ψ D M t).flip
theorem TatePoitouTateHypotheses.finite_ptTSha_one (hM : ∀ m : M, n • m = 0) : Finite (ptTSha φ ψ M 1)
theorem TatePoitouTateHypotheses.finite_ptTSha_two (_hM : ∀ m : M, n • m = 0) : Finite (ptTSha φ ψ (dualRep D M) 2)
```

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@TatePoitouTateHypotheses.isTateNineTermExact : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {κ : Type u_1} {F : κ → Type u_1} [inst_7 : (w : κ) → Group (F w)]
  [inst_8 : (w : κ) → TopologicalSpace (F w)] [inst_9 : ∀ (w : κ), IsTopologicalGroup (F w)]
  [inst_10 : (w : κ) → Fintype (F w)] {ψ : (w : κ) → F w →ₜ* G} [inst_11 : Fintype κ] {n : ℕ} [NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_13 : Langlands.IsSmoothRep D]
  {t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  {invr :
    (w : κ) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(ψ w)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M],
  TatePoitouTateHypotheses φ ψ D t inv invr → (∀ (m : ↑M), n • m = 0) → IsTateNineTermExact φ ψ D t inv invr M

@TatePoitouTateHypotheses.bijective_ptTShaPairing : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {κ : Type u_1} {F : κ → Type u_1} [inst_7 : (w : κ) → Group (F w)]
  [inst_8 : (w : κ) → TopologicalSpace (F w)] [inst_9 : ∀ (w : κ), IsTopologicalGroup (F w)]
  [inst_10 : (w : κ) → Fintype (F w)] {ψ : (w : κ) → F w →ₜ* G} [inst_11 : Fintype κ] {n : ℕ} [NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_13 : Langlands.IsSmoothRep D]
  {t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  {invr :
    (w : κ) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(ψ w)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M],
  TatePoitouTateHypotheses φ ψ D t inv invr → (∀ (m : ↑M), n • m = 0) → Function.Bijective ⇑(ptTShaPairing φ ψ D M t)

@TatePoitouTateHypotheses.bijective_ptTShaPairing_flip : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {κ : Type u_1} {F : κ → Type u_1} [inst_7 : (w : κ) → Group (F w)]
  [inst_8 : (w : κ) → TopologicalSpace (F w)] [inst_9 : ∀ (w : κ), IsTopologicalGroup (F w)]
  [inst_10 : (w : κ) → Fintype (F w)] {ψ : (w : κ) → F w →ₜ* G} [inst_11 : Fintype κ] {n : ℕ} [NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_13 : Langlands.IsSmoothRep D]
  {t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  {invr :
    (w : κ) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(ψ w)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M],
  TatePoitouTateHypotheses φ ψ D t inv invr →
    (∀ (m : ↑M), n • m = 0) → Function.Bijective ⇑(ptTShaPairing φ ψ D M t).flip

@TatePoitouTateHypotheses.finite_ptTSha_one : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {κ : Type u_1} {F : κ → Type u_1} [inst_7 : (w : κ) → Group (F w)]
  [inst_8 : (w : κ) → TopologicalSpace (F w)] [inst_9 : ∀ (w : κ), IsTopologicalGroup (F w)]
  [inst_10 : (w : κ) → Fintype (F w)] {ψ : (w : κ) → F w →ₜ* G} [inst_11 : Fintype κ] {n : ℕ}
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_12 : Langlands.IsSmoothRep D]
  {t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  {invr :
    (w : κ) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(ψ w)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_13 : Langlands.IsSmoothRep M] [Finite ↑M],
  TatePoitouTateHypotheses φ ψ D t inv invr → (∀ (m : ↑M), n • m = 0) → Finite ↥(ptTSha φ ψ M 1)

@TatePoitouTateHypotheses.finite_ptTSha_two : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {κ : Type u_1} {F : κ → Type u_1} [inst_7 : (w : κ) → Group (F w)]
  [inst_8 : (w : κ) → TopologicalSpace (F w)] [inst_9 : ∀ (w : κ), IsTopologicalGroup (F w)]
  [inst_10 : (w : κ) → Fintype (F w)] {ψ : (w : κ) → F w →ₜ* G} [inst_11 : Fintype κ] {n : ℕ} [NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_13 : Langlands.IsSmoothRep D]
  {t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  {invr :
    (w : κ) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(ψ w)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_14 : Langlands.IsSmoothRep M] [inst_15 : Finite ↑M],
  TatePoitouTateHypotheses φ ψ D t inv invr →
    (∀ (m : ↑M), n • m = 0) → Finite ↥(ptTSha φ ψ (Langlands.ProfiniteCohomology.dualRep D M) 2)

@ptTDualToGlobal_eq : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G]
  {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)] [inst_4 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)] (φ : (v : ι) → Hv v →ₜ* G) {κ : Type u_1} {F : κ → Type u_1}
  [inst_6 : (w : κ) → Group (F w)] [inst_7 : (w : κ) → TopologicalSpace (F w)]
  [inst_8 : ∀ (w : κ), IsTopologicalGroup (F w)] [inst_9 : (w : κ) → Fintype (F w)] (ψ : (w : κ) → F w →ₜ* G) {n : ℕ}
  (D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_10 : Langlands.IsSmoothRep D]
  (t : ↑(tateCompactCohomologyRes φ ψ D 3) →+ ZMod n) (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G)
  [inst_11 : Langlands.IsSmoothRep M] [inst_12 : Finite ↑M] {r s : ℕ} (h : r + s = 3)
  (hb : Function.Bijective ⇑(ptTCompactDualMap φ ψ D M t h)),
  ptTDualToGlobal φ ψ D t M h =
    (ModuleCat.Hom.hom (ptTToGlobal φ ψ M r)).toAddMonoidHom.comp
      (AddEquiv.ofBijective (ptTCompactDualMap φ ψ D M t h) hb).symm.toAddMonoidHom
```

## Outline of the proofs

As in `NineTerm.lean`, with the long exact sequence of `TateModified/Basic.lean`; in
degree `0` the local term is `P̂⁰`, which is the quotient of `P⁰` by the norms at the finite groups
(`ptTHatMk`), and the maps of the sequence descend to it (`descendAddHom`) because the duality map
kills norms (`ptTCompactDualMap_ptTLocalToCompact`, `normClass_mem_normClasses`).

## Declarations

`exists_normClass_cycle`, `H0Iso_hom_normClass`, `normClass_mem_normClasses`, `exists_normClass_eq_of_mem`, `cupPairing_normClass_eq_zero`, `ptTLocal`, `ptTGlobalToLocal`, `ptTToGlobal`, `ptTLocalToCompact`, `ptTGlobalToLocal_apply`, `ptTExact_global`, `ptTExact_local`, `ptTExact_compact`, `ptTLocalHat`, `ptTHatMk`, `ptTHatMk_apply`, `ptTHatMk_surjective`, `ptTHatMk_eq_zero_iff`, `ptTGlobalToLocalHat`, `ptTGlobalToLocalHat_apply`, `descendAddHom`, `descendAddHom_apply`, `ptTLocalToCompact_of_hatMk_eq_zero`, `ptTLocalHatToCompact`, `ptTLocalHatToCompact_hatMk`, `ptTSha`, `mem_ptTSha`, `ptTToGlobal_mem_ptTSha`, `exists_ptTToGlobal_eq_of_mem_ptTSha`, `ptTLocalDualMap`, `ptTLocalDualMap_apply`, `ptTLocalDualMap_of_hatMk_eq_zero`, `ptTLocalHatDualMap`, `ptTLocalHatDualMap_hatMk`, `ptTCompactDualMap`, `ptTCompactDualMap_apply`, `tateCompactCupRes_ptTLocalToCompact`, `ptRes_eq_zero_of_mem_ptTSha`, `ptTCompactDualMap_eq_zero_of_ptTToGlobal_eq_zero`, `ptTShaLift`, `ptTToGlobal_ptTShaLift`, `ptTShaPairing`, `ptTShaPairing_apply`, `finite_of_finite_addMonoidHom_zmod`, `normClass_zero`, `TatePoitouTateHypotheses`, `ptTDualToGlobal`, `ptTDualToGlobal_eq`, `bijective_tateCompactCohomologyResMap_of_comp_eq_id`, `IsTateNineTermExact`, `bijective_ptTCompactDualMap`, `ptTCompactDualMap_ptTLocalToCompact`, `exact_stage_succ`, `exact_ptTLocalHatToCompact_ptTToGlobal`, `exact_ptTGlobalToLocalHat_ptTLocalHatToCompact`, `exact_stage_zero`, `injective_ptTGlobalToLocalHat`, `surjective_ptTLocalDualMap_two`, `surjective_ptTLocalToCompact_two`, `injective_ptTGlobalToLocal_three`, `isTateNineTermExact`, `bijective_ptTShaPairing`, `finite_ptTSha_one`, `finite_ptTSha_two`, `bijective_ptTShaPairing_flip`, `LeibnizPairing.homologyMap_homology_of_comm`, `tateForgetRes`, `tateForgetRes_cup`, `tateForget_tateCompactCupRes`, `cochainsMap_normHomotopy`, `tateCompactCochainsResMap_cup`, `tateCompactCohomologyResMap_tateCompactCupRes`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/PoitouTate/RealDefs.lean`, `PoitouTate/RealAbstract.lean` and `PoitouTate/RealCup.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. As in `NineTerm.lean`: `ptTDualToGlobal` takes no proof (defined by cases, `ptTDualToGlobal_eq`), `nineTerm` is the structure `IsTateNineTermExact`, `sha` is split into four theorems. The value of `zeroIso` on the class of a `0`-cocycle is `zeroIso_hom_cohomology_class_zero` of `Langlands.Cohomology.Profinite.Duality.DualModule`. The source states this layer for `Type`; here it is stated for `Type u`.

## References

- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr. Mathematicians (Stockholm 1962), Inst. Mittag-Leffler 1963, pp. 288–295: §1, p. 288 (at the real and complex places `Hʳ` is Tate's modified cohomology `Ĥʳ`), and Theorem 3.1, p. 291 (the perfect pairing of `Ker²(k_S, M)` and `Ker¹(k_S, M')`, the nine-term exact sequence, `Hʳ(k_S, M) ≅ ∏_{P real} Hʳ(k_P, M)` for `r ≥ 3`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6: Theorem (8.6.9), p. 488 (the pairing of `Ш¹` and `Ш²`), and (8.6.10), pp. 489–490 (the nine-term sequence of Poitou–Tate, with Tate's modified groups at the archimedean places in `P⁰`).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 (the Poitou–Tate theorem: perfect pairing of `Ш¹(M)` and `Ш²(M^D)`, the nine-term exact sequence, and `H^r(G_S, M) ≅ ∏_{v real} H^r(K_v, M)` for `r ≥ 3`).
