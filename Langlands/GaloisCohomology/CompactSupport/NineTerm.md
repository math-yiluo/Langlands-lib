# The nine-term sequence of Poitou–Tate (abstract form)

`Langlands/GaloisCohomology/CompactSupport/NineTerm.lean`, namespace `Langlands.GaloisCohomology`.

For a family `(φ_v : H_v →ₜ* G)` indexed by a finite set, a dualizing module `D ≅ ℤ/n` with a trace
`t : H_c^3(G, D) → ℤ/n` and local invariants `inv_v : H²(H_v, D) → ℚ/ℤ`, the hypotheses
`PoitouTateDualityHypotheses` (duality with compact support, finiteness, `H³ = 0`, compatibility of
`t` with the local invariants, surjectivity of the local pairings in degree `0`) imply, for every
finite module `M` killed by `n` with `M' = Hom(M, D)`:

* the nine-term sequence `0 → H⁰(M) → P⁰ → H²(M')^∨ → H¹(M) → P¹ → H¹(M')^∨ → H²(M) → P² → H⁰(M')^∨ → 0`
  is exact (`IsNineTermExact`, `PoitouTateDualityHypotheses.isNineTermExact`), where
  `Pʳ = ∏_v Hʳ(H_v, M)`;
* `Ш¹(M)` and `Ш²(M')` are finite and in perfect duality (`ptShaPairing`).

The connecting maps `ptDualToGlobal` take no proof as argument: they are defined as the inverse of
the duality map followed by `H_c → H` when the duality map is bijective, and `0` otherwise.

```lean
def ptLocalPairing (v : ι) {r s : ℕ} (h : r + s = 2) :
    cohomology (Rep.res (φ v : Hv v →* G) M) r →+
      cohomology (Rep.res (φ v : Hv v →* G) (dualRep D M)) s →+ QZ
def ptLocalDualMap [Fintype ι] {r s : ℕ} (h : r + s = 2) :
    (∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r) →+
      (cohomology (dualRep D M) s →+ QZ)
def ptCompactDualMap {r s : ℕ} (h : r + s = 3) :
    compactSupportCohomologyRes φ M r →+ (cohomology (dualRep D M) s →+ QZ)
noncomputable def ptDualToGlobal {r s : ℕ} (h : r + s = 3) :
    (cohomology (dualRep D M) s →+ QZ) →+ cohomology M r
theorem ptDualToGlobal_eq {r s : ℕ} (h : r + s = 3)
    (hψ : Function.Bijective (ptCompactDualMap φ D M t h)) :
    ptDualToGlobal φ D t M h =
      (ptCompactToGlobal φ M r).hom.toAddMonoidHom.comp
        (AddEquiv.ofBijective _ hψ).symm.toAddMonoidHom
structure PoitouTateDualityHypotheses : Prop where
  /-- The dualizing module is cyclic of order `n`. -/
  nonempty_addEquiv : Nonempty (D ≃+ ZMod n)
  /-- Duality `Hʳ(G, M') ≅ H_c^s(G, M)^∨` (`r + s = 3`) for finite modules killed by `n`. -/
  bijective_compactDualityMap : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective (compactDualityMap φ D h t M)
  /-- The cohomology groups of finite modules killed by `n` are finite. -/
  finite_cohomology : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, Finite (cohomology M r)
  /-- The compactly supported cohomology groups of finite modules killed by `n` are finite. -/
  finite_compactSupportCohomology : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ r, Finite (compactSupportCohomologyRes φ M r)
  /-- `H³` vanishes for finite modules killed by `n`. -/
  subsingleton_three : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → Subsingleton (cohomology M 3)
  /-- The trace `t` on `H_c^3(G, D)` restricts on the image of `∏_v H²(H_v, D)` to the sum of the local invariants. -/
  localToCompact_two : ∀ ξ : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2,
    zmodToQZ n (t ((localToCompact φ D _ (fun _ => 𝟙 _) 2).hom ξ)) = ∑ v, inv v (ξ v)
  /-- The local pairings in degrees `(0, 2)` are surjective onto the duals. -/
  surjective_localPairing : ∀ (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M],
    (∀ m : M, n • m = 0) → ∀ v,
      Function.Surjective (ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl))
structure IsNineTermExact : Prop where
  injective_globalToLocal_zero : Function.Injective (ptGlobalToLocal φ M 0).hom
  exact_globalToLocal_zero :
    Function.Exact (ptGlobalToLocal φ M 0).hom (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl))
  exact_localDualMap_zero :
    Function.Exact (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl))
      (ptDualToGlobal φ D t M (show 1 + 2 = 3 from rfl))
  exact_dualToGlobal_one :
    Function.Exact (ptDualToGlobal φ D t M (show 1 + 2 = 3 from rfl)) (ptGlobalToLocal φ M 1).hom
  exact_globalToLocal_one :
    Function.Exact (ptGlobalToLocal φ M 1).hom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl))
  exact_localDualMap_one :
    Function.Exact (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl))
      (ptDualToGlobal φ D t M (show 2 + 1 = 3 from rfl))
  exact_dualToGlobal_two :
    Function.Exact (ptDualToGlobal φ D t M (show 2 + 1 = 3 from rfl)) (ptGlobalToLocal φ M 2).hom
  exact_globalToLocal_two :
    Function.Exact (ptGlobalToLocal φ M 2).hom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl))
  surjective_localDualMap_two : Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl))
theorem PoitouTateDualityHypotheses.isNineTermExact (hM : ∀ m : M, n • m = 0) : IsNineTermExact φ D t inv M
def ptShaPairing : ptSha φ M 1 →+ ptSha φ (dualRep D M) 2 →+ QZ
theorem PoitouTateDualityHypotheses.bijective_ptShaPairing (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptShaPairing φ D M t)
theorem PoitouTateDualityHypotheses.bijective_ptShaPairing_flip (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptShaPairing φ D M t).flip
theorem PoitouTateDualityHypotheses.finite_ptSha_one (hM : ∀ m : M, n • m = 0) : Finite (ptSha φ M 1)
theorem PoitouTateDualityHypotheses.finite_ptSha_two (_hM : ∀ m : M, n • m = 0) : Finite (ptSha φ (dualRep D M) 2)
```

Variables: `ι` finite, `n ≠ 0`, `D : Rep.{u} (ULift.{u} ℤ) G` smooth, `t : compactSupportCohomologyRes φ D 3 →+ ZMod n`, `inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ`, `M : Rep.{u} (ULift.{u} ℤ) G` smooth and finite.

## Complete types

As printed by `#check` (all variables and instance arguments explicit; `↑(φ v)` is the coercion `(φ v : H v →* G)`):

```lean
@PoitouTateDualityHypotheses.isNineTermExact : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {n : ℕ} [NeZero n] {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G}
  [inst_8 : Langlands.IsSmoothRep D] {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
  PoitouTateDualityHypotheses φ D t inv → (∀ (m : ↑M), n • m = 0) → IsNineTermExact φ D t inv M

@PoitouTateDualityHypotheses.bijective_ptShaPairing : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {n : ℕ} [NeZero n] {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G}
  [inst_8 : Langlands.IsSmoothRep D] {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
  PoitouTateDualityHypotheses φ D t inv → (∀ (m : ↑M), n • m = 0) → Function.Bijective ⇑(ptShaPairing φ D M t)

@PoitouTateDualityHypotheses.bijective_ptShaPairing_flip : ∀ {G : Type u_1} [inst : Group G]
  [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1}
  [inst_3 : (v : ι) → Group (Hv v)] [inst_4 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)] {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {n : ℕ} [NeZero n]
  {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G} [inst_8 : Langlands.IsSmoothRep D]
  {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
  PoitouTateDualityHypotheses φ D t inv → (∀ (m : ↑M), n • m = 0) → Function.Bijective ⇑(ptShaPairing φ D M t).flip

@PoitouTateDualityHypotheses.finite_ptSha_one : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {n : ℕ} {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G}
  [inst_7 : Langlands.IsSmoothRep D] {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_8 : Langlands.IsSmoothRep M] [Finite ↑M],
  PoitouTateDualityHypotheses φ D t inv → (∀ (m : ↑M), n • m = 0) → Finite ↥(ptSha φ M 1)

@PoitouTateDualityHypotheses.finite_ptSha_two : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
  [inst_2 : IsTopologicalGroup G] {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)]
  [inst_4 : (v : ι) → TopologicalSpace (Hv v)] [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)]
  {φ : (v : ι) → Hv v →ₜ* G} [inst_6 : Fintype ι] {n : ℕ} [NeZero n] {D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G}
  [inst_8 : Langlands.IsSmoothRep D] {t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n}
  {inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ}
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_9 : Langlands.IsSmoothRep M] [inst_10 : Finite ↑M],
  PoitouTateDualityHypotheses φ D t inv →
    (∀ (m : ↑M), n • m = 0) → Finite ↥(ptSha φ (Langlands.ProfiniteCohomology.dualRep D M) 2)

@ptDualToGlobal_eq : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G]
  {ι : Type u_1} {Hv : ι → Type u_1} [inst_3 : (v : ι) → Group (Hv v)] [inst_4 : (v : ι) → TopologicalSpace (Hv v)]
  [inst_5 : ∀ (v : ι), IsTopologicalGroup (Hv v)] (φ : (v : ι) → Hv v →ₜ* G) {n : ℕ}
  (D : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G) [inst_6 : Langlands.IsSmoothRep D]
  (t : ↑(compactSupportCohomologyRes φ D 3) →+ ZMod n) (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) G)
  [inst_7 : Langlands.IsSmoothRep M] [inst_8 : Finite ↑M] {r s : ℕ} (h : r + s = 3)
  (hψ : Function.Bijective ⇑(ptCompactDualMap φ D M t h)),
  ptDualToGlobal φ D t M h =
    (ModuleCat.Hom.hom (ptCompactToGlobal φ M r)).toAddMonoidHom.comp
      (AddEquiv.ofBijective (ptCompactDualMap φ D M t h) hψ).symm.toAddMonoidHom
```

Also:

* `compactSupportCohomologyResMap_ptLocalToCompact`: the map `∏_v Hⁿ(H_v, ·) → H_cⁿ⁺¹(G, ·)` is natural
  in the coefficients (with `resMorphism` of `Langlands.GaloisCohomology.CompactSupport.Functoriality`);
* `tensorHom_toDualDual_ptLocalEval`, `ptLocalPairing_dual_toDualDual`: **the sign rule of the local
  pairings in degree one**, `⟨y, x⟩_{M'} = -⟨x, y⟩_M` for `x ∈ H¹(H_v, M)`, `y ∈ H¹(H_v, M')`, `M` mapped
  to `M'' = Hom(Hom(M, D), D)` by evaluation (graded commutativity of the cup product,
  `coeffMap_braiding_cup`).

Their complete types, as printed by `PrettyPrinter.ppSignature`:

```lean
Langlands.GaloisCohomology.compactSupportCohomologyResMap_ptLocalToCompact.{u} {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ι : Type u} {Hv : ι → Type u} [(v : ι) → Group (Hv v)]
  [(v : ι) → TopologicalSpace (Hv v)] [∀ (v : ι), IsTopologicalGroup (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  {A B : Rep.{u, u, u} (ULift.{u, 0} ℤ) G} [Langlands.IsSmoothRep A] [Langlands.IsSmoothRep B] (g : A ⟶ B) (m : ℕ)
  (ξ : (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) A) m)) :
  (ModuleCat.Hom.hom (Langlands.GaloisCohomology.compactSupportCohomologyResMap φ g (m + 1)))
      ((ModuleCat.Hom.hom (Langlands.GaloisCohomology.ptLocalToCompact φ A m)) ξ) =
    (ModuleCat.Hom.hom (Langlands.GaloisCohomology.ptLocalToCompact φ B m)) fun v =>
      (ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.coeffMap (Langlands.GaloisCohomology.resMorphism φ g v) m))
        (ξ v)
Langlands.GaloisCohomology.tensorHom_toDualDual_ptLocalEval.{u} {G : Type u} [Group G] [TopologicalSpace G] {ι : Type u}
  {Hv : ι → Type u} [(v : ι) → Group (Hv v)] [(v : ι) → TopologicalSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  (D M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) (v : ι) :
  CategoryTheory.CategoryStruct.comp
      (CategoryTheory.MonoidalCategoryStruct.tensorHom
        (CategoryTheory.CategoryStruct.id (Rep.res (↑(φ v)) (Langlands.ProfiniteCohomology.dualRep D M)))
        ((Rep.resFunctor ↑(φ v)).map (Langlands.ProfiniteCohomology.toDualDual D M)))
      (Langlands.GaloisCohomology.ptLocalEval φ D (Langlands.ProfiniteCohomology.dualRep D M) v) =
    CategoryTheory.CategoryStruct.comp
      (β_ (Rep.res (↑(φ v)) (Langlands.ProfiniteCohomology.dualRep D M)) (Rep.res (↑(φ v)) M)).hom
      (Langlands.GaloisCohomology.ptLocalEval φ D M v)
Langlands.GaloisCohomology.ptLocalPairing_dual_toDualDual.{u} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {ι : Type u} {Hv : ι → Type u} [(v : ι) → Group (Hv v)] [(v : ι) → TopologicalSpace (Hv v)]
  [∀ (v : ι), IsTopologicalGroup (Hv v)] [∀ (v : ι), CompactSpace (Hv v)] (φ : (v : ι) → Hv v →ₜ* G)
  (D : Rep.{u, u, u} (ULift.{u, 0} ℤ) G) [Langlands.IsSmoothRep D] (M : Rep.{u, u, u} (ULift.{u, 0} ℤ) G)
  [Langlands.IsSmoothRep M] [Finite ↑M] [Langlands.IsSmoothRep (Langlands.ProfiniteCohomology.dualRep D M)]
  [Finite ↑(Langlands.ProfiniteCohomology.dualRep D M)]
  [∀ (v : ι),
      Langlands.IsSmoothRep
        (Rep.res (↑(φ v)) (Langlands.ProfiniteCohomology.dualRep D (Langlands.ProfiniteCohomology.dualRep D M)))]
  (inv :
    (v : ι) → ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) D) 2) →+ Langlands.ProfiniteCohomology.QZ)
  (v : ι) (x : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) M) 1))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Rep.res (↑(φ v)) (Langlands.ProfiniteCohomology.dualRep D M)) 1)) :
  ((Langlands.GaloisCohomology.ptLocalPairing φ D (Langlands.ProfiniteCohomology.dualRep D M) inv v ⋯) y)
      ((ModuleCat.Hom.hom
          (Langlands.ProfiniteCohomology.coeffMap
            ((Rep.resFunctor ↑(φ v)).map (Langlands.ProfiniteCohomology.toDualDual D M)) 1))
        x) =
    -((Langlands.GaloisCohomology.ptLocalPairing φ D M inv v ⋯) x) y
```

## Outline of the proofs

The exact sequence of cohomology with compact support (`Basic.lean`) is transported along
the duality isomorphisms `H_c^r(M) ≅ H^{3−r}(M')^∨`: the map `Pʳ → H^{2−r}(M')^∨` is the composite
of `localToCompact` with the duality map (`ptCompactDualMap_ptLocalToCompact`, from the compatibility
of the trace with the local invariants and of cup products with `localToCompact`), so exactness at
each place follows from exactness of the compact support sequence under additive isomorphisms
(`exact_comp_addEquiv` and its variants). Injectivity at `H⁰` uses `H_c^0 = 0`, surjectivity at the
end uses `H³ = 0`. The pairing of `Ш¹(M)` with `Ш²(M')` lifts `x ∈ Ш¹(M)` to `H_c^1(M)` and pairs it
with the classes of `Ш²(M')`; it is perfect by the duality isomorphism and the surjectivity of the
local pairings in degree `0`; perfectness of the flipped pairing follows by counting.

## Declarations

`ptGlobalToLocal`, `ptCompactToGlobal`, `ptLocalToCompact`, `ptRes`, `ptGlobalToLocal_apply`, `ptExact_global`, `ptExact_local`, `ptExact_compact`, `ptSha`, `mem_ptSha`, `ptRes_eq_zero_of_mem_ptSha`, `ptCompactToGlobal_mem_ptSha`, `exists_ptCompactToGlobal_eq_of_mem_ptSha`, `exists_ptLocalToCompact_eq_of_ptCompactToGlobal_eq_zero`, `isSmoothRep_res_dualRep_of_finite`, `ptLocalEval`, `ptLocalPairing`, `ptLocalPairing_apply`, `ptLocalDualMap`, `ptLocalDualMap_apply`, `ptCompactDualMap`, `ptCompactDualMap_apply`, `compactCupRes_ptLocalToCompact`, `ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero`, `ptShaLift`, `ptCompactToGlobal_ptShaLift`, `ptShaPairing`, `ptShaPairing_apply`, `exact_comp_addEquiv`, `exact_addEquiv_comp_comp_symm`, `exact_comp_symm_addEquiv`, `bijective_compHom_zmodToQZ`, `bijective_flip_of_bijective_qz`, `ptDualToGlobal`, `ptDualToGlobal_eq`, `PoitouTateDualityHypotheses`, `IsNineTermExact`, `bijective_ptCompactDualMap`, `subsingleton_compactSupportCohomologyRes_zero`, `ptCompactDualMap_ptLocalToCompact`, `exact_stage`, `injective_ptGlobalToLocal_zero`, `surjective_ptLocalDualMap_two`, `isNineTermExact`, `bijective_ptShaPairing`, `finite_ptSha_one`, `finite_ptSha_two`, `bijective_ptShaPairing_flip`, `compactSupportCohomologyResMap_ptLocalToCompact`, `tensorHom_toDualDual_ptLocalEval`, `ptLocalPairing_dual_toDualDual`.

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis` (<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files `src/GroundTheory/ProfiniteCohomology/PoitouTate/PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero.lean`, `PoitouTate/Abstract.lean` (lines 15–69 and 98–104 only) and `PoitouTate/General.lean`. The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). The Library's cochains, restriction and coefficient maps (`cochains`, `cochainsMap φ`, `map φ`, `coeffCochainsMap`, `coeffMap`, `IsSmoothRep`) replace the source's (`cochainsComplex`, `cochainsMapAlong`, `cohomologyMapAlong`, `cochainsMap`, `cohomologyMap`, `IsDiscreteRep`); restriction along a family is along the coercion `(φ v : H v →* G)`, while the Mackey parts keep `.toMonoidHom` as the foundations' Mackey API does; `compactCohomology*` names become `compactSupportCohomology*`, `compactCohomologyMap` → `compactSupportMap`, `compactδ` → `compactSupportδ`. Changes against the source: the structure `PoitouTateHypotheses` of `Abstract.lean` (never instantiated) and its repeated proofs are not taken; `ptDualToGlobal` no longer takes a proof of bijectivity (it is defined by cases on bijectivity, with `ptDualToGlobal_eq`); the nine-fold conjunction `nineTerm` is the structure `IsNineTermExact`; the conjunction `sha` is split into `finite_ptSha_one`, `finite_ptSha_two`, `bijective_ptShaPairing_flip`.

## References

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, Theorem 4.10, pp. 56–57 (the Poitou–Tate theorem: perfect pairing of `Ш¹(M)` and `Ш²(M^D)`, the nine-term exact sequence, and `H^r(G_S, M) ≅ ∏_{v real} H^r(K_v, M)` for `r ≥ 3`).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008; corrected printing 2013), chapter VIII, §6: Theorem (8.6.9), p. 488 (the pairing of `Ш¹` and `Ш²`), and (8.6.10), pp. 489–490 (the nine-term sequence of Poitou–Tate, with Tate's modified groups at the archimedean places in `P⁰`).
- J. Tate, *Duality theorems in Galois cohomology over number fields*, Proc. Internat. Congr. Mathematicians (Stockholm 1962), Inst. Mittag-Leffler 1963, pp. 288–295: §1, p. 288 (at the real and complex places `Hʳ` is Tate's modified cohomology `Ĥʳ`), and Theorem 3.1, p. 291 (the perfect pairing of `Ker²(k_S, M)` and `Ker¹(k_S, M')`, the nine-term exact sequence, `Hʳ(k_S, M) ≅ ∏_{P real} Hʳ(k_P, M)` for `r ≥ 3`).
