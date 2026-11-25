import Langlands.GaloisCohomology.CompactSupport.Duality

/-!
# The nine-term sequence of Poitou–Tate (abstract form)

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
-/

namespace Langlands.GaloisCohomology

open Langlands Langlands.ProfiniteCohomology

universe u

-- from PoitouTate/PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero.lean
section PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero

noncomputable section


open CategoryTheory MonoidalCategory


attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

section Sequence

variable (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M]

/-- The localization `Hʳ(G, M) → ∏_v Hʳ(H_v, M)` of the nine-term sequence. -/
abbrev ptGlobalToLocal (r : ℕ) :=
  globalToLocal φ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _) r

/-- The map `H_c^r(G, M) → Hʳ(G, M)` of the nine-term sequence. -/
abbrev ptCompactToGlobal (r : ℕ) :=
  compactToGlobal φ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _) r

/-- The map `∏_v Hʳ(H_v, M) → H_c^{r+1}(G, M)` of the nine-term sequence. -/
abbrev ptLocalToCompact (r : ℕ) :=
  localToCompact φ M (fun v => Rep.res (φ v : Hv v →* G) M) (fun _ => 𝟙 _) r

/-- Restriction `Hʳ(G, M) → Hʳ(H_v, M)` as an additive map. -/
def ptRes (v : ι) (r : ℕ) : cohomology M r →+ cohomology (Rep.res (φ v : Hv v →* G) M) r :=
  (map (φ v) (𝟙 _) r).hom.toAddMonoidHom

theorem ptGlobalToLocal_apply (r : ℕ) (x : cohomology M r) (v : ι) :
    (ptGlobalToLocal φ M r).hom x v = ptRes φ M v r x :=
  rfl

theorem ptExact_global (r : ℕ) :
    Function.Exact (ptCompactToGlobal φ M r).hom (ptGlobalToLocal φ M r).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactSupportCohomology_exact_global φ M _ (fun _ => 𝟙 _) r)

theorem ptExact_local (r : ℕ) :
    Function.Exact (ptGlobalToLocal φ M r).hom (ptLocalToCompact φ M r).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactSupportCohomology_exact_local φ M _ (fun _ => 𝟙 _) r)

theorem ptExact_compact (r : ℕ) :
    Function.Exact (ptLocalToCompact φ M r).hom (ptCompactToGlobal φ M (r + 1)).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (compactSupportCohomology_exact_compact φ M _ (fun _ => 𝟙 _) r)

/-- `Шʳ(M)`: the kernel of the localization `Hʳ(G, M) → ∏_v Hʳ(H_v, M)`. -/
def ptSha (r : ℕ) : AddSubgroup (cohomology M r) :=
  (ptGlobalToLocal φ M r).hom.toAddMonoidHom.ker

theorem mem_ptSha {r : ℕ} (x : cohomology M r) :
    x ∈ ptSha φ M r ↔ (ptGlobalToLocal φ M r).hom x = 0 :=
  AddMonoidHom.mem_ker

theorem ptRes_eq_zero_of_mem_ptSha {r : ℕ} {x : cohomology M r} (hx : x ∈ ptSha φ M r) (v : ι) :
    ptRes φ M v r x = 0 := by
  rw [← ptGlobalToLocal_apply, (mem_ptSha φ M x).1 hx]
  rfl

theorem ptCompactToGlobal_mem_ptSha {r : ℕ} (x : compactSupportCohomologyRes φ M r) :
    (ptCompactToGlobal φ M r).hom x ∈ ptSha φ M r :=
  (mem_ptSha φ M _).2 ((ptExact_global φ M r _).2 ⟨x, rfl⟩)

theorem exists_ptCompactToGlobal_eq_of_mem_ptSha {r : ℕ} {x : cohomology M r}
    (hx : x ∈ ptSha φ M r) : ∃ y : compactSupportCohomologyRes φ M r, (ptCompactToGlobal φ M r).hom y = x :=
  (ptExact_global φ M r x).1 ((mem_ptSha φ M x).1 hx)

theorem exists_ptLocalToCompact_eq_of_ptCompactToGlobal_eq_zero {r : ℕ}
    {x : compactSupportCohomologyRes φ M (r + 1)} (hx : (ptCompactToGlobal φ M (r + 1)).hom x = 0) :
    ∃ ξ : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r, (ptLocalToCompact φ M r).hom ξ = x :=
  (ptExact_compact φ M r x).1 hx

end Sequence

section Pairings

variable (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
  (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]

instance isSmoothRep_res_dualRep_of_finite {K : Type u} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (ψ : K →ₜ* G) : IsSmoothRep (Rep.res (ψ : K →* G) (dualRep D M)) :=
  have : IsSmoothRep (dualRep D M) := isSmoothRep_dualRep D M
  isSmoothRep_res ψ (dualRep D M)

/-- Evaluation `M ⊗ Hom(M, D) → D` restricted to `H_v`. -/
abbrev ptLocalEval (v : ι) :
    Rep.res (φ v : Hv v →* G) M ⊗ Rep.res (φ v : Hv v →* G) (dualRep D M) ⟶
      Rep.res (φ v : Hv v →* G) D :=
  (Rep.resFunctor (φ v : Hv v →* G)).map (evalPairing D M)

variable (inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ)

/-- The local pairing `Hʳ(H_v, M) × Hˢ(H_v, M') → ℚ/ℤ` (`r + s = 2`): cup product with evaluation
followed by the local invariant `inv_v`. -/
def ptLocalPairing (v : ι) {r s : ℕ} (h : r + s = 2) :
    cohomology (Rep.res (φ v : Hv v →* G) M) r →+
      cohomology (Rep.res (φ v : Hv v →* G) (dualRep D M)) s →+ QZ :=
  (AddMonoidHom.compHom (inv v)).comp (bilinAddHom (cupPairing (ptLocalEval φ D M v) h))

theorem ptLocalPairing_apply (v : ι) {r s : ℕ} (h : r + s = 2)
    (ξ : cohomology (Rep.res (φ v : Hv v →* G) M) r)
    (η : cohomology (Rep.res (φ v : Hv v →* G) (dualRep D M)) s) :
    ptLocalPairing φ D M inv v h ξ η = inv v (cupPairing (ptLocalEval φ D M v) h ξ η) :=
  rfl

/-- The map `∏_v Hʳ(H_v, M) → Hˢ(G, M')^∨` (`r + s = 2`): the sum of the local pairings with the
restrictions of global classes. -/
def ptLocalDualMap [Fintype ι] {r s : ℕ} (h : r + s = 2) :
    (∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r) →+
      (cohomology (dualRep D M) s →+ QZ) where
  toFun ξ := ∑ v, (ptLocalPairing φ D M inv v h (ξ v)).comp (ptRes φ (dualRep D M) v s)
  map_zero' := AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.zero_apply]
    exact Finset.sum_eq_zero fun v _ => DFunLike.congr_fun ((ptLocalPairing φ D M inv v h).map_zero) _
  map_add' ξ ξ' := AddMonoidHom.ext fun y => by
    rw [AddMonoidHom.add_apply, AddMonoidHom.finsetSum_apply, AddMonoidHom.finsetSum_apply,
      AddMonoidHom.finsetSum_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ =>
      DFunLike.congr_fun ((ptLocalPairing φ D M inv v h).map_add (ξ v) (ξ' v)) _

theorem ptLocalDualMap_apply [Fintype ι] {r s : ℕ} (h : r + s = 2)
    (ξ : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r) (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h ξ y =
      ∑ v, ptLocalPairing φ D M inv v h (ξ v) (ptRes φ (dualRep D M) v s y) := by
  change (∑ v, (ptLocalPairing φ D M inv v h (ξ v)).comp (ptRes φ (dualRep D M) v s)) y = _
  rw [AddMonoidHom.finsetSum_apply]
  rfl

variable {n : ℕ} (t : compactSupportCohomologyRes φ D 3 →+ ZMod n)

/-- The duality map `H_c^r(G, M) → Hˢ(G, M')^∨` (`r + s = 3`), with values in `ℚ/ℤ` through `ℤ/n →
ℚ/ℤ`. -/
def ptCompactDualMap {r s : ℕ} (h : r + s = 3) :
    compactSupportCohomologyRes φ M r →+ (cohomology (dualRep D M) s →+ QZ) :=
  (AddMonoidHom.compHom ((zmodToQZ n).comp t)).comp
    (bilinAddHom (compactCupRes φ (evalPairing D M) h))

theorem ptCompactDualMap_apply {r s : ℕ} (h : r + s = 3) (x : compactSupportCohomologyRes φ M r)
    (y : cohomology (dualRep D M) s) :
    ptCompactDualMap φ D M t h x y = zmodToQZ n (t (compactCupRes φ (evalPairing D M) h x y)) :=
  rfl

theorem compactCupRes_ptLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r) (y : cohomology (dualRep D M) s) :
    compactCupRes φ (evalPairing D M) h' ((ptLocalToCompact φ M r).hom ξ) y =
      (localToCompact φ D _ (fun _ => 𝟙 _) 2).hom
        (fun v => cupPairing (ptLocalEval φ D M v) h (ξ v) (ptRes φ (dualRep D M) v s y)) :=
  compactCup_localToCompact φ (evalPairing D M) _ _ h h' ξ y

theorem ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero {x : compactSupportCohomologyRes φ M 1}
    (hx : (ptCompactToGlobal φ M 1).hom x = 0) {y : cohomology (dualRep D M) 2}
    (hy : y ∈ ptSha φ (dualRep D M) 2) :
    ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) x y = 0 := by
  obtain ⟨ξ, rfl⟩ := exists_ptLocalToCompact_eq_of_ptCompactToGlobal_eq_zero φ M (r := 0) hx
  have h0 : (fun v => cupPairing (ptLocalEval φ D M v) (show 0 + 2 = 2 from rfl) (ξ v)
      (ptRes φ (dualRep D M) v 2 y)) = 0 := by
    funext v
    rw [ptRes_eq_zero_of_mem_ptSha φ (dualRep D M) hy v]
    exact map_zero _
  rw [ptCompactDualMap_apply, compactCupRes_ptLocalToCompact φ D M (show 0 + 2 = 2 from rfl), h0,
    map_zero, map_zero, map_zero]

/-- A lift of an element of `Ш¹(M)` to `H_c^1(G, M)` (a choice). -/
def ptShaLift (x : ptSha φ M 1) : compactSupportCohomologyRes φ M 1 :=
  (exists_ptCompactToGlobal_eq_of_mem_ptSha φ M x.2).choose

omit [Finite M] in
theorem ptCompactToGlobal_ptShaLift (x : ptSha φ M 1) :
    (ptCompactToGlobal φ M 1).hom (ptShaLift φ M x) = x :=
  (exists_ptCompactToGlobal_eq_of_mem_ptSha φ M x.2).choose_spec

/-- The pairing `Ш¹(M) × Ш²(M') → ℚ/ℤ`. -/
def ptShaPairing : ptSha φ M 1 →+ ptSha φ (dualRep D M) 2 →+ QZ where
  toFun x := (ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) (ptShaLift φ M x)).comp
    (ptSha φ (dualRep D M) 2).subtype
  map_zero' := by
    refine AddMonoidHom.ext fun y => ?_
    refine ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero φ D M t ?_ y.2
    rw [ptCompactToGlobal_ptShaLift]
    rfl
  map_add' x x' := by
    refine AddMonoidHom.ext fun y => ?_
    have hz := ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero φ D M t
      (x := ptShaLift φ M (x + x') - ptShaLift φ M x - ptShaLift φ M x') ?_ y.2
    · rw [map_sub, map_sub, AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, sub_sub,
        sub_eq_zero] at hz
      simpa using hz
    · rw [map_sub, map_sub, ptCompactToGlobal_ptShaLift, ptCompactToGlobal_ptShaLift,
        ptCompactToGlobal_ptShaLift]
      simp

theorem ptShaPairing_apply (x : compactSupportCohomologyRes φ M 1) (y : ptSha φ (dualRep D M) 2) :
    ptShaPairing φ D M t ⟨_, ptCompactToGlobal_mem_ptSha φ M x⟩ y =
      ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) x y := by
  have hz := ptCompactDualMap_eq_zero_of_ptCompactToGlobal_eq_zero φ D M t
    (x := ptShaLift φ M ⟨_, ptCompactToGlobal_mem_ptSha φ M x⟩ - x) ?_ y.2
  · rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero] at hz
    exact hz
  · rw [map_sub, ptCompactToGlobal_ptShaLift, sub_self]

end Pairings

end

end PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero

-- from PoitouTate/Abstract.lean
section Abstract

noncomputable section


open CategoryTheory MonoidalCategory


attribute [local instance 2000] Rep.hV2

section ExactTransport

variable {A B X Y C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup X] [AddCommGroup Y]
  [AddCommGroup C]

omit [AddCommGroup A] in

theorem exact_comp_addEquiv {f : A → B} {g : B →+ X} (hfg : Function.Exact f g) (e : X ≃+ Y) :
    Function.Exact f (e.toAddMonoidHom.comp g) := fun b => by
  rw [← hfg b, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.map_eq_zero_iff]

theorem exact_addEquiv_comp_comp_symm {g : B →+ X} {c : X → C} (hgc : Function.Exact g c)
    (e : X ≃+ Y) : Function.Exact (e.toAddMonoidHom.comp g) (c ∘ e.symm) := fun y => by
  rw [Function.comp_apply, hgc]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simp [hb]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by simp⟩

omit [AddCommGroup C] in

theorem exact_comp_symm_addEquiv {c : X → C} {β : C → A} (hcβ : Function.Exact c β) (e : X ≃+ Y) :
    Function.Exact (c ∘ e.symm) β := fun x => by
  rw [hcβ x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e z, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

theorem bijective_compHom_zmodToQZ {n : ℕ} [NeZero n] (β : X →+ Y →+ ZMod n)
    (hY : ∀ y : Y, n • y = 0) (hβ : Function.Bijective β) :
    Function.Bijective ((AddMonoidHom.compHom (zmodToQZ n)).comp β) := by
  refine ⟨fun x₁ x₂ hx => hβ.1 (AddMonoidHom.ext fun y => zmodToQZ_injective ?_), fun χ => ?_⟩
  · exact DFunLike.congr_fun hx y
  · have hχ : ∀ y, n • χ y = 0 := fun y => by rw [← map_nsmul, hY, map_zero]
    obtain ⟨x, hx⟩ := hβ.2 (zmodOfQZ χ hχ)
    refine ⟨x, AddMonoidHom.ext fun y => ?_⟩
    change zmodToQZ n (β x y) = χ y
    rw [hx, zmodToQZ_zmodOfQZ]

theorem bijective_flip_of_bijective_qz [Finite X] [Finite Y] (β : X →+ Y →+ QZ)
    (hβ : Function.Bijective β) : Function.Bijective β.flip := by
  have hinj : Function.Injective β.flip := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    by_contra hne
    obtain ⟨χ, hχ⟩ := QZ.exists_apply_ne_zero hne
    obtain ⟨x, rfl⟩ := hβ.2 χ
    exact hχ (DFunLike.congr_fun hy x)
  refine hinj.bijective_of_nat_card_le ?_
  rw [QZ.card_hom, ← QZ.card_hom (G := Y)]
  exact (Nat.card_congr (Equiv.ofBijective _ hβ)).le

end ExactTransport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
  (t : compactSupportCohomologyRes φ D 3 →+ ZMod n)
  (inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ)

variable (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]

open Classical in
/-- The map `Hˢ(G, M')^∨ → Hʳ(G, M)` of the nine-term sequence (`r + s = 3`, `M' = Hom(M, D)`):
the inverse of the duality map `H_c^r(G, M) → Hˢ(G, M')^∨` followed by `H_c^r → Hʳ`. It is defined
as `0` when the duality map is not bijective; under the hypotheses of the duality theorem it is the
intended map (`ptDualToGlobal_eq`). -/
noncomputable def ptDualToGlobal {r s : ℕ} (h : r + s = 3) :
    (cohomology (dualRep D M) s →+ QZ) →+ cohomology M r :=
  if hψ : Function.Bijective (ptCompactDualMap φ D M t h) then
    (ptCompactToGlobal φ M r).hom.toAddMonoidHom.comp (AddEquiv.ofBijective _ hψ).symm.toAddMonoidHom
  else 0

omit [Fintype ι] [NeZero n] in
theorem ptDualToGlobal_eq {r s : ℕ} (h : r + s = 3)
    (hψ : Function.Bijective (ptCompactDualMap φ D M t h)) :
    ptDualToGlobal φ D t M h =
      (ptCompactToGlobal φ M r).hom.toAddMonoidHom.comp
        (AddEquiv.ofBijective _ hψ).symm.toAddMonoidHom :=
  dite_eq_left hψ



end

end Abstract

-- from PoitouTate/General.lean
section General

noncomputable section


open CategoryTheory MonoidalCategory


attribute [local instance 2000] Rep.hV2

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) [Fintype ι]
  {n : ℕ} [NeZero n] (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
  (t : compactSupportCohomologyRes φ D 3 →+ ZMod n)
  (inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ)

/-- The hypotheses of the abstract nine-term sequence: `D ≅ ℤ/n`, bijectivity of the duality maps
`H_c^r × H^s → ℤ/n` for modules killed by `n`, finiteness of the cohomology groups, vanishing of
`H³`, compatibility of the trace with the local invariants in degree 2, and surjectivity of the
local pairings in degree 0. -/
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

variable (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]

variable (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M]

/-- Exactness of the nine-term sequence
`0 → H⁰(M) → P⁰ → H²(M')^∨ → H¹(M) → P¹ → H¹(M')^∨ → H²(M) → P² → H⁰(M')^∨ → 0`, where
`Pʳ = ∏_v Hʳ(H_v, M)`, `M' = Hom(M, D)`, the maps `Pʳ → H^{2-r}(M')^∨` are the sums of the local
pairings (`ptLocalDualMap`) and `H^{2-r}(M')^∨ → H^{r+1}(M)` are the connecting maps
(`ptDualToGlobal`). -/
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

namespace PoitouTateDualityHypotheses

variable {φ D t inv} (P : PoitouTateDualityHypotheses φ D t inv)

include P in

theorem bijective_ptCompactDualMap (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (ptCompactDualMap φ D M t h) := by
  have hD := P.nonempty_addEquiv
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv hD
  have : Finite D := finite_of_nonempty_addEquiv hD
  have : Finite (dualRep D M) := finite_dualRep
  have : Finite (dualRep D (dualRep D M)) := finite_dualRep
  have : IsSmoothRep (dualRep D M) := isSmoothRep_dualRep D M
  have : IsSmoothRep (dualRep D (dualRep D M)) := isSmoothRep_dualRep D (dualRep D M)
  have hMD : ∀ f : dualRep D M, n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hMDD : ∀ f : dualRep D (dualRep D M), n • f = 0 := nsmul_dualRep_eq_zero hnD
  have hφ := P.bijective_compactDualityMap (dualRep D M) hMD (r := s) (s := r) (by omega)
  have := P.finite_compactSupportCohomology (dualRep D (dualRep D M)) hMDD r
  have hflip := bijective_of_bijective_flip (nsmul_compactSupportCohomologyRes_eq_zero φ hMDD r)
    (bilinAddHom (compactCupRes φ (dualEvalPairing D (dualRep D M)) h)) t hφ
  set e := repIsoOfBijective (toDualDual D M) (bijective_toDualDual hD hM)
  have hg := bijective_compactSupportCohomologyResMap_of_comp_eq_id φ e.hom e.inv e.hom_inv_id e.inv_hom_id r
  have hμ : (toDualDual D M ⊗ₘ 𝟙 (dualRep D M)) ≫ dualEvalPairing D (dualRep D M) =
      (𝟙 M ⊗ₘ 𝟙 (dualRep D M)) ≫ evalPairing D M := by
    refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
    induction z using TensorProduct.inductionOn with
    | tmul a f => rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  let β : compactSupportCohomologyRes φ M r →+ (cohomology (dualRep D M) s →+ ZMod n) :=
    (AddMonoidHom.compHom t).comp (bilinAddHom (compactCupRes φ (evalPairing D M) h))
  have hβ : Function.Bijective β := by
    convert hflip.comp hg using 1
    funext x
    refine AddMonoidHom.ext fun y => ?_
    change t (compactCupRes φ (evalPairing D M) h x y) =
      t (compactCupRes φ (dualEvalPairing D (dualRep D M)) h
        ((compactSupportCohomologyResMap φ (toDualDual D M) r).hom x) y)
    rw [compactCupRes_compactSupportCohomologyResMap φ _ (evalPairing D M) _ (𝟙 _) hμ, coeffMap_id]
    rfl
  exact bijective_compHom_zmodToQZ β (nsmul_cohomology_eq_zero _ hMD s) hβ

include P in

theorem subsingleton_compactSupportCohomologyRes_zero (hM : ∀ m : M, n • m = 0) :
    Subsingleton (compactSupportCohomologyRes φ M 0) := by
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have hb := P.bijective_ptCompactDualMap M hM (show 0 + 3 = 3 from rfl)
  have : Subsingleton (cohomology (dualRep D M) 3) :=
    P.subsingleton_three (dualRep D M) (nsmul_dualRep_eq_zero hnD)
  refine ⟨fun a b => hb.1 (AddMonoidHom.ext fun y => ?_)⟩
  rw [Subsingleton.elim y 0, map_zero, map_zero]

omit [NeZero n] in
include P in

theorem ptCompactDualMap_ptLocalToCompact {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3)
    (ξ : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) M) r) :
    ptCompactDualMap φ D M t h' ((ptLocalToCompact φ M r).hom ξ) = ptLocalDualMap φ D M inv h ξ := by
  refine AddMonoidHom.ext fun y => ?_
  rw [ptCompactDualMap_apply, compactCupRes_ptLocalToCompact φ D M h h', P.localToCompact_two,
    ptLocalDualMap_apply]
  rfl

include P in

theorem exact_stage (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2) (h' : r + 1 + s = 3) :
    Function.Exact (ptGlobalToLocal φ M r).hom (ptLocalDualMap φ D M inv h) ∧
      Function.Exact (ptLocalDualMap φ D M inv h)
        (ptDualToGlobal φ D t M h') ∧
      Function.Exact (ptDualToGlobal φ D t M h')
        (ptGlobalToLocal φ M (r + 1)).hom := by
  rw [ptDualToGlobal_eq φ D t M h' (P.bijective_ptCompactDualMap M hM h')]
  set e := AddEquiv.ofBijective _ (P.bijective_ptCompactDualMap M hM h')
  have hlam : ptLocalDualMap φ D M inv h = e.toAddMonoidHom.comp (ptLocalToCompact φ M r).hom.toAddMonoidHom :=
    AddMonoidHom.ext fun ξ => (P.ptCompactDualMap_ptLocalToCompact M h h' ξ).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hlam]
    exact exact_comp_addEquiv (ptExact_local φ M r) e
  · rw [hlam]
    exact exact_addEquiv_comp_comp_symm (g := (ptLocalToCompact φ M r).hom.toAddMonoidHom)
      (ptExact_compact φ M r) e
  · exact exact_comp_symm_addEquiv (ptExact_global φ M (r + 1)) e

include P in

theorem injective_ptGlobalToLocal_zero (hM : ∀ m : M, n • m = 0) :
    Function.Injective (ptGlobalToLocal φ M 0).hom := by
  have := P.subsingleton_compactSupportCohomologyRes_zero M hM
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨z, rfl⟩ := (ptExact_global φ M 0 x).1 hx
  rw [Subsingleton.elim z 0]
  exact map_zero _

include P in

theorem surjective_ptLocalDualMap_two (hM : ∀ m : M, n • m = 0) :
    Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) := by
  intro χ
  set e := AddEquiv.ofBijective _ (P.bijective_ptCompactDualMap M hM (show 2 + 1 + 0 = 3 from rfl))
  have := P.subsingleton_three M hM
  obtain ⟨ξ, hξ⟩ := (ptExact_compact φ M 2 (e.symm χ)).1 (Subsingleton.elim _ _)
  refine ⟨ξ, ?_⟩
  rw [← P.ptCompactDualMap_ptLocalToCompact M _ (show 2 + 1 + 0 = 3 from rfl), hξ]
  exact e.apply_symm_apply χ

include P in
/-- The nine-term sequence of Poitou–Tate (abstract form) under `PoitouTateDualityHypotheses`. -/
theorem isNineTermExact (hM : ∀ m : M, n • m = 0) : IsNineTermExact φ D t inv M := by
  obtain ⟨a0, b0, c0⟩ := P.exact_stage M hM (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 3 from rfl)
  obtain ⟨a1, b1, c1⟩ := P.exact_stage M hM (show 1 + 1 = 2 from rfl) (show 1 + 1 + 1 = 3 from rfl)
  obtain ⟨a2, -, -⟩ := P.exact_stage M hM (show 2 + 0 = 2 from rfl) (show 2 + 1 + 0 = 3 from rfl)
  exact ⟨P.injective_ptGlobalToLocal_zero M hM, a0, b0, c0, a1, b1, c1, a2,
    P.surjective_ptLocalDualMap_two M hM⟩

include P in

theorem bijective_ptShaPairing (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptShaPairing φ D M t) := by
  classical
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have hMD : ∀ f : dualRep D M, n • f = 0 := nsmul_dualRep_eq_zero hnD
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have hψ := P.bijective_ptCompactDualMap M hM (show 1 + 2 = 3 from rfl)
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun χ => ?_⟩
  ·
    set f := ptCompactDualMap φ D M t (show 1 + 2 = 3 from rfl) (ptShaLift φ M x)
    have hker : (ptGlobalToLocal φ (dualRep D M) 2).hom.toAddMonoidHom.ker ≤ f.ker := fun y hy =>
      AddMonoidHom.mem_ker.2 (DFunLike.congr_fun hx ⟨y, hy⟩)
    obtain ⟨g, hg⟩ := QZ.exists_comp_eq_of_ker_le
      (ptGlobalToLocal φ (dualRep D M) 2).hom.toAddMonoidHom f hker
    have hloc : ∀ v, ∃ ξv, ptLocalPairing φ D M inv v (show 0 + 2 = 2 from rfl) ξv =
        g.comp (AddMonoidHom.single (fun w => cohomology (Rep.res (φ w : Hv w →* G) (dualRep D M)) 2) v) :=
      fun v => P.surjective_localPairing M hM v _
    choose ξ hξ using hloc
    have hf : ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl) ξ = f := by
      refine AddMonoidHom.ext fun y => ?_
      rw [ptLocalDualMap_apply, ← hg, AddMonoidHom.comp_apply]
      simp_rw [hξ, AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
      rw [← map_sum, Finset.univ_sum_single]
      rfl
    rw [← P.ptCompactDualMap_ptLocalToCompact M _ (show 0 + 1 + 2 = 3 from rfl)] at hf
    have hx' : (ptLocalToCompact φ M 0).hom ξ = ptShaLift φ M x := hψ.1 hf
    apply Subtype.ext
    rw [← ptCompactToGlobal_ptShaLift φ M x, ← hx']
    exact (ptExact_compact φ M 0 _).2 ⟨ξ, rfl⟩
  · obtain ⟨f, hf⟩ := QZ.exists_comp_eq_of_injective (ptSha φ (dualRep D M) 2).subtype
      Subtype.val_injective χ
    obtain ⟨x, hx⟩ := hψ.2 f
    refine ⟨⟨_, ptCompactToGlobal_mem_ptSha φ M x⟩, AddMonoidHom.ext fun y => ?_⟩
    rw [ptShaPairing_apply, hx, ← hf]
    rfl

omit [NeZero n] in
include P in
/-- `Ш¹(M)` is finite. -/
theorem finite_ptSha_one (hM : ∀ m : M, n • m = 0) : Finite (ptSha φ M 1) := by
  have := P.finite_cohomology M hM 1
  exact Finite.of_injective _ Subtype.val_injective

include P in
/-- `Ш²(M')` is finite, `M' = Hom(M, D)`. -/
theorem finite_ptSha_two (_hM : ∀ m : M, n • m = 0) : Finite (ptSha φ (dualRep D M) 2) := by
  have hnD := nsmul_eq_zero_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite D := finite_of_nonempty_addEquiv P.nonempty_addEquiv
  have : Finite (dualRep D M) := finite_dualRep
  have := P.finite_cohomology (dualRep D M) (nsmul_dualRep_eq_zero hnD) 2
  exact Finite.of_injective _ Subtype.val_injective

include P in
/-- The pairing `Ш¹(M) × Ш²(M') → ℚ/ℤ` is perfect: the flipped pairing is also bijective. -/
theorem bijective_ptShaPairing_flip (hM : ∀ m : M, n • m = 0) :
    Function.Bijective (ptShaPairing φ D M t).flip := by
  have := P.finite_ptSha_one M hM
  have := P.finite_ptSha_two M hM
  exact bijective_flip_of_bijective_qz _ (P.bijective_ptShaPairing M hM)

end PoitouTateDualityHypotheses



end

end General

section ResMap

open CategoryTheory

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D] {n : ℕ} (hD : ∀ d : D, n • d = 0)
  (U : OpenSubgroup G)

omit [CompactSpace G] [∀ v, CompactSpace (Hv v)] [IsSmoothRep D] in
/-- Naturality of `∏_v Hⁿ(H_v, ·) → H_cⁿ⁺¹(G, ·)` in the coefficients. -/
theorem compactSupportCohomologyResMap_ptLocalToCompact {A B : Rep.{u} (ULift.{u} ℤ) G}
    [IsSmoothRep A] [IsSmoothRep B] (g : A ⟶ B) (m : ℕ)
    (ξ : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) A) m) :
    (compactSupportCohomologyResMap φ g (m + 1)).hom ((ptLocalToCompact φ A m).hom ξ) =
      (ptLocalToCompact φ B m).hom (fun v => (coeffMap (resMorphism φ g v) m).hom (ξ v)) := by
  have h := congrArg (fun F => F.hom ξ) (localToCompact_compactSupportMap φ
    (Aᵥ := fun v => Rep.res (φ v : Hv v →* G) A) (Bᵥ := fun v => Rep.res (φ v : Hv v →* G) B)
    (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) g (fun v => (Rep.resFunctor (φ v : Hv v →* G)).map g)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) m)
  refine h.trans ?_
  simp only [resMorphism_eq]
  rfl

end ResMap

noncomputable section

open CategoryTheory MonoidalCategory

section Sign

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  (D : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep D]
  (M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep M] [Finite M] [IsSmoothRep (dualRep D M)]
  [Finite (dualRep D M)] [∀ v, IsSmoothRep (Rep.res (φ v : Hv v →* G) (dualRep D (dualRep D M)))]
  (inv : ∀ v, cohomology (Rep.res (φ v : Hv v →* G) D) 2 →+ QZ)

omit [IsTopologicalGroup G] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  [IsSmoothRep D] [IsSmoothRep M] [Finite M] [IsSmoothRep (dualRep D M)] [Finite (dualRep D M)]
  [∀ v, IsSmoothRep (Rep.res (φ v : Hv v →* G) (dualRep D (dualRep D M)))] in
/-- The evaluation of `M'` against the image of `M` in `M''` is the evaluation of `M` after the
braiding. -/
theorem tensorHom_toDualDual_ptLocalEval (v : ι) :
    (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v : Hv v →* G)).map (toDualDual D M)) ≫
        ptLocalEval φ D (dualRep D M) v =
      (β_ (Rep.res (φ v : Hv v →* G) (dualRep D M)) (Rep.res (φ v : Hv v →* G) M)).hom ≫
        ptLocalEval φ D M v := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul f m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The sign rule of the local pairings in degree one**: `⟨y, x⟩_{M'} = -⟨x, y⟩_M` for
`x ∈ H¹(H_v, M)`, `y ∈ H¹(H_v, M')`, `M` mapped to `M''` by evaluation. -/
theorem ptLocalPairing_dual_toDualDual (v : ι) (x : cohomology (Rep.res (φ v : Hv v →* G) M) 1)
    (y : cohomology (Rep.res (φ v : Hv v →* G) (dualRep D M)) 1) :
    ptLocalPairing φ D (dualRep D M) inv v (show 1 + 1 = 2 from rfl) y
        ((coeffMap ((Rep.resFunctor (φ v : Hv v →* G)).map (toDualDual D M)) 1).hom x) =
      -ptLocalPairing φ D M inv v (show 1 + 1 = 2 from rfl) x y := by
  rw [ptLocalPairing_apply, ptLocalPairing_apply, ← map_neg]
  congr 1
  have hc := cupPairing_cohomologyMap (ptLocalEval φ D (dualRep D M) v) (𝟙 _)
    ((Rep.resFunctor (φ v : Hv v →* G)).map (toDualDual D M)) (show 1 + 1 = 2 from rfl) y x
  rw [coeffMap_id, ModuleCat.id_apply] at hc
  rw [hc, tensorHom_toDualDual_ptLocalEval, cupPairing_apply, cupPairing_apply, coeffMap_comp,
    ModuleCat.comp_apply, coeffMap_braiding_cup (show 1 + 1 = 2 from rfl) (show 1 + 1 = 2 from rfl),
    show ((-1 : ULift.{u} ℤ) ^ (1 * 1)) = -1 by simp, neg_one_smul, map_neg]

end Sign

end

end Langlands.GaloisCohomology
