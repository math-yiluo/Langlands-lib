import Langlands.GaloisCohomology.Global.Units.DivisorModule

/-!
# Counting components of divisor classes

Let `G` be a profinite group, `φ_i : H_i →ₜ* G` continuous homomorphisms from profinite groups, and
`D = divisorModule φ ℤ`. Suppose the image of `H_i` is *topologically cyclic up to every
neighbourhood of `1`*: for every neighbourhood `V` of `1` there is `h₀ ∈ H_i` such that every
`φ_i(h)` lies in `φ_i(h₀)^k V` for some `k ∈ ℤ`.

* `card_le_of_topologicallyCyclic`: then the components at `i` (in `H²(H_i, ℤ)`) of the classes of
  `H²(G, D)`, among the classes killed by `m ≠ 0`, are at most `m` in number. A component is the
  connecting image of a homomorphism `H_i → ℚ/ℤ` factoring through `φ_i` up to a neighbourhood of `1`
  (`H²(G, D) ≅ H¹(G, D(ℚ/ℤ))`), and such homomorphisms killed by `m` are determined by their value at
  `h₀`, an element of `(1/m)ℤ/ℤ`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology

universe u

noncomputable section

section Torsion

/-- An element of `ℚ/ℤ` killed by `m ≠ 0` is the class of `k / m` for some `0 ≤ k < m`. -/
theorem exists_fin_eq_of_nsmul_eq_zero {m : ℕ} (hm : m ≠ 0) {a : ULift.{u} QZ} (ha : m • a = 0) :
    ∃ k : Fin m, a = ULift.up (ratToQZ ((k : ℚ) / m)) := by
  obtain ⟨q, hq⟩ := ratToQZ_surjective a.down
  have hmq : ratToQZ ((m : ℚ) * q) = 0 := by
    have h1 : (m • a).down = 0 := congrArg ULift.down ha
    have h2 : (m • a).down = m • a.down := rfl
    rw [h2, ← hq, ← map_nsmul, nsmul_eq_mul] at h1
    exact h1
  obtain ⟨n, hn⟩ := (ratToQZ_eq_zero_iff _).1 hmq
  have hm' : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmod := Int.emod_nonneg n hm'.ne'
  have hlt := Int.emod_lt_of_pos n hm'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hmod
  have hkm : k < m := by omega
  refine ⟨⟨k, hkm⟩, ULift.ext ?_⟩
  change a.down = ratToQZ ((k : ℚ) / (m : ℚ))
  rw [← hq]
  have hmq0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnm : (n : ℚ) = (m : ℚ) * ((n / m : ℤ) : ℚ) + (k : ℚ) := by
    have e := Int.emod_def n m
    have e' : n = (m : ℤ) * (n / m) + (k : ℤ) := by rw [← hk, e]; ring
    exact_mod_cast e'
  have hq' : q = ((n / m : ℤ) : ℚ) + (k : ℚ) / m := by
    field_simp
    linarith [hn, hnm]
  rw [hq', map_add]
  have h0 : ratToQZ (((n / m : ℤ) : ℚ)) = 0 := (ratToQZ_eq_zero_iff _).2 ⟨n / m, rfl⟩
  rw [h0, zero_add]

/-- The elements of `ℚ/ℤ` killed by `m ≠ 0`, as a finite set of at most `m` elements containing them
all. -/
theorem exists_finset_nsmul_eq_zero {m : ℕ} (hm : m ≠ 0) :
    ∃ T : Finset (ULift.{u} QZ), T.card ≤ m ∧ ∀ a : ULift.{u} QZ, m • a = 0 → a ∈ T := by
  classical
  refine ⟨Finset.univ.image fun k : Fin m => ULift.up (ratToQZ ((k : ℚ) / m)), ?_, fun a ha => ?_⟩
  · exact (Finset.card_image_le).trans (by rw [Finset.card_univ, Fintype.card_fin])
  · obtain ⟨k, rfl⟩ := exists_fin_eq_of_nsmul_eq_zero hm ha
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩

end Torsion

section Count

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {I : Type u} {H : I → Type u} [∀ i, Group (H i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, CompactSpace (H i)]
  [∀ i, TotallyDisconnectedSpace (H i)] (φ : ∀ i, H i →ₜ* G)

omit [∀ i, CompactSpace (H i)] [∀ i, TotallyDisconnectedSpace (H i)] in
/-- The component at `i` of a class of `H²(G, D)` is the connecting image of a cocycle of `H_i` with
values in `ℚ/ℤ` which is constant on the cosets of a neighbourhood of `1` pulled back by `φ_i`. -/
theorem exists_cocycle_of_divisorEval (i : I) (d : cohomology (divisorModule φ (ULift.{u} ℤ)) 2) :
    ∃ (w : cocycles (trivialSequence (H i)).X₃ 1) (V : Set G), V ∈ nhds (1 : G) ∧
      (δ (trivialSequence_shortExact (H i)) 1 2 rfl).hom ((cohomologyπ _ 1).hom w) =
        (map (φ i) (divisorEval φ (ULift.{u} ℤ) i) 2).hom d ∧
      ∀ h h' : H i, (φ i h)⁻¹ * φ i h' ∈ V →
        cocycleFun _ w (fun _ => h) = cocycleFun _ w (fun _ => h') := by
  have hS := divisorSequence_shortExact φ
  have hT := trivialSequence_shortExact (H i)
  have h2 : IsZero (cohomology (divisorSequence φ).X₂ 2) :=
    isZero_cohomology_divisorModule_rat φ (by norm_num)
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 1 2 rfl) d
    ((ModuleCat.subsingleton_of_isZero h2).elim _ _)
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 y
  set c : (Fin 1 → G) → divisorFunctions φ (ULift.{u} QZ) := cocycleFun (divisorSequence φ).X₃ z
    with hc
  have hlcx : IsLocallyConstant fun x : G => c fun _ => x :=
    (isLocallyConstant_cocycleFun _ z).comp_continuous (continuous_pi fun _ => continuous_id)
  obtain ⟨V, hV, hVc⟩ := exists_mem_nhds_one_forall_mul_eq hlcx
  refine ⟨cocyclesMap (φ i) (divisorEvalSequence φ i).τ₃ 1 z, V, hV, ?_, fun h h' hh => ?_⟩
  · have e := congrArg (fun ψ => ψ.hom ((cohomologyπ _ 1).hom z))
      (δ_comp_map (φ i) (divisorEvalSequence φ i) hS hT 1 2 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at e
    rw [← cohomologyπ_map_apply, ← e]
    exact congrArg _ hy
  · have key : cocycleFun (trivialSequence (H i)).X₃
        (cocyclesMap (φ i) (divisorEvalSequence φ i).τ₃ 1 z) =
        fun g => (divisorEval φ (ULift.{u} QZ) i).hom (c (⇑(φ i) ∘ g)) :=
      cochainOf_cocycleι_cocyclesMap (φ i) (divisorEvalSequence φ i).τ₃ z
    rw [key]
    have e := hVc (φ i h) _ hh
    rw [mul_inv_cancel_left] at e
    change (divisorEval φ (ULift.{u} QZ) i).hom (c fun _ => φ i h) =
      (divisorEval φ (ULift.{u} QZ) i).hom (c fun _ => φ i h')
    rw [e]

/-- A cocycle of a group with values in a trivial module is a homomorphism. -/
theorem cocycleFun_mul_trivial {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (w : cocycles (trivialSequence K).X₃ 1) (g h : K) :
    cocycleFun _ w (fun _ => g * h) = cocycleFun _ w (fun _ => g) + cocycleFun _ w (fun _ => h) := by
  rw [cocycle_mul_of_d_eq_zero (d_cocycleFun _ w) g h, add_comm]
  rfl

/-- **Counting components.** If the image of `H_i` is topologically cyclic up to every neighbourhood
of `1`, at most `m` classes of `H²(H_i, ℤ)` killed by `m` are components at `i` of classes of
`H²(G, D)`. -/
theorem card_le_of_topologicallyCyclic (i : I) {m : ℕ} (hm : m ≠ 0)
    (hcyc : ∀ V ∈ nhds (1 : G), ∃ h₀ : H i, ∀ h : H i, ∃ k : ℤ, (φ i (h₀ ^ k))⁻¹ * φ i h ∈ V)
    (s : Finset (cohomology (trivialModule (H i) (ULift.{u} ℤ)) 2))
    (hs : ∀ c ∈ s, m • c = 0 ∧ ∃ d : cohomology (divisorModule φ (ULift.{u} ℤ)) 2,
      (map (φ i) (divisorEval φ (ULift.{u} ℤ) i) 2).hom d = c) :
    s.card ≤ m := by
  classical
  have hT := trivialSequence_shortExact (H i)
  have key : ∀ c ∈ s, ∃ (w : cocycles (trivialSequence (H i)).X₃ 1) (V : Set G),
      V ∈ nhds (1 : G) ∧ (δ hT 1 2 rfl).hom ((cohomologyπ _ 1).hom w) = c ∧
      ∀ h h' : H i, (φ i h)⁻¹ * φ i h' ∈ V →
        cocycleFun _ w (fun _ => h) = cocycleFun _ w (fun _ => h') := by
    intro c hc
    obtain ⟨-, d, rfl⟩ := hs c hc
    exact exists_cocycle_of_divisorEval φ i d
  choose w V hV hwc hwV using key
  -- the cocycles are killed by `m`
  have hδinj : Function.Injective (δ hT 1 2 rfl).hom := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨r, hr⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hT 1 2 rfl) x hx
    have hr0 : r = 0 := (ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_trivialModule_rat (H i) le_rfl)).elim _ _
    rw [← hr, hr0, map_zero]
    exact Submodule.zero_mem _
  have hwm : ∀ (c : _) (hc : c ∈ s) (h : H i), m • cocycleFun _ (w c hc) (fun _ => h) = 0 := by
    intro c hc h
    have h1 : (cohomologyπ _ 1).hom (m • w c hc) = 0 := by
      apply hδinj
      rw [map_nsmul, map_nsmul, hwc, map_zero]
      exact (hs c hc).1
    have hev := congrArg (H1Eval (trivialSequence (H i)).X₃ h).hom h1
    rw [map_zero, H1Eval_cohomology_class_apply, Submodule.Quotient.mk_eq_zero] at hev
    obtain ⟨a, ha⟩ := hev
    have h0 : ((trivialSequence (H i)).X₃.ρ h - 1) a = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      rfl
    rw [h0] at ha
    have hlin : cocycleFun _ (m • w c hc) = m • cocycleFun _ (w c hc) := by
      unfold cocycleFun
      rw [map_nsmul]
      rfl
    have := congrFun hlin fun _ => h
    rw [← ha] at this
    exact this.symm
  -- a common neighbourhood and a generator
  let W : Set G := ⋂ c ∈ s.attach, V c.1 c.2
  have hW : W ∈ nhds (1 : G) :=
    (Filter.biInter_finset_mem s.attach).2 fun c _ => hV c.1 c.2
  obtain ⟨h₀, hh₀⟩ := hcyc W hW
  choose kf hkf using hh₀
  -- every cocycle is determined by its value at `h₀`
  have hdet : ∀ (c : _) (hc : c ∈ s) (h : H i),
      cocycleFun _ (w c hc) (fun _ => h) = kf h • cocycleFun _ (w c hc) (fun _ => h₀) := by
    intro c hc h
    have hkW : (φ i (h₀ ^ kf h))⁻¹ * φ i h ∈ V c hc :=
      Set.mem_iInter₂.1 (hkf h) ⟨c, hc⟩ (Finset.mem_attach _ _)
    refine (hwV c hc _ _ hkW).symm.trans ?_
    let F : Additive (H i) →+ ULift.{u} QZ :=
      { toFun := fun x => cocycleFun _ (w c hc) (fun _ => Additive.toMul x)
        map_zero' := by
          have e := cocycleFun_mul_trivial (w c hc) (1 : H i) 1
          rw [mul_one] at e
          change cocycleFun _ (w c hc) (fun _ => 1) = 0
          exact left_eq_add.1 e
        map_add' := fun x y => cocycleFun_mul_trivial (w c hc) _ _ }
    exact map_zsmul F (kf h) (Additive.ofMul h₀)
  obtain ⟨T, hTcard, hTmem⟩ := exists_finset_nsmul_eq_zero.{u} hm
  let f : cohomology (trivialModule (H i) (ULift.{u} ℤ)) 2 → ULift.{u} QZ := fun c =>
    if hc : c ∈ s then cocycleFun _ (w c hc) (fun _ => h₀) else 0
  have hf : ∀ (c : _) (hc : c ∈ s), f c = cocycleFun _ (w c hc) (fun _ => h₀) := fun c hc => by
    exact dite_eq_left hc
  have hmaps : ∀ c ∈ s, f c ∈ T := fun c hc => by
    rw [hf c hc]
    exact hTmem _ (hwm c hc h₀)
  have hinj : Set.InjOn f s := by
    intro c hc c' hc' hff
    rw [hf c hc, hf c' hc'] at hff
    have hfun : cocycleFun _ (w c hc) = cocycleFun _ (w c' hc') := by
      funext g
      have hg : g = fun _ => g 0 := funext fun j => by rw [Subsingleton.elim j 0]
      rw [hg, hdet c hc, hdet c' hc', hff]
    have := cocycleFun_injective _ hfun
    rw [← hwc c hc, ← hwc c' hc', this]
  exact (Finset.card_le_card_of_injOn f hmaps hinj).trans hTcard

end Count

end

end Langlands.GaloisCohomology
