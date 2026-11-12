import Langlands.Geometry.Building.RankZeroAffineRootSystem
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.Tactic

/-! # Special points of affine root systems, including rank zero -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Set Module

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

include hΨ

private theorem finiteDimensional_translation : FiniteDimensional ℝ V := by
  have : Module.Finite ℝ (Module.Dual ℝ V) :=
    Module.Finite.of_fg_top (hΨ.span_derivativeRoots_eq_top ▸
      Submodule.fg_span hΨ.finite_derivativeRoots)
  exact (Module.finite_dual_iff ℝ).mp this

/-- A chosen affine root with the prescribed derivative. -/
def derivativeRootLift (_hΨ : IsAffineRootSystemWithRankZero Ψ)
    (a : derivativeRoots Ψ) : A →ᵃ[ℝ] ℝ :=
  a.property.choose

theorem derivativeRootLift_mem (a : derivativeRoots Ψ) :
    hΨ.derivativeRootLift a ∈ Ψ :=
  a.property.choose_spec.1

@[simp] theorem linear_derivativeRootLift (a : derivativeRoots Ψ) :
    (hΨ.derivativeRootLift a).linear = a.val :=
  a.property.choose_spec.2

/-- The coroot vector of the chosen lift. -/
def derivativeCoroot (a : derivativeRoots Ψ) : V :=
  (hΨ.exists_isCoroot _ (hΨ.derivativeRootLift_mem a)).choose

theorem isCoroot_derivativeCoroot (a : derivativeRoots Ψ) :
    IsCoroot Ψ (hΨ.derivativeRootLift a) (hΨ.derivativeCoroot a) :=
  (hΨ.exists_isCoroot _ (hΨ.derivativeRootLift_mem a)).choose_spec

theorem derivative_apply_coroot (a : derivativeRoots Ψ) :
    a.val (hΨ.derivativeCoroot a) = 2 := by
  simpa only [hΨ.linear_derivativeRootLift] using (hΨ.isCoroot_derivativeCoroot a).1

theorem mapsTo_derivativeReflection (a : derivativeRoots Ψ) :
    MapsTo (Module.preReflection a.val (Module.Dual.eval ℝ V (hΨ.derivativeCoroot a)))
      (derivativeRoots Ψ) (derivativeRoots Ψ) := by
  rintro _ ⟨η, hη, rfl⟩
  refine ⟨η - η.linear (hΨ.derivativeCoroot a) • hΨ.derivativeRootLift a,
    (hΨ.isCoroot_derivativeCoroot a).2 η hη, ?_⟩
  simp [Module.preReflection_apply]

theorem derivativeCoroot_injective : Function.Injective hΨ.derivativeCoroot := by
  have : IsAddTorsionFree (Module.Dual ℝ V) := .of_isTorsionFree ℝ _
  intro a b hab
  apply Subtype.ext
  exact Module.eq_of_mapsTo_reflection_of_mem hΨ.finite_derivativeRoots
    (hΨ.derivative_apply_coroot a) (hΨ.derivative_apply_coroot b)
    (hab ▸ hΨ.derivative_apply_coroot a) (hab.symm ▸ hΨ.derivative_apply_coroot b)
    (hΨ.mapsTo_derivativeReflection a) (hΨ.mapsTo_derivativeReflection b) b.property

/-- The finite root pairing of derivatives, on the actual translation space and its dual. -/
def derivativePairing : RootPairing (derivativeRoots Ψ) ℝ (Module.Dual ℝ V) V := by
  let := hΨ.finite_derivativeRoots.fintype
  let := hΨ.finiteDimensional_translation
  have hrange : range (Function.Embedding.subtype (fun a => a ∈ derivativeRoots Ψ)) =
      derivativeRoots Ψ := by ext; simp
  exact RootPairing.mk'' (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)
    (Function.Embedding.subtype _) ⟨hΨ.derivativeCoroot, hΨ.derivativeCoroot_injective⟩
    hΨ.derivative_apply_coroot
    (by intro a; rw [hrange]; exact hΨ.mapsTo_derivativeReflection a)
    (by rw [hrange]; exact hΨ.span_derivativeRoots_eq_top)

@[simp] theorem derivativePairing_root (a : derivativeRoots Ψ) :
    hΨ.derivativePairing.root a = a.val := rfl

@[simp] theorem derivativePairing_coroot (a : derivativeRoots Ψ) :
    hΨ.derivativePairing.coroot a = hΨ.derivativeCoroot a := rfl

instance derivativePairing_isCrystallographic : hΨ.derivativePairing.IsCrystallographic where
  exists_value a b := by
    obtain ⟨n, hn⟩ := hΨ.coroot_integral _ (hΨ.derivativeRootLift_mem a)
      _ (hΨ.derivativeRootLift_mem b) _ (hΨ.isCoroot_derivativeCoroot b)
    refine ⟨n, ?_⟩
    change (n : ℝ) = a.val (hΨ.derivativeCoroot b)
    simpa only [hΨ.linear_derivativeRootLift] using hn.symm

end IsAffineRootSystemWithRankZero

/-! The next elementary descent lemmas adapt the published simple-reflection
generation argument in `Langlands.Group.RootPairingWeylGeneration`. -/

section SimpleRootDescent

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [Finite ι] [P.IsCrystallographic]
  (f : Module.Dual ℝ M)

omit [P.IsCrystallographic] in
private lemma root_mem_simple_closure {i : ι} (hi : 0 < f (P.root i)) :
    P.root i ∈ AddSubmonoid.closure
      (P.root '' IsAddIndecomposable.baseOf P.root (f : M →+ ℝ)) := by
  rw [AddSubmonoid.closure_image_isAddIndecomposable_baseOf P.root (f : M →+ ℝ)]
  exact AddSubmonoid.subset_closure ⟨i, hi, rfl⟩

omit [P.IsCrystallographic] in
private lemma neg_root_mem_simple_closure {i : ι} (hi : f (P.root i) < 0) :
    -P.root i ∈ AddSubmonoid.closure
      (P.root '' IsAddIndecomposable.baseOf P.root (f : M →+ ℝ)) := by
  have h : P.root (P.reflectionPerm i i) = -P.root i := by simp
  rw [← h]
  exact root_mem_simple_closure P f (by rw [h, map_neg]; linarith)

private lemma exists_simple_coord (hf : ∀ i, f (P.root i) ≠ 0) {c : ι}
    (hc : c ∈ IsAddIndecomposable.baseOf P.root (f : M →+ ℝ)) :
    ∃ φ : Module.Dual ℝ M, φ (P.root c) = 1 ∧
      ∀ d ∈ IsAddIndecomposable.baseOf P.root (f : M →+ ℝ), d ≠ c →
        φ (P.root d) = 0 := by
  have hli := P.linearIndepOn_root_baseOf' (S := ℝ) f hf
  obtain ⟨g, hg, hg'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (hli.notMem_span hc)
    inferInstance
  refine ⟨(g (P.root c))⁻¹ • g, by simp [hg], fun d hd hdc => ?_⟩
  have hmem : g (P.root d) ∈ (Submodule.span ℝ
      (P.root '' (IsAddIndecomposable.baseOf P.root (f : M →+ ℝ) \ {c}))).map g :=
    Submodule.mem_map_of_mem (Submodule.subset_span ⟨d, ⟨hd, hdc⟩, rfl⟩)
  rw [hg', Submodule.mem_bot] at hmem
  simp [hmem]

private lemma proportional_of_simple_reflection_negative (hf : ∀ i, f (P.root i) ≠ 0)
    {b i : ι} (hb : b ∈ IsAddIndecomposable.baseOf P.root (f : M →+ ℝ))
    (hi : 0 < f (P.root i)) (hj : f (P.reflection b (P.root i)) < 0) :
    ∃ t : ℝ, P.root i = t • P.root b := by
  classical
  let Δ := IsAddIndecomposable.baseOf P.root (f : M →+ ℝ)
  have hφ : ∀ c, ∃ φ : Module.Dual ℝ M, c ∈ Δ →
      (φ (P.root c) = 1 ∧ ∀ d ∈ Δ, d ≠ c → φ (P.root d) = 0) := by
    intro c
    by_cases hc : c ∈ Δ
    · obtain ⟨φ, h1, h2⟩ := exists_simple_coord P f hf hc
      exact ⟨φ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose φ hφ using hφ
  let Δs : Finset ι := (Set.toFinite Δ).toFinset
  have hΔs : ∀ c, c ∈ Δs ↔ c ∈ Δ := fun c => Set.Finite.mem_toFinset _
  have key : ∀ x ∈ AddSubmonoid.closure (P.root '' Δ),
      (∀ c ∈ Δ, 0 ≤ φ c x) ∧ x = ∑ c ∈ Δs, φ c x • P.root c := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      refine ⟨fun c hc => ?_, ?_⟩
      · by_cases hdc : d = c
        · subst hdc
          rw [(hφ d hd).1]
          exact zero_le_one
        · rw [(hφ c hc).2 d hd hdc]
      · rw [Finset.sum_eq_single d]
        · rw [(hφ d hd).1, one_smul]
        · intro c hc hcd
          rw [(hφ c ((hΔs c).mp hc)).2 d hd (Ne.symm hcd), zero_smul]
        · intro hd'
          exact absurd ((hΔs d).mpr hd) hd'
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨fun c hc => ?_, ?_⟩
      · rw [map_add]
        exact add_nonneg (hx.1 c hc) (hy.1 c hc)
      · simp only [map_add, add_smul, Finset.sum_add_distrib]
        rw [← hx.2, ← hy.2]
  have hx := key _ (root_mem_simple_closure P f hi)
  have hy := key _ (neg_root_mem_simple_closure P f (i := P.reflectionPerm b i)
    (by rwa [RootPairing.root_reflectionPerm]))
  have hzero : ∀ c ∈ Δ, c ≠ b → φ c (P.root i) = 0 := by
    intro c hc hcb
    have h1 := hx.1 c hc
    have h2 := hy.1 c hc
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, map_neg, map_sub,
      map_smul, (hφ c hc).2 b hb (Ne.symm hcb), smul_zero, sub_zero] at h2
    linarith
  refine ⟨φ b (P.root i), ?_⟩
  calc P.root i = ∑ c ∈ Δs, φ c (P.root i) • P.root c := hx.2
    _ = φ b (P.root i) • P.root b := by
      refine Finset.sum_eq_single b (fun c hc hcb => ?_) (fun hb' => ?_)
      · rw [hzero c ((hΔs c).mp hc) hcb, zero_smul]
      · exact absurd ((hΔs b).mpr hb) hb'

private lemma exists_simple_pairing_pos {i : ι} (hi : 0 < f (P.root i)) :
    ∃ b ∈ IsAddIndecomposable.baseOf P.root (f : M →+ ℝ), 0 < P.pairing i b := by
  by_contra! h
  have key : ∀ x ∈ AddSubmonoid.closure
      (P.root '' IsAddIndecomposable.baseOf P.root (f : M →+ ℝ)), P.coroot' i x ≤ 0 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [RootPairing.root_coroot'_eq_pairing]
      have hsym : 0 < P.pairing b i ↔ 0 < P.pairing i b := by
        rw [← P.algebraMap_pairingIn ℤ, ← P.algebraMap_pairingIn ℤ]
        simpa using P.zero_lt_pairingIn_iff' ℤ (i := b) (j := i)
      exact not_lt.mp fun hpos => absurd (hsym.mp hpos) (not_lt.mpr (h b hb))
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using add_nonpos hx hy
  have := key _ (root_mem_simple_closure P f hi)
  rw [RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same] at this
  norm_num at this

/-- A set of root directions containing the simple directions and stable under
simple reflections contains all root directions, without a reducedness hypothesis. -/
private lemma all_directions_of_simple_directions
    (hf : ∀ i, f (P.root i) ≠ 0) (S : Set ι)
    (hprop : ∀ i b, b ∈ IsAddIndecomposable.baseOf P.root (f : M →+ ℝ) →
      (∃ t : ℝ, P.root i = t • P.root b) → i ∈ S)
    (hneg : ∀ i, P.reflectionPerm i i ∈ S → i ∈ S)
    (hreflect : ∀ b ∈ IsAddIndecomposable.baseOf P.root (f : M →+ ℝ),
      ∀ i, P.reflectionPerm b i ∈ S → i ∈ S) :
    ∀ i, i ∈ S := by
  have hpos : ∀ i, 0 < f (P.root i) → i ∈ S := by
    intro i hi
    by_contra hiS
    let T : Set ι := {i | 0 < f (P.root i) ∧ i ∉ S}
    obtain ⟨k, hk⟩ := T.toFinite.exists_minimalFor (fun j => f (P.root j)) T ⟨i, hi, hiS⟩
    obtain ⟨hk0, hk1⟩ := hk.prop
    obtain ⟨b, hb, hpair⟩ := exists_simple_pairing_pos P f hk0
    have hlt : f (P.root (P.reflectionPerm b k)) < f (P.root k) := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
        map_sub, map_smul, smul_eq_mul]
      have := hb.1
      change 0 < f (P.root b) at this
      nlinarith
    rcases lt_or_gt_of_ne (hf (P.reflectionPerm b k)) with hneg' | hpos'
    · apply hk1
      apply hprop k b hb
      exact proportional_of_simple_reflection_negative P f hf hb hk0
        (by rwa [RootPairing.root_reflectionPerm] at hneg')
    · have hmissing : P.reflectionPerm b k ∉ S := fun h => hk1 (hreflect b hb k h)
      exact absurd hlt (not_lt.mpr
        (hk.le_of_le (show P.reflectionPerm b k ∈ T from ⟨hpos', hmissing⟩) hlt.le))
  intro i
  rcases lt_or_gt_of_ne (hf i) with hi | hi
  · apply hneg i
    apply hpos
    simpa using neg_pos.mpr hi
  · exact hpos i hi

end SimpleRootDescent

namespace IsAffineRootSystemWithRankZero

/-- Every affine root system, including the empty system in rank zero, has a special point. -/
theorem exists_isSpecialPoint (hΨ : IsAffineRootSystemWithRankZero Ψ) :
    ∃ x : A, IsSpecialPoint Ψ x := by
  classical
  let := hΨ.finite_derivativeRoots.fintype
  let := hΨ.finiteDimensional_translation
  let P := hΨ.derivativePairing
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    P.root (fun i => P.ne_zero i)
  let Δ := IsAddIndecomposable.baseOf P.root (f : Module.Dual ℝ V →+ ℝ)
  have hli : LinearIndependent ℝ (fun b : Δ => P.root b.val) :=
    P.linearIndepOn_root_baseOf' (S := ℝ) f hf
  have hspan : Submodule.span ℝ (P.root '' Δ) = ⊤ := by
    apply top_unique
    rw [← hΨ.span_derivativeRoots_eq_top]
    apply Submodule.span_le.mpr
    intro a ha
    let i : derivativeRoots Ψ := ⟨a, ha⟩
    change P.root i ∈ _
    rcases lt_or_gt_of_ne (hf i) with hi | hi
    · exact (Submodule.span ℝ (P.root '' Δ)).neg_mem_iff.mp
        (Submodule.closure_subset_span (neg_root_mem_simple_closure P f hi))
    · exact Submodule.closure_subset_span (root_mem_simple_closure P f hi)
  let b : Basis Δ ℝ (Module.Dual ℝ V) := Basis.mk hli (by
    simpa only [← Set.image_eq_range] using hspan.ge)
  obtain ⟨p⟩ : Nonempty A := inferInstance
  let φ : Module.Dual ℝ (Module.Dual ℝ V) :=
    b.constr ℝ (fun i => -(hΨ.derivativeRootLift i.val) p)
  obtain ⟨v, hv⟩ := (Module.evalEquiv ℝ V).surjective φ
  let x : A := v +ᵥ p
  have hzero (i : Δ) : hΨ.derivativeRootLift i.val x = 0 := by
    have heval : (P.root i.val) v = -(hΨ.derivativeRootLift i.val) p := by
      calc
        (P.root i.val) v = φ (P.root i.val) := LinearMap.congr_fun hv _
        _ = -(hΨ.derivativeRootLift i.val) p := by
          have hbi : b i = P.root i.val := Basis.mk_apply _ _ _
          rw [← hbi]
          simp [φ]
    rw [show x = v +ᵥ p from rfl, AffineMap.map_vadd, hΨ.linear_derivativeRootLift,
      vadd_eq_add]
    change P.root i.val v + hΨ.derivativeRootLift i.val p = 0
    rw [heval, neg_add_cancel]
  let S : Set (derivativeRoots Ψ) := {i |
    ∃ η ∈ vanishingRoots Ψ x, LinearMap.ker (P.root i) = LinearMap.ker η.linear}
  have hall : ∀ i, i ∈ S := by
    apply all_directions_of_simple_directions P f hf S
    · intro i j hj ⟨t, ht⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact P.ne_zero i (by simpa using ht)
      refine ⟨hΨ.derivativeRootLift j, ⟨hΨ.derivativeRootLift_mem j, hzero ⟨j, hj⟩⟩, ?_⟩
      rw [hΨ.linear_derivativeRootLift]
      change LinearMap.ker (P.root i) = LinearMap.ker (P.root j)
      rw [ht, LinearMap.ker_smul _ t ht0]
    · intro i ⟨η, hη, hker⟩
      refine ⟨η, hη, ?_⟩
      simpa using hker
    · intro j hj i ⟨η, hη, hker⟩
      let ψ := hΨ.derivativeRootLift j
      let u := hΨ.derivativeCoroot j
      have hu : IsCoroot Ψ ψ u := hΨ.isCoroot_derivativeCoroot j
      let e := affineReflection ψ hu.1
      have hex : e x = x := affineReflection_apply_of_mem ψ hu.1 (hzero ⟨j, hj⟩)
      have hηe : η.comp e.toAffineMap ∈ Ψ := by
        rw [comp_affineReflection]
        exact hu.2 η hη.1
      refine ⟨η.comp e.toAffineMap, ⟨hηe, ?_⟩, ?_⟩
      · simpa only [AffineMap.comp_apply, AffineEquiv.coe_toAffineMap, hex] using hη.2
      · have hlin : (P.root (P.reflectionPerm j i)).comp e.linear.toLinearMap = P.root i := by
          ext w
          rw [LinearMap.comp_apply, RootPairing.root_reflectionPerm,
            RootPairing.reflection_apply_root]
          change (i.val - i.val u • j.val) (Module.reflection hu.1 w) = i.val w
          rw [Module.reflection_apply]
          simp only [ψ, hΨ.linear_derivativeRootLift, LinearMap.sub_apply,
            LinearMap.smul_apply, map_sub, map_smul, u, hΨ.derivative_apply_coroot,
            smul_eq_mul]
          ring
        rw [AffineMap.comp_linear]
        change LinearMap.ker (P.root i) =
          LinearMap.ker (η.linear.comp e.linear.toLinearMap)
        rw [← hlin, LinearMap.ker_comp, LinearMap.ker_comp, hker]
  refine ⟨x, (isSpecialPoint_iff_ker hΨ.linear_ne_zero x).mpr ?_⟩
  intro ψ hψ
  exact hall ⟨ψ.linear, linear_mem_derivativeRoots hψ⟩

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
