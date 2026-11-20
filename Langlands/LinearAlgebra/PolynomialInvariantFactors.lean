import Langlands.LinearAlgebra.CyclicQuotientPairingProof
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Ordered cyclic factors of a polynomial module

A finite-dimensional torsion polynomial module splits off a copy of the
quotient by its annihilator. Iteration gives monic cyclic factors in decreasing
order for divisibility.
-/

namespace Langlands.PolynomialInvariantFactors

open Polynomial

universe u v w

variable {K : Type u} [Field K]

/-- The quotient ring, with its `K[X]`-module structure. -/
abbrev Quot (q : K[X]) := K[X] ⧸ Ideal.span ({q} : Set K[X])

/-- The polynomial module described by a list of monic cyclic factors. -/
abbrev Model (qs : List K[X]) := ∀ i : Fin qs.length, Quot (qs.get i)

/-- Factors are monic, have positive degree and are ordered by reverse divisibility. -/
def Ordered (qs : List K[X]) : Prop :=
  qs.Pairwise (fun p q => q ∣ p) ∧ ∀ q ∈ qs, q.Monic ∧ 0 < q.natDegree

private theorem Ordered.tail {q : K[X]} {qs : List K[X]} (h : Ordered (q :: qs)) : Ordered qs :=
  ⟨(List.pairwise_cons.mp h.1).2, fun p hp => h.2 p (List.mem_cons_of_mem q hp)⟩

private instance modelNilSubsingleton : Subsingleton (Model ([] : List K[X])) :=
  ⟨fun _ _ => funext fun i => Fin.elim0 i⟩

private def consEquiv (q : K[X]) (qs : List K[X]) :
    Model (q :: qs) ≃ₗ[K[X]] Quot q × Model qs where
  toFun f := (f 0, fun i => f i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv f := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Split

variable {M : Type v} [AddCommGroup M] [Module K M] [Module K[X] M]
  [IsScalarTower K K[X] M]

/-- The map from the cyclic quotient taking the class of `1` to a specified vector. -/
private noncomputable def cyclicMap (q : K[X]) (hq : q ∈ Module.annihilator K[X] M) (x : M) :
    Quot q →ₗ[K[X]] M :=
  (Ideal.span {q}).liftQ (LinearMap.toSpanSingleton K[X] M x) fun _ hp =>
    Module.mem_annihilator.mp ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq)) hp) x

omit [Module K M] [IsScalarTower K K[X] M] in
private theorem cyclicMap_mk (q : K[X]) (hq : q ∈ Module.annihilator K[X] M) (x : M)
    (p : K[X]) : cyclicMap q hq x (AdjoinRoot.mk q p) = p • x := rfl

private theorem splitCyclic (q : K[X]) (hq : q.Monic)
    (hann : Ideal.span {q} = Module.annihilator K[X] M) [Module.Finite K[X] M] :
    ∃ r : M →ₗ[K[X]] Quot q, ∃ j : Quot q →ₗ[K[X]] M,
      r.comp j = LinearMap.id := by
  classical
  have hqmem : q ∈ Module.annihilator K[X] M := hann ▸ Ideal.subset_span (Set.mem_singleton q)
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator (R := K[X]) (M := M)
  let j := cyclicMap q hqmem x
  have hj : Function.Injective j := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' _ _ (hann.trans hx.symm))
  let jk := j.restrictScalars K
  obtain ⟨s, hs⟩ := jk.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  have hsapply (a : Quot q) : s (j a) = a := DFunLike.congr_fun hs a
  let hfin : FiniteDimensional K (AdjoinRoot q) :=
    (AdjoinRoot.powerBasisAux' hq).finiteDimensional_of_finite
  obtain ⟨B, hsym, hnd, hbal⟩ := cyclicQuotientPairing K q hq.ne_zero
  let D := B.toDual hnd
  let L : M →ₗ[K] K := (B 1).comp s
  let r (y : M) : AdjoinRoot q := D.symm (L.comp ((cyclicMap q hqmem y).restrictScalars K))
  have hr (y : M) (a : AdjoinRoot q) : B (r y) a = L (cyclicMap q hqmem y a) := by
    change D (D.symm (L.comp ((cyclicMap q hqmem y).restrictScalars K))) a = _
    rw [D.apply_symm_apply]
    rfl
  have hsep {a b : AdjoinRoot q} (h : ∀ t, B a t = B b t) : a = b :=
    D.injective (LinearMap.ext h)
  refine ⟨{ toFun := r, map_add' := ?_, map_smul' := ?_ }, j, ?_⟩
  · intro y z
    apply hsep
    intro a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    change B (r (y + z)) (AdjoinRoot.mk q p) = B (r y + r z) (AdjoinRoot.mk q p)
    simp only [map_add, LinearMap.add_apply, hr, cyclicMap_mk, smul_add]
  · intro p y
    apply hsep
    intro a
    obtain ⟨t, rfl⟩ := AdjoinRoot.mk_surjective a
    change B (r (p • y)) (AdjoinRoot.mk q t) =
      B (AdjoinRoot.mk q p * r y) (AdjoinRoot.mk q t)
    rw [hbal, ← map_mul, hr, hr, cyclicMap_mk, cyclicMap_mk, mul_smul, smul_comm t p]
  · apply LinearMap.ext
    intro a
    change r (j a) = a
    change AdjoinRoot q at a
    apply hsep
    intro b
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective b
    have hjp : p • j a = j (AdjoinRoot.mk q p * a) := (j.map_smul p a).symm
    calc
      B (r (j a)) (AdjoinRoot.mk q p) = L (p • j a) := (hr _ _).trans
        (congrArg L (cyclicMap_mk q hqmem _ p))
      _ = L (j (AdjoinRoot.mk q p * a)) := congrArg L hjp
      _ = B 1 (AdjoinRoot.mk q p * a) := congrArg (B 1) (hsapply _)
      _ = B a (AdjoinRoot.mk q p) := by
        rw [← hbal, mul_one]
        exact hsym.eq _ _

end Split

private theorem smul_quot_one_eq_zero {q p : K[X]} :
    p • (1 : Quot q) = 0 ↔ q ∣ p := by
  change AdjoinRoot.mk q p * (1 : AdjoinRoot q) = 0 ↔ q ∣ p
  rw [mul_one, AdjoinRoot.mk_eq_zero]

private theorem dvd_iff_annihilates_quot {q p : K[X]} :
    q ∣ p ↔ ∀ x : Quot q, p • x = 0 := by
  refine ⟨fun hp x => ?_, fun h => smul_quot_one_eq_zero.mp (h 1)⟩
  let y : AdjoinRoot q := x
  change AdjoinRoot.mk q p * y = 0
  rw [AdjoinRoot.mk_eq_zero.mpr hp, zero_mul]

private theorem annihilates_model_iff (qs : List K[X]) (p : K[X]) :
    (∀ x : Model qs, p • x = 0) ↔ ∀ q ∈ qs, q ∣ p := by
  classical
  simp only [List.mem_iff_get, forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨fun h i => smul_quot_one_eq_zero.mp ?_, fun h x => ?_⟩
  · simpa only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply] using
      congrFun (h (Pi.single i 1)) i
  · funext i
    exact dvd_iff_annihilates_quot.mp (h i) (x i)

private theorem existsModelAux (d : ℕ) {c : K[X]} (hc0 : c ≠ 0) :
    ∀ (M : Type v) [AddCommGroup M] [Module K M] [Module K[X] M] [IsScalarTower K K[X] M]
      [FiniteDimensional K M], Module.finrank K M = d → (∀ x : M, c • x = 0) →
      ∃ qs : List K[X], Ordered qs ∧ Nonempty (M ≃ₗ[K[X]] Model qs) := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro M _ _ _ _ _ hd hc
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact ⟨[], by simp [Ordered], ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    let I := Module.annihilator K[X] M
    have hI₀ : I ≠ ⊥ := by
      intro hI
      have hcI : c ∈ I := Module.mem_annihilator.mpr hc
      rw [hI] at hcI
      exact hc0 hcI
    have hI₁ : I ≠ ⊤ := fun hI => (not_subsingleton M) (Module.annihilator_eq_top_iff.mp hI)
    let q := normalize (Submodule.IsPrincipal.generator I)
    have hq : q.Monic := monic_normalize
      (mt (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hI₀)
    have hann : Ideal.span ({q} : Set K[X]) = I :=
      (Ideal.span_singleton_eq_span_singleton.mpr (normalize_associated _)).trans
        (Ideal.span_singleton_generator I)
    have hqpos : 0 < q.natDegree := Nat.pos_of_ne_zero fun h =>
      hI₁ (hann.symm.trans (Ideal.span_singleton_eq_top.mpr (by
        rw [eq_one_of_monic_natDegree_zero hq h]
        exact isUnit_one)))
    have hqmem : q ∈ I := hann ▸ Ideal.subset_span (Set.mem_singleton q)
    have hqann (x : M) : q • x = 0 := Module.mem_annihilator.mp hqmem x
    have : Module.Finite K[X] M := Module.Finite.of_restrictScalars_finite K K[X] M
    obtain ⟨r, j, hrj⟩ := splitCyclic q hq hann
    let N := LinearMap.ker r
    let e : M ≃ₗ[K[X]] Quot q × N :=
      (lequivProdOfRightSplitExact (j := N.subtype) Subtype.val_injective
        (Submodule.range_subtype N) hrj).symm.trans (LinearEquiv.prodComm K[X] N (Quot q))
    let _ : FiniteDimensional K N :=
      inferInstanceAs (FiniteDimensional K (N.restrictScalars K))
    let _ : FiniteDimensional K (Quot q) := (AdjoinRoot.powerBasisAux' hq).finiteDimensional_of_finite
    have hdim : d = q.natDegree + Module.finrank K N := by
      rw [← hd, (e.restrictScalars K).finrank_eq, Module.finrank_prod,
        finrank_quotient_span_eq_natDegree]
    obtain ⟨qs, hqs, ⟨e'⟩⟩ := ih _ (by omega) N rfl
      (fun x => Subtype.ext (hc x))
    have hqann' : ∀ x : Model qs, q • x = 0 := by
      intro x
      have hx : q • e'.symm x = 0 := Subtype.ext (hqann (e'.symm x))
      simpa only [map_smul, LinearEquiv.apply_symm_apply, map_zero] using congrArg e' hx
    refine ⟨q :: qs, ⟨List.pairwise_cons.mpr ⟨(annihilates_model_iff qs q).mp hqann', hqs.1⟩,
      ?_⟩, ⟨e.trans ((LinearEquiv.refl K[X] (Quot q)).prodCongr e') |>.trans
        (consEquiv q qs).symm⟩⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hq, hqpos⟩
    · exact hqs.2 p hp

/-- A finite-dimensional polynomial module killed by a nonzero polynomial admits
an ordered cyclic decomposition. -/
theorem existsModel {M : Type v} [AddCommGroup M] [Module K M] [Module K[X] M]
    [IsScalarTower K K[X] M] [FiniteDimensional K M] {c : K[X]} (hc0 : c ≠ 0)
    (hc : ∀ x : M, c • x = 0) :
    ∃ qs : List K[X], Ordered qs ∧ Nonempty (M ≃ₗ[K[X]] Model qs) :=
  existsModelAux (Module.finrank K M) hc0 M rfl hc

private theorem modelFinite (qs : List K[X]) (hqs : Ordered qs) :
    FiniteDimensional K (Model qs) := by
  let _ (i : Fin qs.length) : FiniteDimensional K (Quot (qs.get i)) :=
    (AdjoinRoot.powerBasisAux' (hqs.2 _ (List.get_mem qs i)).1).finiteDimensional_of_finite
  infer_instance

section KernelDimension

variable (K) (M : Type v) [AddCommGroup M] [Module K M] [Module K[X] M] [IsScalarTower K K[X] M]

private noncomputable def kernelDim (p : K[X]) : ℕ :=
  Module.finrank K (LinearMap.ker (Algebra.lsmul K K M p))

private theorem kernelDim_zero : kernelDim K M 0 = Module.finrank K M := by
  rw [kernelDim, map_zero, LinearMap.ker_zero, finrank_top]

private theorem annihilates_iff_kernelDim_eq [FiniteDimensional K M] (p : K[X]) :
    (∀ x : M, p • x = 0) ↔ kernelDim K M p = kernelDim K M 0 := by
  rw [kernelDim_zero, kernelDim, ← Submodule.eq_top_iff_finrank_eq, eq_top_iff]
  simp only [SetLike.le_def, Submodule.mem_top, true_implies, LinearMap.mem_ker, Algebra.lsmul_apply]

variable {K M} {N : Type w} [AddCommGroup N] [Module K N] [Module K[X] N] [IsScalarTower K K[X] N]

private theorem kernelDim_eq (e : M ≃ₗ[K[X]] N) (p : K[X]) :
    kernelDim K M p = kernelDim K N p := by
  unfold kernelDim
  apply LinearEquiv.finrank_eq ((e.restrictScalars K).ofSubmodules _ _ ?_)
  apply Submodule.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change p • x = 0 at hx
    change p • e x = 0
    rw [← e.map_smul, hx, map_zero]
  · intro hy
    change p • y = 0 at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change p • e.symm y = 0
    rw [← e.symm.map_smul, hy, map_zero]

private theorem kernelDim_prod [FiniteDimensional K M] [FiniteDimensional K N] (p : K[X]) :
    kernelDim K (M × N) p = kernelDim K M p + kernelDim K N p := by
  unfold kernelDim
  let f := Algebra.lsmul K K M p
  let g := Algebra.lsmul K K N p
  change Module.finrank K (LinearMap.ker (f.prodMap g)) =
    Module.finrank K f.ker + Module.finrank K g.ker
  rw [LinearMap.ker_prodMap, (Submodule.prodEquiv f.ker g.ker).finrank_eq, Module.finrank_prod]

end KernelDimension

private theorem kernelDim_cons {q : K[X]} {qs : List K[X]} (h : Ordered (q :: qs)) (p : K[X]) :
    kernelDim K (Model (q :: qs)) p = kernelDim K (Quot q) p + kernelDim K (Model qs) p := by
  let _ : FiniteDimensional K (Quot q) :=
    (AdjoinRoot.powerBasisAux' (h.2 q (List.mem_cons_self ..)).1).finiteDimensional_of_finite
  let _ : FiniteDimensional K (Model qs) := modelFinite qs h.tail
  rw [kernelDim_eq (consEquiv q qs), kernelDim_prod]

private theorem kernelDim_nil (p : K[X]) : kernelDim K (Model ([] : List K[X])) p = 0 := by
  unfold kernelDim
  exact Module.finrank_zero_of_subsingleton

private theorem kernelDim_cons_pos {q : K[X]} {qs : List K[X]} (h : Ordered (q :: qs)) :
    0 < kernelDim K (Model (q :: qs)) 0 := by
  rw [kernelDim_cons h, kernelDim_zero K (Quot q), finrank_quotient_span_eq_natDegree]
  have := (h.2 q (List.mem_cons_self ..)).2
  omega

private theorem annihilates_cons_iff {q : K[X]} {qs : List K[X]} (h : Ordered (q :: qs))
    (p : K[X]) : (∀ x : Model (q :: qs), p • x = 0) ↔ q ∣ p := by
  rw [annihilates_model_iff]
  refine ⟨fun hp => hp q (List.mem_cons_self ..), fun hp r hr => ?_⟩
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hp
  · exact ((List.pairwise_cons.mp h.1).1 r hr).trans hp

private theorem eq_of_kernelDim (qs rs : List K[X]) (hqs : Ordered qs) (hrs : Ordered rs)
    (h : ∀ p, kernelDim K (Model qs) p = kernelDim K (Model rs) p) : qs = rs := by
  induction qs generalizing rs with
  | nil =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      have he := h 0
      rw [kernelDim_nil] at he
      exact ((kernelDim_cons_pos hrs).ne' he.symm).elim
  | cons q qs ih =>
    cases rs with
    | nil =>
      have he := h 0
      rw [kernelDim_nil] at he
      exact ((kernelDim_cons_pos hqs).ne' he).elim
    | cons r rs =>
      let _ : FiniteDimensional K (Model (q :: qs)) := modelFinite _ hqs
      let _ : FiniteDimensional K (Model (r :: rs)) := modelFinite _ hrs
      have hdiv (p : K[X]) : q ∣ p ↔ r ∣ p := by
        rw [← annihilates_cons_iff hqs, ← annihilates_cons_iff hrs,
          annihilates_iff_kernelDim_eq K (Model (q :: qs)) p,
          annihilates_iff_kernelDim_eq K (Model (r :: rs)) p, h p, h 0]
      have hqr : q ∣ r := (hdiv r).mpr dvd_rfl
      have hrq : r ∣ q := (hdiv q).mp dvd_rfl
      have hq := (hqs.2 q (List.mem_cons_self ..)).1
      have hr := (hrs.2 r (List.mem_cons_self ..)).1
      have he : q = r :=
        eq_of_monic_of_dvd_of_natDegree_le hr hq hrq (natDegree_le_of_dvd hqr hr.ne_zero)
      subst r
      congr 1
      apply ih rs hqs.tail hrs.tail
      intro p
      exact Nat.add_left_cancel ((kernelDim_cons hqs p).symm.trans
        ((h p).trans (kernelDim_cons hrs p)))

/-- Isomorphic ordered cyclic models have the same list of monic factors. -/
theorem eq_of_equiv {qs rs : List K[X]} (hqs : Ordered qs) (hrs : Ordered rs)
    (e : Model qs ≃ₗ[K[X]] Model rs) : qs = rs :=
  eq_of_kernelDim qs rs hqs hrs (kernelDim_eq e)

end Langlands.PolynomialInvariantFactors
