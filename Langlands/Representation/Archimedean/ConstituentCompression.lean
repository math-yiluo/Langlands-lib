import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Detecting a simple constituent on a finite-dimensional range

Two algebra actions have the same simple constituents detected by a common
finite-rank operator if their compressed operators have equal determinants.
This is an algebraic step for comparing different orders of induction.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.ConstituentCompression

variable {A : Type*} [Ring A] [Algebra ℂ A]
variable {M N J : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup J]
variable [Module ℂ M] [Module ℂ N] [Module ℂ J]

/-- A complex subspace invariant under an algebra action. -/
def IsStable (ρ : A →ₐ[ℂ] Module.End ℂ M) (W : Submodule ℂ M) : Prop :=
  ∀ a : A, ∀ x ∈ W, ρ a x ∈ W

/-- An equivariant surjection onto `J` from an invariant subspace. -/
def IsConstituent (ρ : A →ₐ[ℂ] Module.End ℂ M) (σ : A →ₐ[ℂ] Module.End ℂ J) : Prop :=
  ∃ (W : Submodule ℂ M) (hW : IsStable ρ W) (f : W →ₗ[ℂ] J),
    Function.Surjective f ∧ ∀ a : A, ∀ w : W, f ⟨ρ a w, hW a w w.2⟩ = σ a (f w)

/-- An algebra action is simple if every nonzero vector generates the module. -/
def IsSimple (σ : A →ₐ[ℂ] Module.End ℂ J) : Prop :=
  ∀ j : J, j ≠ 0 → ∀ y : J, ∃ a : A, σ a j = y

private def restrictRange (p T : Module.End ℂ M) : Module.End ℂ (LinearMap.range p) :=
  (p.rangeRestrict ∘ₗ T) ∘ₗ (LinearMap.range p).subtype

/-- The determinant of the identity minus the operator obtained by applying `ρ a`
and then `ρ p` on the range of `ρ p`. -/
def compressedDet (ρ : A →ₐ[ℂ] Module.End ℂ M) (p a : A) : ℂ :=
  LinearMap.det (1 - restrictRange (ρ p) (ρ a))

private def rangeAction (ρ : A →ₐ[ℂ] Module.End ℂ M) (p : A) (a : A) :
    Module.End ℂ (LinearMap.range (ρ p)) := restrictRange (ρ p) (ρ a)

private theorem compressedDet_eq_one_of_annihilates
    (ρ : A →ₐ[ℂ] Module.End ℂ M) (p a : A)
    (h : ∀ v ∈ LinearMap.range (ρ p), ρ a v = 0) : compressedDet ρ p a = 1 := by
  have hz : restrictRange (ρ p) (ρ a) = 0 := by
    ext v
    change ρ p (ρ a v) = 0
    rw [h v v.2, map_zero]
  simp [compressedDet, hz]

private theorem not_fixed_of_det_ne_zero
    (ρ : A →ₐ[ℂ] Module.End ℂ M) (σ : A →ₐ[ℂ] Module.End ℂ J) (p a : A)
    [FiniteDimensional ℂ (LinearMap.range (ρ p))] (h : compressedDet ρ p a ≠ 0)
    (hJ : IsConstituent ρ σ) {j : J} (hj : j ∈ LinearMap.range (σ p))
    (hfix : σ p (σ a j) = j) : j = 0 := by
  obtain ⟨W, hW, f, hsurj, hf⟩ := hJ
  let U := W.comap (LinearMap.range (ρ p)).subtype
  let T : Module.End ℂ (LinearMap.range (ρ p)) := 1 - rangeAction ρ p a
  have hT (v : LinearMap.range (ρ p)) : (T v : M) = v - ρ p (ρ a v) := rfl
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.1
    by_contra hn
    exact h (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hn)
  have hTU : ∀ v ∈ U, T v ∈ U := by
    intro v hv
    change (v : M) ∈ W at hv
    change (T v : M) ∈ W
    rw [hT]
    exact W.sub_mem hv (hW p _ (hW a _ hv))
  let T' : Module.End ℂ U := T.restrict hTU
  have hT' : Function.Surjective T' :=
    LinearMap.injective_iff_surjective.mp (fun _ _ he =>
      Subtype.ext (hinj (congrArg Subtype.val he)))
  let g : U →ₗ[ℂ] J := f.comp ((LinearMap.range (ρ p)).subtype.restrict
    (p := U) (q := W) (fun _ hv => hv))
  have heq (v : U) : g (T' v) = g v - σ p (σ a (g v)) := by
    change f ⟨(T v : M), hTU v v.2⟩ = _
    have hv : (v.val : M) ∈ W := v.2
    have hh : (⟨(T v : M), hTU v v.2⟩ : W) =
        ⟨v.val, hv⟩ - ⟨ρ p (ρ a v.val), hW p _ (hW a _ hv)⟩ := Subtype.ext (hT v)
    rw [hh, map_sub, hf p ⟨ρ a v.val, hW a _ hv⟩, hf a ⟨v.val, hv⟩]
    rfl
  let Tj : Module.End ℂ (LinearMap.range g) := (1 - (σ p * σ a)).restrict (by
    rintro y ⟨v, rfl⟩
    exact ⟨T' v, heq v⟩)
  have hs : Function.Surjective Tj := by
    rintro ⟨_, v, rfl⟩
    obtain ⟨w, hw⟩ := hT' v
    exact ⟨⟨g w, w, rfl⟩, Subtype.ext ((heq w).symm.trans (congrArg g hw))⟩
  have : FiniteDimensional ℂ (LinearMap.range g) := LinearMap.finiteDimensional_range g
  have hi : Function.Injective Tj := LinearMap.injective_iff_surjective.mpr hs
  obtain ⟨j0, rfl⟩ := hj
  obtain ⟨v, hv⟩ := hsurj j0
  have hjg : σ p j0 ∈ LinearMap.range g := by
    let v' : LinearMap.range (ρ p) := ⟨ρ p v, v, rfl⟩
    exact ⟨⟨v', hW p v v.2⟩, (hf p v).trans (congrArg (σ p) hv)⟩
  have e : Tj ⟨σ p j0, hjg⟩ = Tj 0 := by
    apply Subtype.ext
    change σ p j0 - σ p (σ a (σ p j0)) = (Tj 0 : J)
    rw [hfix, sub_self, map_zero]
    rfl
  exact congrArg Subtype.val (hi e)

private theorem constituent_of_fin_power (ρ : A →ₐ[ℂ] Module.End ℂ N)
    (σ : A →ₐ[ℂ] Module.End ℂ J) (hσ : IsSimple σ) [Nontrivial J] :
    ∀ {d : ℕ} (W : Submodule ℂ (Fin d → N))
      (hW : ∀ a : A, ∀ w ∈ W, (fun i => ρ a (w i)) ∈ W)
      (f : W →ₗ[ℂ] J), Function.Surjective f →
      (∀ (a : A) (w : W), f ⟨_, hW a w w.2⟩ = σ a (f w)) → IsConstituent ρ σ := by
  intro d
  induction d with
  | zero =>
    intro W hW f hsurj hf
    obtain ⟨j, hj⟩ := exists_ne (0 : J)
    obtain ⟨w, hw⟩ := hsurj j
    exact (hj (hw.symm.trans (by rw [Subsingleton.elim w 0, map_zero]))).elim
  | succ d ih =>
    intro W hW f hsurj hf
    let tail : (Fin (d + 1) → N) →ₗ[ℂ] (Fin d → N) := LinearMap.funLeft ℂ N Fin.succ
    let head : (Fin (d + 1) → N) →ₗ[ℂ] N := LinearMap.proj 0
    let s := (tail.comp W.subtype)
    by_cases hk : LinearMap.ker s ≤ LinearMap.ker f
    · let g : (LinearMap.range s) →ₗ[ℂ] J :=
        (LinearMap.ker s).liftQ f hk ∘ₗ s.quotKerEquivRange.symm.toLinearMap
      have hgs (w : W) : g (s.rangeRestrict w) = f w := by
        change (LinearMap.ker s).liftQ f hk (s.quotKerEquivRange.symm
          ⟨s w, LinearMap.mem_range_self s w⟩) = f w
        rw [LinearMap.quotKerEquivRange_symm_apply_image]
        rfl
      have hS (a : A) (v : Fin d → N) (hv : v ∈ LinearMap.range s) :
          (fun i => ρ a (v i)) ∈ LinearMap.range s := by
        obtain ⟨w, rfl⟩ := hv
        exact ⟨⟨_, hW a w w.2⟩, rfl⟩
      apply ih _ hS g
      · intro j
        obtain ⟨w, rfl⟩ := hsurj j
        exact ⟨s.rangeRestrict w, hgs w⟩
      · rintro a ⟨v, w, rfl⟩
        exact (hgs ⟨_, hW a w w.2⟩).trans ((hf a w).trans (congrArg (σ a) (hgs w).symm))
    · obtain ⟨w, hw, hwf⟩ := SetLike.not_le_iff_exists.mp hk
      let U := LinearMap.ker s
      let q := head.comp (W.subtype.comp U.subtype)
      have hq : Function.Injective q := by
        intro v w hvw
        apply Subtype.ext
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hvw
        · exact (congrFun (LinearMap.mem_ker.mp v.2) j).trans
            (congrFun (LinearMap.mem_ker.mp w.2) j).symm
      let g := (f.comp U.subtype).comp (LinearEquiv.ofInjective q hq).symm.toLinearMap
      have hgs (w : U) : g (q.rangeRestrict w) = f w := by
        change f ((LinearEquiv.ofInjective q hq).symm (LinearEquiv.ofInjective q hq w)) = _
        rw [LinearEquiv.symm_apply_apply]
      have hU (a : A) (w : U) : (⟨_, hW a (w.val : Fin (d + 1) → N) w.val.2⟩ : W) ∈ U := by
        change tail (fun i => ρ a ((w.val : Fin (d + 1) → N) i)) = 0
        funext i
        change ρ a ((w.val : Fin (d + 1) → N) i.succ) = 0
        have e : (w.val : Fin (d + 1) → N) i.succ = 0 :=
          congrFun (LinearMap.mem_ker.mp w.2) i
        rw [e, map_zero]
      have hQ : IsStable ρ (LinearMap.range q) := by
        rintro a _ ⟨v, rfl⟩
        exact ⟨⟨_, hU a v⟩, rfl⟩
      refine ⟨_, hQ, g, ?_, ?_⟩
      · intro j
        obtain ⟨a, ha⟩ := hσ (f w) (fun h => hwf (LinearMap.mem_ker.mpr h)) j
        let v : U := ⟨w, hw⟩
        exact ⟨q.rangeRestrict ⟨_, hU a v⟩,
          (hgs ⟨_, hU a v⟩).trans ((hf a w).trans ha)⟩
      · rintro a ⟨x, v, rfl⟩
        exact (hgs ⟨_, hU a v⟩).trans ((hf a v.val).trans (congrArg (σ a) (hgs v).symm))

/-- Equality of compressed determinants transfers a simple constituent detected
by the finite-rank operator. -/
theorem isConstituent_of_compressedDet_eq
    (ρ : A →ₐ[ℂ] Module.End ℂ M) (τ : A →ₐ[ℂ] Module.End ℂ N)
    (σ : A →ₐ[ℂ] Module.End ℂ J) (p : A)
    [FiniteDimensional ℂ (LinearMap.range (ρ p))] [FiniteDimensional ℂ (LinearMap.range (τ p))]
    (hdet : ∀ a : A, compressedDet ρ p a = compressedDet τ p a)
    (hJ : IsConstituent ρ σ) (hσ : IsSimple σ) {j0 : J} (hj : σ p j0 ≠ 0) :
    IsConstituent τ σ := by
  let _ : Nontrivial J := ⟨⟨σ p j0, 0, hj⟩⟩
  let b := Module.finBasis ℂ (LinearMap.range (τ p))
  let e : A →ₗ[ℂ] (Fin (Module.finrank ℂ (LinearMap.range (τ p))) → N) :=
    LinearMap.pi fun i => LinearMap.applyₗ (b i : N) ∘ₗ τ.toLinearMap
  let f : A →ₗ[ℂ] J := LinearMap.applyₗ (σ p j0) ∘ₗ σ.toLinearMap
  have he (a : A) (i : Fin (Module.finrank ℂ (LinearMap.range (τ p)))) :
      e a i = τ a (b i) := rfl
  have hf (a : A) : f a = σ a (σ p j0) := rfl
  have hk : LinearMap.ker e ≤ LinearMap.ker f := by
    intro a ha
    rw [LinearMap.mem_ker, hf]
    by_contra h
    obtain ⟨c, hc⟩ := hσ _ h j0
    have hz : ∀ v ∈ LinearMap.range (τ p), τ (c * a) v = 0 := by
      intro v hv
      have hb (i : Fin (Module.finrank ℂ (LinearMap.range (τ p)))) : τ a (b i) = 0 :=
        congrFun (LinearMap.mem_ker.mp ha) i
      have hA : (τ a).comp (LinearMap.range (τ p)).subtype = 0 := by
        apply b.ext
        intro i
        exact hb i
      have hv' : τ a v = 0 := by simpa using LinearMap.congr_fun hA ⟨v, hv⟩
      rw [map_mul, Module.End.mul_apply, hv', map_zero]
    have hd := (hdet (c * a)).trans (compressedDet_eq_one_of_annihilates τ p (c * a) hz)
    apply hj (not_fixed_of_det_ne_zero ρ σ p (c * a) (by rw [hd]; exact one_ne_zero)
      hJ (LinearMap.mem_range_self (σ p) j0) ?_)
    rw [map_mul, Module.End.mul_apply, hc]
  let g : LinearMap.range e →ₗ[ℂ] J :=
    (LinearMap.ker e).liftQ f hk ∘ₗ e.quotKerEquivRange.symm.toLinearMap
  have hgs (a : A) : g (e.rangeRestrict a) = f a := by
    change (LinearMap.ker e).liftQ f hk (e.quotKerEquivRange.symm
      ⟨e a, LinearMap.mem_range_self e a⟩) = f a
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hE (a : A) (v : Fin (Module.finrank ℂ (LinearMap.range (τ p))) → N)
      (hv : v ∈ LinearMap.range e) : (fun i => τ a (v i)) ∈ LinearMap.range e := by
    obtain ⟨c, rfl⟩ := hv
    exact ⟨a * c, funext (fun i => by simp only [he, map_mul, Module.End.mul_apply])⟩
  apply constituent_of_fin_power τ σ hσ _ hE g
  · intro j
    obtain ⟨a, ha⟩ := hσ (σ p j0) hj j
    exact ⟨e.rangeRestrict a, (hgs a).trans ha⟩
  · rintro a ⟨_, c, rfl⟩
    have : (⟨_, hE a (e c) (LinearMap.mem_range_self e c)⟩ : LinearMap.range e) =
        e.rangeRestrict (a * c) := by
      apply Subtype.ext
      funext i
      change τ a (e c i) = e (a * c) i
      simp only [he, map_mul, Module.End.mul_apply]
    change g _ = σ a (g (e.rangeRestrict c))
    rw [this, hgs, hgs, hf, hf, map_mul, Module.End.mul_apply]

end Langlands.Archimedean.ConstituentCompression
