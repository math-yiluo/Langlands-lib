import Langlands.Automorphic.StableTwist.ArithmeticDeepTwist
import Langlands.Correspondence.HenniartUnramified.Occurs
import Langlands.Correspondence.HenniartUnramified.Degree
import Langlands.Correspondence.HenniartUnramified.Swan
import Langlands.Correspondence.HenniartUnramified.Torsion

/-! # Local Weil groups as split degree data, and their unramified stages -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation FiniteRepresentation.SplitDegree Weil.Local
open VirtualRepresentation.LocalWeil.Ramification Ramification.HerbrandBridge Ramification.Padic
open LocalClassField

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The local Weil group with its geometric degree and a chosen element of degree one. -/
abbrev weilSplit (φ : localWeilGroup F) (hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ)) :
    SplitDegree (localWeilGroup F) :=
  ⟨localDegree F, φ, hφ⟩

section Stage

variable (φ : localWeilGroup F) (hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ)) (m : ℕ)

include hφ in
theorem localDegreeInt_pow_split (j : ℕ) : localDegreeInt F (φ ^ j) = j := by
  change (localDegree F (φ ^ j)).toAdd = j
  rw [map_pow, hφ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one]

include hφ in
theorem pow_mem_unramifiedStage :
    φ ^ (m + 1) ∈ pullbackFixingSubgroup F.Carrier (unramifiedStage F (m + 1)).field
      (localResidueDegree F) := by
  rw [← intermediateWeilMap_range]
  apply (mem_unramifiedStage_weilRange F (m + 1) _).mpr
  rw [localDegreeInt_pow_split F φ hφ]

theorem localInertia_le_unramifiedStage :
    Langlands.Weil.Local.localInertia F ≤ pullbackFixingSubgroup F.Carrier (unramifiedStage F (m + 1)).field
      (localResidueDegree F) := by
  rw [← intermediateWeilMap_range]
  exact unramifiedStage_localInertia_le F (m + 1)

theorem unramifiedStage_residueDegree :
    extensionResidueDegree F ((unramifiedStage F (m + 1)).asPadicField (p := p))
      (intermediateEmbedding F (unramifiedStage F (m + 1))) = m + 1 :=
  (unramifiedStage_isUnramifiedOfDegree F (m + 1)).2

/-- The `(m + 1)`st power of the lift, as an element of the stage Weil group. -/
def stageLift : localWeilGroup ((unramifiedStage F (m + 1)).asPadicField (p := p)) :=
  (intermediateWeilEquiv F (unramifiedStage F (m + 1))).symm
    ⟨φ ^ (m + 1), pow_mem_unramifiedStage F φ hφ m⟩

theorem stageLift_degree :
    localDegree _ (stageLift F φ hφ m) = Multiplicative.ofAdd (1 : ℤ) := by
  have h := intermediateWeilEquiv_symm_degree F (unramifiedStage F (m + 1))
    ⟨φ ^ (m + 1), pow_mem_unramifiedStage F φ hφ m⟩
  rw [unramifiedStage_residueDegree] at h
  change localDegreeInt F (φ ^ (m + 1)) = _ * localDegreeInt _ (stageLift F φ hφ m) at h
  rw [localDegreeInt_pow_split F φ hφ] at h
  have h1 : localDegreeInt _ (stageLift F φ hφ m) = 1 := by
    have hne : ((m + 1 : ℕ) : ℤ) ≠ 0 := by positivity
    have h' : ((m + 1 : ℕ) : ℤ) * localDegreeInt _ (stageLift F φ hφ m) =
        ((m + 1 : ℕ) : ℤ) * 1 := by
      rw [mul_one]; exact h.symm
    exact mul_left_cancel₀ hne h'
  change Multiplicative.ofAdd (localDegreeInt _ (stageLift F φ hφ m)) = _
  rw [h1]

/-- Inertia of the base, viewed in the stage Weil group. -/
def stageKappa :
    Langlands.Weil.Local.localInertia F →* localWeilGroup ((unramifiedStage F (m + 1)).asPadicField (p := p)) :=
  (intermediateWeilEquiv F (unramifiedStage F (m + 1))).symm.toMonoidHom.comp
    (Subgroup.inclusion (localInertia_le_unramifiedStage F m))

/-- The unramified stage of degree `m + 1` as an abstract stage. -/
def weilStage : Stage (weilSplit F φ hφ)
    (weilSplit _ (stageLift F φ hφ m) (stageLift_degree F φ hφ m)) (m + 1) where
  ι := (intermediateWeilMap F (unramifiedStage F (m + 1))).toMonoidHom
  injective := intermediateWeilMap_injective F _
  continuous_ι := (intermediateWeilMap F _).continuous
  κ := stageKappa F m
  continuous_κ := (intermediateWeilEquiv F (unramifiedStage F (m + 1))).symm.continuous.comp
    (continuous_subtype_val.subtype_mk _)
  ι_κ n := intermediateWeilMap_equiv_symm F _ _
  degree_ι h := by
    have h' := intermediateWeilEquiv_degree F (unramifiedStage F (m + 1)) h
    rw [unramifiedStage_residueDegree] at h'
    exact h'
  ι_lift := intermediateWeilMap_equiv_symm F _ _

@[simp] theorem weilStage_ι (h : localWeilGroup ((unramifiedStage F (m + 1)).asPadicField (p := p))) :
    (weilStage F φ hφ m).ι h = intermediateWeilMap F (unramifiedStage F (m + 1)) h := rfl

end Stage

section Break

/-- The break of an inertia representation: the infimum of the nonnegative indices whose upper
ramification group acts trivially. -/
def inertiaBreak {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Langlands.Weil.Local.localInertia F) V) : ℝ :=
  sInf {v : ℝ | 0 ≤ v ∧ ∀ n : Langlands.Weil.Local.localInertia F, (n : localWeilGroup F) ∈ upperGroup F v → ρ n = 1}

instance upperGroup_normal' (v : ℝ) : (upperGroup F v).Normal :=
  Langlands.LocalFactor.NonabelianSystem.DeligneHenniart.upperGroup_normal F v

/-- The last break is the break of the inertia restriction. -/
theorem lastBreak_eq_inertiaBreak (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)) :
    lastBreak F A = inertiaBreak F (A.representation.comp (Langlands.Weil.Local.localInertia F).subtype) := by
  unfold lastBreak trivialityThresholds inertiaBreak
  congr 1
  ext v
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun n hn => h n hn⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun w hw => h ⟨w, Langlands.ArithmeticStableTwist.upperGroup_le_localInertia F hv hw⟩ hw⟩

theorem inertiaBreak_congr {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ (Langlands.Weil.Local.localInertia F) V} {σ : Representation ℂ (Langlands.Weil.Local.localInertia F) W}
    (h : ∀ v : ℝ, 0 ≤ v →
      ((∀ n : Langlands.Weil.Local.localInertia F, (n : localWeilGroup F) ∈ upperGroup F v → ρ n = 1) ↔
        (∀ n : Langlands.Weil.Local.localInertia F, (n : localWeilGroup F) ∈ upperGroup F v → σ n = 1))) :
    inertiaBreak F ρ = inertiaBreak F σ := by
  unfold inertiaBreak
  congr 1
  ext v
  constructor
  · rintro ⟨hv, h'⟩
    exact ⟨hv, (h v hv).mp h'⟩
  · rintro ⟨hv, h'⟩
    exact ⟨hv, (h v hv).mpr h'⟩

theorem eq_one_of_equiv {J : Type*} [Group J] {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ J V} {σ : Representation ℂ J W}
    (e : Representation.Equiv ρ σ) (n : J) (h : ρ n = 1) : σ n = 1 := by
  apply LinearMap.ext
  intro w
  have h1 := e.isIntertwining' n
  have h2 := congrArg (fun T : V →ₗ[ℂ] W => T (e.toLinearEquiv.symm w)) h1
  simp only [LinearMap.comp_apply, h, Module.End.one_apply] at h2
  change e.toLinearEquiv (e.toLinearEquiv.symm w) =
    σ n (e.toLinearEquiv (e.toLinearEquiv.symm w)) at h2
  rw [LinearEquiv.apply_symm_apply] at h2
  rw [Module.End.one_apply]
  exact h2.symm

/-- Isomorphic inertia representations have the same break. -/
theorem inertiaBreak_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ (Langlands.Weil.Local.localInertia F) V} {σ : Representation ℂ (Langlands.Weil.Local.localInertia F) W}
    (e : Representation.Equiv ρ σ) : inertiaBreak F ρ = inertiaBreak F σ :=
  inertiaBreak_congr F fun _ _ =>
    ⟨fun h n hn => eq_one_of_equiv e n (h n hn), fun h n hn => eq_one_of_equiv e.symm n (h n hn)⟩

end Break

end Langlands.Henniart.Numerical
