import Mathlib.Topology.LocallyConstant.Basic
import Langlands.Representation.Conductor.Definitions
import Langlands.Representation.Whittaker.Algebraic
import Langlands.Group.GL.RankMaps
import Langlands.Group.GL.UpperUnipotent

/-!
# Spherical test vectors for the corrected essential-vector construction

The test vectors belong to actual coefficient images. Normalization is performed
only on a supplied spherical vector whose value at the identity is nonzero.
No spherical existence, multiplicity one, test integral or local factor is
asserted here.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker

universe uF uV uW

section IntegralRank

universe uR uS

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] {r : ℕ}

private theorem rankInclusion_last_row (g : Langlands.GeneralLinear r R) :
    (rankInclusion 1 g).val (Fin.last r) =
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (Fin.last r) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change blockSum (g, 1) ((0 : Fin 1).natAdd r) ((0 : Fin 1).natAdd r) = _
    rw [blockSum_apply_right]
    simp
  · change blockSum (g, 1) ((0 : Fin 1).natAdd r) (j.castAdd 1) = _
    rw [blockSum_apply_right_left]
    change 0 = if Fin.last r = j.castSucc then 1 else 0
    have hj : Fin.last r ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      have hlt := j.isLt
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    simp [hj]

private theorem rankInclusion_map (f : R →+* S) (g : Langlands.GeneralLinear r R) :
    Matrix.GeneralLinearGroup.map f (rankInclusion 1 g) =
      rankInclusion 1 (Matrix.GeneralLinearGroup.map f g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · change f (blockSum (g, 1) ((0 : Fin 1).natAdd r) ((0 : Fin 1).natAdd r)) =
        blockSum (Matrix.GeneralLinearGroup.map f g, 1)
          ((0 : Fin 1).natAdd r) ((0 : Fin 1).natAdd r)
      simp
    · change f (blockSum (g, 1) ((0 : Fin 1).natAdd r) (j.castAdd 1)) =
        blockSum (Matrix.GeneralLinearGroup.map f g, 1) ((0 : Fin 1).natAdd r) (j.castAdd 1)
      simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · change f (blockSum (g, 1) (i.castAdd 1) ((0 : Fin 1).natAdd r)) =
        blockSum (Matrix.GeneralLinearGroup.map f g, 1) (i.castAdd 1) ((0 : Fin 1).natAdd r)
      simp
    · change f (blockSum (g, 1) (i.castAdd 1) (j.castAdd 1)) =
        blockSum (Matrix.GeneralLinearGroup.map f g, 1) (i.castAdd 1) (j.castAdd 1)
      simp

/-- The embedded smaller integral group lies in every larger congruence group.
Its last row is the identity row exactly, before any reduction. -/
theorem rankInclusion_mem_congruenceSubgroup {F : Type uF} [Field F]
    (O : Subring F) (n : ℕ) (I : Ideal O) (k : integralSubgroup O n) :
    rankInclusion 1 k.val ∈ congruenceSubgroup O (n + 1) I := by
  obtain ⟨kO, hk⟩ := k.property
  refine ⟨rankInclusion 1 kO, ?_, ?_⟩
  · apply (mem_integralCongruence (n + 1) I _).mpr
    intro j
    rw [congrFun (rankInclusion_last_row kO) j, sub_self]
    exact I.zero_mem
  · rw [rankInclusion_map, hk]

end IntegralRank

variable {F : Type uF} [Field F] [ValuativeRel F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {n : ℕ} {θ : upperUnipotent (n + 1) F →* ℂˣ}
variable (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
variable (ℓ : functionals (upperUnipotent (n + 1) F) θ σ)

/-- Evaluation at one on the actual coefficient image, as a linear map. -/
def modelEvaluation :
    (coefficientModel σ ℓ).toSubmodule →ₗ[ℂ] ℂ where
  toFun w := w.val.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Spherical vectors in a coefficient model are its level-zero fixed vectors. -/
abbrev sphericalModelSpace : Submodule ℂ (coefficientModel σ ℓ).toSubmodule :=
  levelFixedVectors (K := ℂ) (F := F) (V := (coefficientModel σ ℓ).toSubmodule)
    (modelRepresentation σ ℓ) 0

/-- The fixed-space condition is exactly right invariance under the integral group. -/
theorem mem_sphericalModelSpace (w : (coefficientModel σ ℓ).toSubmodule) :
    w ∈ sphericalModelSpace σ ℓ ↔
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        ∀ g, w.val.val (g * k) = w.val.val g := by
  rw [sphericalModelSpace, mem_levelFixedVectors, levelSubgroup_zero]
  constructor
  · intro hw k hk g
    exact congrArg (fun z : (coefficientModel σ ℓ).toSubmodule => z.val.val g) (hw k hk)
  · intro hw k hk
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact hw k hk g

/-- An identity-normalized spherical vector in the specified coefficient image.
This subtype may be empty; its definition does not assert spherical existence. -/
def SphericalTest :=
  {w : sphericalModelSpace σ ℓ // modelEvaluation σ ℓ w = 1}

/-- Normalize a specified spherical vector with nonzero identity value. -/
def normalizeSphericalTest (w : sphericalModelSpace σ ℓ)
    (hw : modelEvaluation σ ℓ w ≠ 0) : SphericalTest σ ℓ :=
  ⟨(modelEvaluation σ ℓ w)⁻¹ • w, by
    change modelEvaluation σ ℓ ((modelEvaluation σ ℓ w)⁻¹ • w.val) = 1
    simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩

/-- The scalar function represented by a normalized spherical test. -/
def sphericalTestFunction (w : SphericalTest σ ℓ) :
    Langlands.GeneralLinear (n + 1) F → ℂ :=
  w.val.val.val.val

@[simp] theorem sphericalTestFunction_one (w : SphericalTest σ ℓ) :
    sphericalTestFunction σ ℓ w 1 = 1 :=
  w.property

theorem sphericalTestFunction_right_invariant (w : SphericalTest σ ℓ)
    (k : integralSubgroup (ValuativeRel.valuation F).integer n)
    (g : Langlands.GeneralLinear (n + 1) F) :
    sphericalTestFunction σ ℓ w (g * k.val) =
      sphericalTestFunction σ ℓ w g :=
  (mem_sphericalModelSpace σ ℓ w.val.val).mp w.val.property k.val k.property g

theorem sphericalTestFunction_equivariance (w : SphericalTest σ ℓ)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    sphericalTestFunction σ ℓ w (u.val * g) =
      (θ u : ℂ) * sphericalTestFunction σ ℓ w g :=
  w.val.val.val.property u g

/-- A normalized test cannot be the zero model vector. -/
theorem sphericalTest_ne_zero (w : SphericalTest σ ℓ) :
    w.val.val ≠ 0 := by
  intro h
  have he := w.property
  change modelEvaluation σ ℓ w.val.val = 1 at he
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Existence of a normalized test is exactly nonvanishing of evaluation on
some actual spherical vector. No multiplicity-one theorem is implicit. -/
theorem nonempty_sphericalTest_iff :
    Nonempty (SphericalTest σ ℓ) ↔
      ∃ w : sphericalModelSpace σ ℓ, modelEvaluation σ ℓ w ≠ 0 := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.val, by rw [w.property]; exact one_ne_zero⟩
  · rintro ⟨w, hw⟩
    exact ⟨normalizeSphericalTest σ ℓ w hw⟩

section LocalField

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Each spherical test is smooth by the proved openness of the integral group,
even without assuming smoothness of the entire source representation. -/
theorem sphericalTest_isSmoothVector (w : SphericalTest σ ℓ) :
    IsSmoothVector (R := ℂ) (V := (coefficientModel σ ℓ).toSubmodule)
      (modelRepresentation σ ℓ) w.val.val :=
  ⟨levelOpenSubgroup F n 0, w.val.property⟩

/-- The function of an actual spherical test is locally constant: it is constant
on each left translate of the open integral group. -/
theorem sphericalTestFunction_isLocallyConstant (w : SphericalTest σ ℓ) :
    IsLocallyConstant (sphericalTestFunction σ ℓ w) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  have hK : IsOpen (levelOpenSubgroup F n 0 : Set (Langlands.GeneralLinear (n + 1) F)) :=
    (levelOpenSubgroup F n 0).isOpen
  refine ⟨(fun h : Langlands.GeneralLinear (n + 1) F => g⁻¹ * h) ⁻¹'
      (levelOpenSubgroup F n 0 : Set (Langlands.GeneralLinear (n + 1) F)),
    hK.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change g⁻¹ * g ∈ levelSubgroup F n 0
    rw [inv_mul_cancel]
    exact (levelSubgroup F n 0).one_mem
  · intro h hh
    have hk : g⁻¹ * h ∈ integralSubgroup (ValuativeRel.valuation F).integer n := by
      rw [← levelSubgroup_zero]
      exact hh
    have hr := sphericalTestFunction_right_invariant σ ℓ w ⟨g⁻¹ * h, hk⟩ g
    change sphericalTestFunction σ ℓ w (g * (g⁻¹ * h)) = _ at hr
    rwa [mul_inv_cancel_left] at hr

end LocalField

section Restriction

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {θ' : upperUnipotent ((n + 1) + 1) F →* ℂˣ}
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) W)
variable (ell : functionals (upperUnipotent ((n + 1) + 1) F) θ' π)

/-- The precise restriction-invariance condition in Jacquet's uniqueness clause.
Only the function restricted to `diag(GL_(n+1),1)` is tested here. -/
def IsIntegralInvariantOnRestriction (w : (coefficientModel π ell).toSubmodule) : Prop :=
  ∀ (g : Langlands.GeneralLinear (n + 1) F)
    (k : integralSubgroup (ValuativeRel.valuation F).integer n),
    w.val.val (rankInclusion 1 (g * k.val)) =
      w.val.val (rankInclusion 1 g)

/-- Fixing any actual newvector level implies the restriction-invariance
condition, without an essential-vector existence assumption. -/
theorem isIntegralInvariantOnRestriction_of_mem_levelFixedVectors
    {a : ℕ} (w : (coefficientModel π ell).toSubmodule)
    (hw : w ∈ levelFixedVectors (V := (coefficientModel π ell).toSubmodule)
      (modelRepresentation π ell) a) :
    IsIntegralInvariantOnRestriction π ell w := by
  intro g k
  have hk : rankInclusion 1 k.val ∈ levelSubgroup F (n + 1) a :=
    rankInclusion_mem_congruenceSubgroup _ _ _ k
  have he : modelRepresentation π ell (rankInclusion 1 k.val) w = w :=
    hw ⟨rankInclusion 1 k.val, hk⟩
  have hi := congrArg
    (fun z : (coefficientModel π ell).toSubmodule => z.val.val (rankInclusion 1 g)) he
  change w.val.val (rankInclusion 1 g * rankInclusion 1 k.val) =
    w.val.val (rankInclusion 1 g) at hi
  simpa only [map_mul] using hi

end Restriction

end Langlands.Conductor
