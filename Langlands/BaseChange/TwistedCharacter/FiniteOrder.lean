import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.Representation.Smooth.Schur.Proof

/-! # Finite-order normalization of a twisting isomorphism -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

universe uG uV uW

section Algebra

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (θ : MulAut G)

/-- A power of the twisting map intertwines the corresponding power of the automorphism. -/
theorem twistingEquiv_pow_apply (A : ρ.Equiv (ρ.comp θ.toMonoidHom))
    (d : ℕ) (g : G) (v : V) :
    (A.toLinearMap ^ d) (ρ g v) = ρ ((θ ^ d) g) ((A.toLinearMap ^ d) v) := by
  induction d with
  | zero => simp only [pow_zero, Module.End.one_apply, MulAut.one_apply]
  | succ d ih =>
    rw [pow_succ' A.toLinearMap, Module.End.mul_apply, Module.End.mul_apply, ih,
      pow_succ' θ, MulAut.mul_apply]
    exact LinearMap.congr_fun (A.isIntertwining' ((θ ^ d) g)) ((A.toLinearMap ^ d) v)

/-- Scalar multiplication by a complex unit preserves the twisting isomorphism. -/
def scaleTwistingEquiv (c : ℂˣ) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    ρ.Equiv (ρ.comp θ.toMonoidHom) :=
  Representation.Equiv.mk (A.toLinearEquiv.trans (LinearEquiv.smulOfUnit c)) fun g => by
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun (A.isIntertwining' g) v
    change A (ρ g v) = ρ (θ g) (A v) at h
    change (c : ℂ) • A (ρ g v) = ρ (θ g) ((c : ℂ) • A v)
    rw [map_smul, h]

@[simp]
theorem scaleTwistingEquiv_toLinearMap (c : ℂˣ) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    (scaleTwistingEquiv θ c A).toLinearMap = (c : ℂ) • A.toLinearMap := rfl

variable [TopologicalSpace G]

/-- Any twisting isomorphism of an admissible irreducible representation can be scaled to
have `d`-th power the identity, when the automorphism has this power. -/
theorem exists_twistingEquiv_normalizingScalar (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) {d : ℕ} (hd : 0 < d) (hθ : θ ^ d = 1) :
    ∃ c : ℂˣ, ((c : ℂ) • A.toLinearMap) ^ d = 1 := by
  let T : ρ.IntertwiningMap ρ := ⟨A.toLinearMap ^ d, fun g => LinearMap.ext fun v => by
    have h := twistingEquiv_pow_apply θ A d g v
    rwa [hθ, MulAut.one_apply] at h⟩
  obtain ⟨a, ha, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ hirr T
  have hpow : A.toLinearMap ^ d = a • (1 : Module.End ℂ V) :=
    congrArg Representation.IntertwiningMap.toLinearMap ha
  have hane : a ≠ 0 := by
    intro hz
    let := hirr
    let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    have hinj (n : ℕ) : Function.Injective (A.toLinearMap ^ n : Module.End ℂ V) := by
      induction n with
      | zero =>
        rw [pow_zero]
        exact Function.injective_id
      | succ n ih =>
        rw [pow_succ']
        exact A.injective.comp ih
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv (hinj d ?_)
    rw [hpow, hz, zero_smul]
    rfl
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ hd
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, zero_pow hd.ne'] at hc
    exact (inv_ne_zero hane) hc.symm
  refine ⟨Units.mk0 c hcne, ?_⟩
  change (c • A.toLinearMap) ^ d = 1
  rw [smul_pow, hc, hpow, smul_smul, inv_mul_cancel₀ hane, one_smul]

/-- Two twisting isomorphisms of one irreducible admissible representation with `d`-th
power one differ by a `d`-th root of unity on the entire carrier. -/
theorem exists_rootOfUnity_smul_twistingEquiv (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible)
    (A B : ρ.Equiv (ρ.comp θ.toMonoidHom)) {d : ℕ}
    (hA : A.toLinearMap ^ d = 1) (hB : B.toLinearMap ^ d = 1) :
    ∃ c : ℂ, c ^ d = 1 ∧ B.toLinearMap = c • A.toLinearMap := by
  let S : ρ.IntertwiningMap ρ := A.symm.toIntertwiningMap.comp B.toIntertwiningMap
  obtain ⟨c, hc, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ hirr S
  have hBA : B.toLinearMap = c • A.toLinearMap := by
    apply LinearMap.ext
    intro v
    have he := congrArg (fun f : ρ.IntertwiningMap ρ => f v) hc
    change A.symm (B v) = c • v at he
    change B v = c • A v
    exact (A.apply_symm_apply (B v)).symm.trans
      ((congrArg A he).trans (map_smul A.toLinearEquiv c v))
  have hp : c ^ d • (1 : Module.End ℂ V) = 1 := by
    calc
      c ^ d • (1 : Module.End ℂ V) = c ^ d • A.toLinearMap ^ d := by rw [hA]
      _ = (c • A.toLinearMap) ^ d := (smul_pow _ _ _).symm
      _ = B.toLinearMap ^ d := by rw [hBA]
      _ = 1 := hB
  let := hirr
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨c, smul_left_injective ℂ hv ?_, hBA⟩
  simpa only [LinearMap.smul_apply, Module.End.one_apply, one_smul] using LinearMap.congr_fun hp v

end Algebra

section Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type*} [Group M] {X : Type uV} [AddCommGroup X] [Module ℂ X]

/-- The induced twisting isomorphism has `d`-th power one if the action on the
ambient group and the inducing twisting operator both have this power. -/
theorem inducedTwistedIntertwiner_pow_eq_one (θ : MulAut G) (hθ : Continuous θ)
    (hθ' : Continuous θ.symm) (P : Subgroup G) (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (p : P →* M)
    (θM : M ≃* M) (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x))
    (Ξ : Representation ℂ M X) (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom))
    {d : ℕ} (hθd : θ ^ d = 1) (hBd : B.toLinearMap ^ d = 1) :
    (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B).toLinearMap ^ d = 1 := by
  let T := inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B
  have hEval (j : ℕ) (f : Induction.SmoothFunctions P (Ξ.comp p)) (g : G) :
      Induction.eval P (Ξ.comp p) ((T.toLinearMap ^ j) f) g =
        (B.toLinearMap ^ j) (Induction.eval P (Ξ.comp p) f (((θ⁻¹ : MulAut G) ^ j) g)) := by
    induction j generalizing g with
    | zero => simp only [pow_zero, Module.End.one_apply, MulAut.one_apply]
    | succ j ih =>
      rw [pow_succ' T.toLinearMap, Module.End.mul_apply]
      change Induction.eval P (Ξ.comp p) (T ((T.toLinearMap ^ j) f)) g = _
      rw [eval_inducedTwistedIntertwiner, ih, pow_succ' B.toLinearMap, Module.End.mul_apply,
        pow_succ (θ⁻¹ : MulAut G), MulAut.mul_apply]
      rfl
  have hInv : (θ⁻¹ : MulAut G) ^ d = 1 := by rw [inv_pow, hθd, inv_one]
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change Induction.eval P (Ξ.comp p) ((T.toLinearMap ^ d) f) g = Induction.eval P (Ξ.comp p) f g
  rw [hEval, hBd, hInv, Module.End.one_apply, MulAut.one_apply]

end Induction

section Distributions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {π : Representation ℂ G W} (θ : MulAut G)

/-- Comparing equivalent irreducible representations with finite-order twisting
isomorphisms makes their whole twisted distributions proportional by a root of unity. -/
theorem exists_rootOfUnity_twistedDistribution_eq_smul_of_equiv
    (hρ : IsAdmissible ρ) (hirr : ρ.IsIrreducible) (hπ : IsAdmissible π) (e : ρ.Equiv π)
    (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) (B : π.Equiv (π.comp θ.toMonoidHom)) {d : ℕ}
    (hA : A.toLinearMap ^ d = 1) (hB : B.toLinearMap ^ d = 1) :
    ∃ c : ℂ, c ^ d = 1 ∧ twistedDistribution μ π hπ B.toLinearMap =
      c • twistedDistribution μ ρ hρ A.toLinearMap := by
  let eθ : Representation.Equiv (π.comp θ.toMonoidHom) (ρ.comp θ.toMonoidHom) :=
    Representation.Equiv.mk e.symm.toLinearEquiv (fun g => e.symm.isIntertwining' (θ g))
  let C := (e.trans B).trans eθ
  let D := e.symm.toLinearEquiv.conjAlgEquiv ℂ
  have hC : C.toLinearMap = D B.toLinearMap := rfl
  have hCpow : C.toLinearMap ^ d = 1 := by rw [hC, ← map_pow, hB, map_one]
  obtain ⟨c, hc, hAC⟩ := exists_rootOfUnity_smul_twistingEquiv θ hρ hirr A C hA hCpow
  refine ⟨c, hc, ?_⟩
  calc
    twistedDistribution μ π hπ B.toLinearMap = twistedDistribution μ ρ hρ C.toLinearMap :=
      (twistedDistribution_eq_of_equivalent μ hπ hρ e.symm B.toLinearMap).symm
    _ = c • twistedDistribution μ ρ hρ A.toLinearMap := by
      rw [hAC, twistedDistribution_smul]

end Distributions

end Langlands.BaseChange
