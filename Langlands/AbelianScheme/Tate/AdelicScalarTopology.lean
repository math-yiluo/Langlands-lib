import Langlands.AbelianScheme.Tate.RationalScalarTopology
import Langlands.AbelianScheme.Tate.RationalTopology

noncomputable section
open scoped TensorProduct
open Topology
open CategoryTheory AlgebraicGeometry

namespace Langlands.TateScalarExtension

local instance {M : Type*} [AddCommGroup M] [TopologicalSpace M] :
    TopologicalSpace (ℚ ⊗[ℤ] M) := Langlands.Topology.Rationalization.finalTopology M

private theorem isOpenEmbedding_chart {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    (hM : IsOpenEmbedding (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x))
    (q : ℚ) (hq : q ≠ 0) :
    IsOpenEmbedding (fun x : M => q ⊗ₜ[ℤ] x) := by
  have hc := (Langlands.Topology.Rationalization.scalarHomeomorph q hq).isOpenEmbedding.comp hM
  change IsOpenEmbedding (fun x : M => q • ((1 : ℚ) ⊗ₜ[ℤ] x)) at hc
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hc

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace R] [TopologicalSpace M] [ContinuousSMul R M]

/-- Joint continuity of rational scalar extension when both integral charts are open. -/
theorem continuous_action
    (hR : IsOpenEmbedding (fun a : R => (1 : ℚ) ⊗ₜ[ℤ] a))
    (hM : IsOpenEmbedding (fun x : M => (1 : ℚ) ⊗ₜ[ℤ] x)) :
    Continuous (fun p : (ℚ ⊗[ℤ] R) × (ℚ ⊗[ℤ] M) => action R M p.1 p.2) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨a, x⟩
  obtain ⟨q, hq, a, rfl⟩ := Langlands.Topology.Rationalization.exists_chart a
  obtain ⟨r, hr, x, rfl⟩ := Langlands.Topology.Rationalization.exists_chart x
  apply (((isOpenEmbedding_chart hR q hq).prodMap
    (isOpenEmbedding_chart hM r hr)).continuousAt_iff (x := (a, x))).mp
  have hc := (Langlands.Topology.Rationalization.continuous_tmul (M := M) (q * r)).comp
    (continuous_smul : Continuous (fun p : R × M => p.1 • p.2))
  change ContinuousAt (fun p : R × M => action R M (q ⊗ₜ[ℤ] p.1) (r ⊗ₜ[ℤ] p.2)) (a, x)
  simpa only [action_tmul, Function.comp_def] using hc.continuousAt

end Langlands.TateScalarExtension

namespace Langlands.Global.RationalProfiniteIntegerAdeleComparison

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

local instance : TopologicalSpace (ℚ ⊗[ℤ] Global.ProfiniteIntegerRing) :=
  Langlands.Topology.Rationalization.finalTopology Global.ProfiniteIntegerRing

include h in
/-- The actual integral residue scalars form an open subspace of their rationalization. -/
theorem isOpenEmbedding_integralChart :
    IsOpenEmbedding (fun a : Global.ProfiniteIntegerRing => (1 : ℚ) ⊗ₜ[ℤ] a) := by
  have hc := (rationalHomeomorph h).symm.isOpenEmbedding.comp (isOpenEmbedding_integralEquiv h)
  have he : (rationalHomeomorph h).symm ∘
      (fun a : Global.ProfiniteIntegerRing => (integralEquiv h a : Global.FiniteAdeles ℚ)) =
      (fun a => (1 : ℚ) ⊗ₜ[ℤ] a) := by
    funext a
    apply (rationalHomeomorph h).injective
    change rationalHomeomorph h ((rationalHomeomorph h).symm _) = _
    rw [Homeomorph.apply_symm_apply, rationalHomeomorph_apply, rationalEquiv_tmul,
      map_one, one_mul]
  rw [he] at hc
  exact hc

end Langlands.Global.RationalProfiniteIntegerAdeleComparison

namespace Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison

variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

local instance : TopologicalSpace (ℚ ⊗[ℤ] Global.PrimeToProfiniteIntegerRing m) :=
  Langlands.Topology.Rationalization.finalTopology (Global.PrimeToProfiniteIntegerRing m)

include hAway in
theorem isOpenEmbedding_integralChart :
    IsOpenEmbedding (fun a : Global.PrimeToProfiniteIntegerRing m =>
      (1 : ℚ) ⊗ₜ[ℤ] a) := by
  have hc := (rationalHomeomorph hAway).symm.isOpenEmbedding.comp
    (isOpenEmbedding_integralEquiv hAway)
  have he : (rationalHomeomorph hAway).symm ∘
      (fun a : Global.PrimeToProfiniteIntegerRing m =>
        (integralEquiv hAway a : Global.PrimeToFiniteAdeles m)) =
      (fun a => (1 : ℚ) ⊗ₜ[ℤ] a) := by
    funext a
    apply (rationalHomeomorph hAway).injective
    change rationalHomeomorph hAway ((rationalHomeomorph hAway).symm _) = _
    rw [Homeomorph.apply_symm_apply, rationalHomeomorph_apply, rationalEquiv_tmul,
      map_one, one_mul]
  rw [he] at hc
  exact hc

end Langlands.Global.PrimeToRationalProfiniteIntegerAdeleComparison

namespace Langlands.AbelianScheme.Tate

open scoped CategoryTheory.MonObj
universe u
variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)

attribute [local instance] rationalTopology

local instance {M : Type*} [AddCommGroup M] [TopologicalSpace M] :
    TopologicalSpace (ℚ ⊗[ℤ] M) := Langlands.Topology.Rationalization.finalTopology M

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- The existing finite-adelic scalar action is jointly continuous on the full Tate carrier. -/
theorem continuous_finiteAdeleAction :
    Continuous (fun p : Global.FiniteAdeles ℚ × RationalFull A T =>
      finiteAdeleAction A T (fun _ => True) h p.1 p.2) := by
  have hc := TateScalarExtension.continuous_action Global.ProfiniteIntegerRing
    (Integral A T (fun _ => True))
    (Global.RationalProfiniteIntegerAdeleComparison.isOpenEmbedding_integralChart h)
    (isOpenEmbedding_full_toRational A T)
  exact hc.comp
    (((Global.RationalProfiniteIntegerAdeleComparison.rationalHomeomorph h).symm.continuous.comp
      continuous_fst).prodMk continuous_snd)

/-- The actual full adelic action as a jointly continuous map. -/
def finiteAdeleContinuousAction :
    C(Global.FiniteAdeles ℚ × RationalFull A T, RationalFull A T) where
  toFun p := finiteAdeleAction A T (fun _ => True) h p.1 p.2
  continuous_toFun := continuous_finiteAdeleAction A T h

@[simp] theorem finiteAdeleContinuousAction_apply
    (a : Global.FiniteAdeles ℚ) (x : RationalFull A T) :
    finiteAdeleContinuousAction A T h (a, x) =
      finiteAdeleAction A T (fun _ => True) h a x := rfl

/-- Joint continuity for the existing locally installed finite-adelic module structure. -/
theorem finiteAdeleModule_continuousSMul :
    let := finiteAdeleModule A T (fun _ => True) h
    ContinuousSMul (Global.FiniteAdeles ℚ) (RationalFull A T) := by
  let := finiteAdeleModule A T (fun _ => True) h
  exact ⟨continuous_finiteAdeleAction A T h⟩

variable {h} {m : ℕ}
variable (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- Joint continuity of the existing away adelic scalar action for every modulus. -/
theorem continuous_primeToFiniteAdeleAction :
    Continuous (fun p : Global.PrimeToFiniteAdeles m × RationalAway A T m =>
      primeToFiniteAdeleAction A T hAway p.1 p.2) := by
  have hc := TateScalarExtension.continuous_action (Global.PrimeToProfiniteIntegerRing m)
    (GroupScheme.Tate.Away A.toGrp T m)
    (Global.PrimeToRationalProfiniteIntegerAdeleComparison.isOpenEmbedding_integralChart hAway)
    (isOpenEmbedding_away_toRational A T m)
  exact hc.comp
    (((Global.PrimeToRationalProfiniteIntegerAdeleComparison.rationalHomeomorph hAway).symm.continuous.comp
      continuous_fst).prodMk continuous_snd)

def primeToFiniteAdeleContinuousAction :
    C(Global.PrimeToFiniteAdeles m × RationalAway A T m, RationalAway A T m) where
  toFun p := primeToFiniteAdeleAction A T hAway p.1 p.2
  continuous_toFun := continuous_primeToFiniteAdeleAction A T hAway

@[simp] theorem primeToFiniteAdeleContinuousAction_apply
    (a : Global.PrimeToFiniteAdeles m) (x : RationalAway A T m) :
    primeToFiniteAdeleContinuousAction A T hAway (a, x) =
      primeToFiniteAdeleAction A T hAway a x := rfl

theorem primeToFiniteAdeleModule_continuousSMul :
    let := primeToFiniteAdeleModule A T hAway
    ContinuousSMul (Global.PrimeToFiniteAdeles m) (RationalAway A T m) := by
  let := primeToFiniteAdeleModule A T hAway
  exact ⟨continuous_primeToFiniteAdeleAction A T hAway⟩

end Langlands.AbelianScheme.Tate
