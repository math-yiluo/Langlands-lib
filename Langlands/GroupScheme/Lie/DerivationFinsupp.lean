import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Finite coefficient families of derivations -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Lie

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {M : Type v} [AddCommGroup M] [Module C M] [Module R M]
  [IsScalarTower R C M]
variable {ι : Type w}

/-- Extract one coefficient of a derivation into a finitely supported family. -/
def derivationCoefficient (i : ι) :
    Derivation R C (ι →₀ M) →ₗ[C] Derivation R C M :=
  (Finsupp.lapply i : (ι →₀ M) →ₗ[C] M).compDer

@[simp] theorem derivationCoefficient_apply (i : ι)
    (d : Derivation R C (ι →₀ M)) (c : C) :
    derivationCoefficient i d c = d c i := rfl

/-- Finite algebra generation gives a uniform finite set of nonzero coefficients. -/
theorem derivationCoefficient_finite [Algebra.FiniteType R C]
    (d : Derivation R C (ι →₀ M)) :
    (Function.support (fun i => derivationCoefficient i d)).Finite := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := C)
  refine (s.biUnion (fun c => (d c).support)).finite_toSet.subset ?_
  intro i hi
  by_contra h
  apply hi
  apply Derivation.ext_of_adjoin_eq_top (s : Set C) hs
  intro c hc
  change (d c) i = 0
  by_contra hic
  exact h (Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_support_iff.mpr hic⟩)

/-- The coefficient derivations, as an actual finite family. -/
def derivationCoefficients [Algebra.FiniteType R C] :
    Derivation R C (ι →₀ M) →ₗ[C] (ι →₀ Derivation R C M) where
  toFun d := Finsupp.ofSupportFinite (fun i => derivationCoefficient i d)
    (derivationCoefficient_finite d)
  map_add' d e := by ext i c; rfl
  map_smul' c d := by ext i e; rfl

@[simp] theorem derivationCoefficients_apply [Algebra.FiniteType R C]
    (d : Derivation R C (ι →₀ M)) (i : ι) (c : C) :
    derivationCoefficients d i c = d c i := rfl

/-- Assemble coefficient derivations by their finitely supported sum. -/
def sumDerivationCoefficients : (ι →₀ Derivation R C M) →ₗ[C]
    Derivation R C (ι →₀ M) :=
  Finsupp.lsum C fun i => (Finsupp.lsingle i : M →ₗ[C] (ι →₀ M)).compDer

@[simp] theorem sumDerivationCoefficients_single (i : ι) (d : Derivation R C M) :
    sumDerivationCoefficients (Finsupp.single i d) =
      (Finsupp.lsingle i : M →ₗ[C] (ι →₀ M)).compDer d :=
  Finsupp.lsum_single C _ i d

@[simp] theorem sumDerivationCoefficients_apply
    (d : ι →₀ Derivation R C M) (c : C) (i : ι) :
    sumDerivationCoefficients d c i = d i c := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp [hd, he]
  | single j e =>
      simp only [sumDerivationCoefficients_single]
      change (Finsupp.single j (e c)) i = (Finsupp.single j e) i c
      by_cases h : j = i
      · subst i; simp
      · simp [Finsupp.single_eq_of_ne (Ne.symm h)]

/-- Derivations out of a finite-type algebra commute with finitely supported sums. -/
def derivationFinsuppLinearEquiv [Algebra.FiniteType R C] :
    Derivation R C (ι →₀ M) ≃ₗ[C] (ι →₀ Derivation R C M) where
  toLinearMap := derivationCoefficients
  invFun := sumDerivationCoefficients
  left_inv d := by ext c i; simp
  right_inv d := by ext i c; simp

end Langlands.GroupScheme.Lie
