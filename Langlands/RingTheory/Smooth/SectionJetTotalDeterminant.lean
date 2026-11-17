import Langlands.RingTheory.Smooth.SectionJetLayerDeterminant
import Langlands.LinearAlgebra.SplitBasisDeterminant

/-! # Total augmentation-jet determinant transitions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v w

namespace Algebra.SectionJet.Coordinates

open Langlands.LinearAlgebra
open Langlands.GroupScheme.CoordinateWeights

variable (σ : Type w)

/-- Filtration-adapted basis indices for an entire jet. -/
def JetIndex : ℕ → Type w
  | 0 => ULift.{w} (Fin 1)
  | n + 1 => JetIndex n ⊕ HomogeneousPolynomial.MonomialIndex σ (n + 1)

noncomputable instance [DecidableEq σ] (n : ℕ) : DecidableEq (JetIndex σ n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq (ULift.{w} (Fin 1)))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs
      (DecidableEq (JetIndex σ n ⊕ HomogeneousPolynomial.MonomialIndex σ (n + 1)))

instance [Finite σ] (n : ℕ) : Finite (JetIndex σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite (ULift.{w} (Fin 1)))
  | succ n ih =>
    exact inferInstanceAs
      (Finite (JetIndex σ n ⊕ HomogeneousPolynomial.MonomialIndex σ (n + 1)))

noncomputable instance [Finite σ] (n : ℕ) : Fintype (JetIndex σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (ULift.{w} (Fin 1)))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs
      (Fintype (JetIndex σ n ⊕ HomogeneousPolynomial.MonomialIndex σ (n + 1)))

variable [Finite σ]

/-- The total jet determinant exponent, the sum of the positive-degree layer exponents. -/
def jetExponent : ℕ → ℕ
  | 0 => 0
  | n + 1 => jetExponent n + HomogeneousPolynomial.exponent σ (n + 1)

theorem jetExponent_pos (n : ℕ) (hn : 0 < n) : 0 < jetExponent σ n := by
  cases n with
  | zero => omega
  | succ n =>
    have h := HomogeneousPolynomial.exponent_pos σ (n + 1) (Nat.succ_pos n)
    simp only [jetExponent]
    omega

variable {σ}
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ε : A →ₐ[R] R} [Fintype σ] [DecidableEq σ] [FormallySmooth R A]

/-- A filtration-adapted basis of every actual jet, using an arbitrary family
of linear sections of its truncations and actual cotangent lifts. -/
def totalBasis (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ i, ε (z i) = 0)
    (hzb : ∀ i, AugmentedAlgebra.classMap ε (z i) = b i)
    (s : ∀ n, Quotient ε n →ₗ[R] Quotient ε (n + 1))
    (hs : ∀ n x, (truncate ε n).toLinearMap (s n x) = x) :
    (n : ℕ) → Module.Basis (JetIndex σ n) R (Quotient ε n)
  | 0 => (Module.Basis.singleton (ULift.{w} (Fin 1)) R).map
      (zeroEquiv ε).symm.toLinearEquiv
  | n + 1 => SplitBasis.adaptedBasis
      (truncate ε n).toLinearMap (s n) (hs n)
      (totalBasis z b hz hzb s hs n) (layerBasis z b hz hzb n)

set_option maxHeartbeats 800000 in
/-- The total actual-jet basis transition determinant is the corresponding
cotangent determinant power, independent of both families of linear sections. -/
theorem totalBasis_toMatrix_det
    (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ i, ε (z i) = 0)
    (hzb : ∀ i, AugmentedAlgebra.classMap ε (z i) = b i)
    (s : ∀ n, Quotient ε n →ₗ[R] Quotient ε (n + 1))
    (hs : ∀ n x, (truncate ε n).toLinearMap (s n x) = x)
    (z' : σ → A) (b' : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz' : ∀ i, ε (z' i) = 0)
    (hzb' : ∀ i, AugmentedAlgebra.classMap ε (z' i) = b' i)
    (t : ∀ n, Quotient ε n →ₗ[R] Quotient ε (n + 1))
    (ht : ∀ n x, (truncate ε n).toLinearMap (t n x) = x) (n : ℕ) :
    ((totalBasis z b hz hzb s hs n).toMatrix
      (totalBasis z' b' hz' hzb' t ht n)).det =
      (b.toMatrix b').det ^ jetExponent σ n := by
  classical
  induction n with
  | zero =>
    simp only [totalBasis, jetExponent, Module.Basis.toMatrix_self, Matrix.det_one, pow_zero]
  | succ n ih =>
    calc
      _ = ((totalBasis z b hz hzb s hs n).toMatrix
          (totalBasis z' b' hz' hzb' t ht n)).det *
          ((layerBasis z b hz hzb n).toMatrix (layerBasis z' b' hz' hzb' n)).det :=
        SplitBasis.adaptedBasis_toMatrix_det (truncate ε n).toLinearMap
          (s n) (hs n) (t n) (ht n)
          (totalBasis z b hz hzb s hs n) (totalBasis z' b' hz' hzb' t ht n)
          (layerBasis z b hz hzb n) (layerBasis z' b' hz' hzb' n)
      _ = _ := by rw [ih, layerBasis_toMatrix_det, jetExponent, pow_add]

/-- Finite-type formally smooth augmented algebras supply a family of sections,
so the filtration-adapted total bases always exist in that setting. -/
def chosenTotalBasis [FiniteType R A]
    (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ i, ε (z i) = 0)
    (hzb : ∀ i, AugmentedAlgebra.classMap ε (z i) = b i) (n : ℕ) :
    Module.Basis (JetIndex σ n) R (Quotient ε n) :=
  totalBasis z b hz hzb (linearSection ε) (fun n x => truncate_linearSection ε n x) n

end Algebra.SectionJet.Coordinates
