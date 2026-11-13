import Langlands.AbelianScheme.Tate.RationalPrimeScalars
import Langlands.Global.ProfiniteIntegerCompletionComparisonProof
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Actual prime extraction and finite-adelic scalars -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000

local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

namespace Langlands.Global

/-- Evaluation of an actual rational finite adele in the corresponding p-adic field. -/
def finiteAdeleToPadic (v : FinitePlace ℚ) :
    FiniteAdeles ℚ →ₐ[ℚ] ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val] where
  toFun a := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a v)
  map_one' := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).map_one
  map_mul' a b := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).map_mul (a v) (b v)
  map_zero' := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).map_zero
  map_add' a b := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).map_add (a v) (b v)
  commutes' q := by
    change Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
      (algebraMap ℚ (FiniteCompletion ℚ v) q) = _
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).commutes q

@[simp] theorem finiteAdeleToPadic_apply (v : FinitePlace ℚ) (a : FiniteAdeles ℚ) :
    finiteAdeleToPadic v a =
      Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a v) := rfl

namespace RationalProfiniteIntegerAdeleComparison

variable (h : RationalProfiniteIntegerAdeleComparison) (v : FinitePlace ℚ)

/-- Every normalized continuous integral scalar comparison has the canonical
p-adic coordinate, since the integer residue families are dense. -/
theorem integralEquiv_toPadic (a : ProfiniteIntegerRing) :
    finiteAdeleToPadic v (integralEquiv h a : FiniteAdeles ℚ) =
      (ProfiniteIntegerRing.toPadic (Rat.HeightOneSpectrum.primesEquiv v).val a :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]) := by
  have hinc : Continuous (fun a : integralFiniteAdeles ℚ => (a : FiniteAdeles ℚ)) :=
    continuous_subtype_val
  have hleft : Continuous (fun x : ProfiniteIntegerRing =>
      finiteAdeleToPadic v (integralEquiv h x : FiniteAdeles ℚ)) :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).continuous.comp
      ((RestrictedProduct.continuous_eval v).comp
        (hinc.comp h.choose_spec.1))
  have hright : Continuous (fun x : ProfiniteIntegerRing =>
      (ProfiniteIntegerRing.toPadic (Rat.HeightOneSpectrum.primesEquiv v).val x :
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])) :=
    continuous_subtype_val.comp (ProfiniteIntegerRing.continuous_toPadic _)
  have heq := residue_integer_dense.equalizer hleft hright
  apply congrFun (heq ?_) a
  funext z
  change finiteAdeleToPadic v
    (integralEquiv h (ProfiniteIntegerRing.intCastHom z) : FiniteAdeles ℚ) =
      (ProfiniteIntegerRing.toPadic (Rat.HeightOneSpectrum.primesEquiv v).val
        (ProfiniteIntegerRing.intCastHom z) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val])
  rw [show (integralEquiv h (ProfiniteIntegerRing.intCastHom z) : FiniteAdeles ℚ) =
      algebraMap ℚ (FiniteAdeles ℚ) (z : ℚ) from h.choose_spec.2.2.1 z]
  simp

/-- The coupled rational scalar comparison preserves every actual local projection. -/
theorem rationalEquiv_toPadic (a : ℚ ⊗[ℤ] ProfiniteIntegerRing) :
    finiteAdeleToPadic v (rationalEquiv h a) =
      ProfiniteIntegerRing.rationalToPadic (Rat.HeightOneSpectrum.primesEquiv v).val a := by
  induction a using TensorProduct.inductionOn with
  | tmul q a =>
    rw [rationalEquiv_tmul, map_mul, AlgHom.commutes, integralEquiv_toPadic,
      ProfiniteIntegerRing.rationalToPadic_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- The inverse scalar comparison has the same canonical local normalization. -/
theorem rationalEquiv_symm_toPadic (a : FiniteAdeles ℚ) :
    ProfiniteIntegerRing.rationalToPadic (Rat.HeightOneSpectrum.primesEquiv v).val
        ((rationalEquiv h).symm a) = finiteAdeleToPadic v a := by
  rw [← rationalEquiv_toPadic h v, AlgEquiv.apply_symm_apply]

end RationalProfiniteIntegerAdeleComparison
end Langlands.Global

namespace Langlands.GroupScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)
  (h : Global.RationalProfiniteIntegerAdeleComparison) (v : Global.FinitePlace ℚ)

/-- Actual rational prime extraction is semilinear for the finite-adelic action
and the actual corresponding finite-place evaluation. -/
theorem rationalFullToPrime_finiteAdeleAction
    (a : Global.FiniteAdeles ℚ) (x : RationalFull G T) :
    rationalFullToPrime G T (Rat.HeightOneSpectrum.primesEquiv v).val
        (finiteAdeleAction G T (fun _ => True) h a x) =
      Global.finiteAdeleToPadic v a •
        rationalFullToPrime G T (Rat.HeightOneSpectrum.primesEquiv v).val x := by
  change rationalFullToPrime G T (Rat.HeightOneSpectrum.primesEquiv v).val
      (rationalScalarAction G T (fun _ => True)
        ((Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv h).symm a) x) = _
  rw [rationalFullToPrime_scalarAction,
    Global.RationalProfiniteIntegerAdeleComparison.rationalEquiv_symm_toPadic]

end Langlands.GroupScheme.Tate.PrimeComparison

namespace Langlands.AbelianScheme.Tate.PrimeComparison

universe u
variable {S : Scheme.{u}} (B : AbelianScheme S) (T : Over S)
  (h : Global.RationalProfiniteIntegerAdeleComparison) (v : Global.FinitePlace ℚ)

/-- Actual abelian-scheme prime extraction preserves the finite-adelic scalar projection. -/
theorem rationalFullToPrime_finiteAdeleAction
    (a : Global.FiniteAdeles ℚ) (x : RationalFull B T) :
    rationalFullToPrime B T (Rat.HeightOneSpectrum.primesEquiv v).val
        (finiteAdeleAction B T (fun _ => True) h a x) =
      Global.finiteAdeleToPadic v a •
        rationalFullToPrime B T (Rat.HeightOneSpectrum.primesEquiv v).val x :=
  GroupScheme.Tate.PrimeComparison.rationalFullToPrime_finiteAdeleAction B.toGrp T h v a x

end Langlands.AbelianScheme.Tate.PrimeComparison
