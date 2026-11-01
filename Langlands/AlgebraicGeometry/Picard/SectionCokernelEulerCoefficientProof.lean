import Langlands.AlgebraicGeometry.Picard.SectionCokernelEulerCoefficientStatement
import Langlands.AlgebraicGeometry.Picard.IntegralAmpleSectionCokernelProof
import Langlands.Algebra.RationalPolynomialShiftDifference

/-! # Euler coefficient identity from an actual section exact sequence -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

local instance (X : Scheme.{u}) : (structureModule X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

local instance {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) :
    (tensorPow L.obj n).IsQuasicoherent :=
  (tensorPow_isLocallyFreeRankOne X L n).isQuasicoherent

local instance {X : Scheme.{u}} (L : LineBundle X) (n : ℕ) (s : L.powSections n) :
    (cokernel (sectionHom (tensorPow L.obj n) s)).IsQuasicoherent :=
  QuasicoherentLocal.isQuasicoherent_cokernel (sectionHom (tensorPow L.obj n) s)

/-- A generically generating section's cokernel gives the translation-difference
coefficient of the actual line-bundle Euler polynomial. -/
theorem sectionCokernelEulerCoefficient : SectionCokernelEulerCoefficientStatement.{u} := by
  intro K _ X _ _ _ f _ d hX L n s hs hQ hQsupport
  let O := structureModule X
  let Q := cokernel (sectionHom (tensorPow L.obj n) s)
  let hO : HasFiniteAffineSections O := hasFiniteAffineSections_structureSheaf X
  let hN : HasFiniteAffineSections (tensorPow L.obj n) :=
    hasFiniteAffineSections_lineBundle
      ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩
  let P := lineBundleEulerPolynomial f L (d + 1)
  let R := coherentEulerPolynomial f Q hQ L d
  have hP (m : ℕ) : P.eval (m : ℚ) = coherentEulerSequence f O hO L m :=
    coherentEulerPolynomial_eval f O hO L (d + 1)
      (HasSupportDimensionLT.of_topologicalKrullDim_le hX O) m
  have hR (m : ℕ) : R.eval (m : ℚ) = coherentEulerSequence f Q hQ L m :=
    coherentEulerPolynomial_eval f Q hQ L d hQsupport m
  have hshift (m : ℕ) :
      coherentEulerSequence f (tensorPow L.obj n) hN L m =
        coherentEulerSequence f O hO L (m + n) := by
    have hLm := tensorPow_isLocallyFreeRankOne X L m
    have hLmn := tensorPow_isLocallyFreeRankOne X L (m + n)
    have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
      (tensorPow L.obj n) (tensorPow L.obj m) hLm
    have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
      O (tensorPow L.obj (m + n)) hLmn
    change (coherentEulerCharacteristic f
      (tensorObj (tensorPow L.obj n) (tensorPow L.obj m)) _ : ℚ) =
        (coherentEulerCharacteristic f (tensorObj O (tensorPow L.obj (m + n))) _ : ℚ)
    exact congrArg (Int.cast : ℤ → ℚ) (coherentEulerCharacteristic_iso f
      (hN.tensor_lineBundle hLm) (hO.tensor_lineBundle hLmn)
      (tensorPowAddIso L.obj n m ≪≫
        eqToIso (congrArg (tensorPow L.obj) (Nat.add_comm n m)) ≪≫
        (tensorLeftUnitor (tensorPow L.obj (m + n))).symm))
  have hdiff (m : ℕ) :
      R.eval (m : ℚ) = P.eval ((m + n : ℕ) : ℚ) - P.eval (m : ℚ) := by
    let S := ShortComplex.cokernelSequence (sectionHom (tensorPow L.obj n) s)
    have : S.X₁.IsQuasicoherent := inferInstanceAs O.IsQuasicoherent
    have : S.X₂.IsQuasicoherent := inferInstanceAs (tensorPow L.obj n).IsQuasicoherent
    have : S.X₃.IsQuasicoherent := inferInstanceAs Q.IsQuasicoherent
    have hadd := congrFun (coherentEulerSequence_add f S
      (shortExact_sectionHom_cokernel _ s hs) hO hN hQ L) m
    change coherentEulerSequence f (tensorPow L.obj n) hN L m =
      coherentEulerSequence f O hO L m + coherentEulerSequence f Q hQ L m at hadd
    rw [hshift, ← hP, ← hP, ← hR] at hadd
    exact eq_sub_of_add_eq (by simpa only [add_comm] using hadd.symm)
  have heq : R = Langlands.Algebra.RationalPolynomial.shiftDifference P (n : ℚ) :=
    Langlands.Algebra.RationalPolynomial.eq_shiftDifference_of_eventually_nat_eval_eq
      P R n (Filter.Eventually.of_forall hdiff)
  change R.coeff d = ((d + 1 : ℕ) : ℚ) * (n : ℚ) * P.coeff (d + 1)
  rw [heq]
  exact Langlands.Algebra.RationalPolynomial.shiftDifference_coeff P (n : ℚ) d
    (lineBundleEulerPolynomial_natDegree_le f L (d + 1))

end Langlands.AlgebraicGeometry.Picard
