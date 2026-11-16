import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial
import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomialAdditivity
import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialProof
import Langlands.Algebra.RationalPolynomialShiftDifference

/-! # Actual mixed line-bundle Euler coefficients -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

local instance (X : Scheme.{u}) : (structureSheaf X).IsQuasicoherent :=
  (LineBundle.trivial X).property.isQuasicoherent

local instance {X : Scheme.{u}} (N : LineBundle X) : N.obj.IsQuasicoherent :=
  N.property.isQuasicoherent

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- The Euler polynomial of `N` twisted by powers of `L`, minus that of the
structure sheaf twisted by the same powers. Both use actual cohomology. -/
def mixedLineBundleEulerPolynomial (L N : LineBundle X) (d : ℕ) : Polynomial ℚ :=
  coherentEulerPolynomial f N.obj (hasFiniteAffineSections_lineBundle N) L d -
    lineBundleEulerPolynomial f L d

/-- The subleading mixed coefficient, at the specified dimension truncation.
At dimension zero the index is zero by natural subtraction. -/
def mixedLineBundleEulerCoefficient (L N : LineBundle X) (d : ℕ) : ℚ :=
  (mixedLineBundleEulerPolynomial f L N d).coeff (d - 1)

/-- A trivial coefficient bundle gives the zero difference polynomial. -/
@[simp] theorem mixedLineBundleEulerPolynomial_trivial (L : LineBundle X) (d : ℕ) :
    mixedLineBundleEulerPolynomial f L (LineBundle.trivial X) d = 0 := by
  simp only [mixedLineBundleEulerPolynomial, lineBundleEulerPolynomial,
    LineBundle.trivial, structureSheaf, sub_self]

/-- The mixed coefficient of the trivial bundle is zero, including dimension zero. -/
@[simp] theorem mixedLineBundleEulerCoefficient_trivial (L : LineBundle X) (d : ℕ) :
    mixedLineBundleEulerCoefficient f L (LineBundle.trivial X) d = 0 := by
  simp [mixedLineBundleEulerCoefficient]

/-- Changing the coefficient bundle by an actual isomorphism preserves its
mixed Euler polynomial. -/
theorem mixedLineBundleEulerPolynomial_iso (L M N : LineBundle X) (d : ℕ)
    (e : M.obj ≅ N.obj) :
    mixedLineBundleEulerPolynomial f L M d = mixedLineBundleEulerPolynomial f L N d := by
  unfold mixedLineBundleEulerPolynomial
  rw [coherentEulerPolynomial_iso f
    (hasFiniteAffineSections_lineBundle M) (hasFiniteAffineSections_lineBundle N) L d e]

/-- Under the dimension bound the difference polynomial evaluates to the
difference of the two actual twisted coherent Euler sequences. -/
theorem mixedLineBundleEulerPolynomial_eval [IsNoetherian X] [X.IsSeparated]
    (L N : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d) (n : ℕ) :
    (mixedLineBundleEulerPolynomial f L N d).eval (n : ℚ) =
      coherentEulerSequence f N.obj (hasFiniteAffineSections_lineBundle N) L n -
        coherentEulerSequence f (structureSheaf X)
          (hasFiniteAffineSections_structureSheaf X) L n := by
  simp only [mixedLineBundleEulerPolynomial, lineBundleEulerPolynomial, Polynomial.eval_sub,
    coherentEulerPolynomial_eval f _ _ L d
      (HasSupportDimensionLT.of_topologicalKrullDim_le hX _) n]

/-- Taking the coefficient bundle equal to `L` gives the unit translation
difference of the pure Euler polynomial. -/
theorem mixedLineBundleEulerPolynomial_self [IsNoetherian X] [X.IsSeparated]
    (L : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d) :
    mixedLineBundleEulerPolynomial f L L d =
      Langlands.Algebra.RationalPolynomial.shiftDifference
        (lineBundleEulerPolynomial f L d) 1 := by
  apply Langlands.Algebra.RationalPolynomial.eq_shiftDifference_of_eventually_nat_eval_eq
    (lineBundleEulerPolynomial f L d) (mixedLineBundleEulerPolynomial f L L d) 1
  apply Filter.Eventually.of_forall
  intro n
  rw [mixedLineBundleEulerPolynomial_eval f L L d hX]
  have hshift :
      coherentEulerSequence f L.obj (hasFiniteAffineSections_lineBundle L) L n =
        coherentEulerSequence f (structureSheaf X)
          (hasFiniteAffineSections_structureSheaf X) L (n + 1) := by
    have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle
      (structureSheaf X) L.obj L.property
    have heq := congrFun (coherentEulerSequence_iso f
      ((hasFiniteAffineSections_structureSheaf X).tensor_lineBundle L.property)
      (hasFiniteAffineSections_lineBundle L) L (tensorLeftUnitor L.obj)) n
    rw [← heq]
    exact coherentEulerSequence_shift f (structureSheaf X)
      (hasFiniteAffineSections_structureSheaf X) L n
  rw [hshift]
  simp only [lineBundleEulerPolynomial,
    coherentEulerPolynomial_eval f _ _ L d
      (HasSupportDimensionLT.of_topologicalKrullDim_le hX _) (n + 1),
    coherentEulerPolynomial_eval f _ _ L d
      (HasSupportDimensionLT.of_topologicalKrullDim_le hX _) n]

/-- The normalization of the mixed coefficient agrees with the derivative
normalization of the top pure Euler coefficient. -/
theorem mixedLineBundleEulerCoefficient_self [IsNoetherian X] [X.IsSeparated]
    (L : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d + 1) :
    mixedLineBundleEulerCoefficient f L L (d + 1) =
      ((d + 1 : ℕ) : ℚ) * (lineBundleEulerPolynomial f L (d + 1)).coeff (d + 1) := by
  unfold mixedLineBundleEulerCoefficient
  rw [mixedLineBundleEulerPolynomial_self f L (d + 1) hX]
  simpa only [Nat.add_sub_cancel, mul_one] using
    Langlands.Algebra.RationalPolynomial.shiftDifference_coeff
      (lineBundleEulerPolynomial f L (d + 1)) 1 d
      (lineBundleEulerPolynomial_natDegree_le f L (d + 1))

/-- The canonical pure Euler polynomial, rather than an existentially chosen
polynomial, has strictly positive top coefficient for an ample bundle. -/
theorem lineBundleEulerPolynomial_topCoeff_pos (g : ℕ)
    (hs : SmoothOfRelativeDimension g f) (hc : GeometricallyConnected f)
    (L : LineBundle X) (hL : L.IsAmple) :
    0 < (lineBundleEulerPolynomial f L g).coeff g := by
  let : SmoothOfRelativeDimension g f := hs
  let : Smooth f := SmoothOfRelativeDimension.smooth g f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let : X.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := f)).mp inferInstance
  obtain ⟨h, Q, hQ, _, hample⟩ :=
    smoothProperLineBundleEulerPolynomial K (Over.mk f) g hs
      (show IsProper f from inferInstance) hc L
  have hdim : topologicalKrullDim X ≤ g :=
    fieldSmoothTopologicalKrullDim K X f g hs inferInstance
  have heq : Q = lineBundleEulerPolynomial f L g := by
    apply Langlands.Algebra.RationalPolynomial.eq_of_eventually_nat_eval_eq
    apply Filter.Eventually.of_forall
    intro n
    exact (hQ n).trans (lineBundleEulerPolynomial_eval f L g hdim n (h n)).symm
  obtain ⟨hdeg, hpos⟩ := hample hL
  rw [Polynomial.leadingCoeff, hdeg, heq] at hpos
  exact hpos

end Langlands.AlgebraicGeometry.Picard
