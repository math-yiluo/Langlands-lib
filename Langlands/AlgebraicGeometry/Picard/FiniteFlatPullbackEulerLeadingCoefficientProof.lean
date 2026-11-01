import Langlands.AlgebraicGeometry.Picard.FiniteFlatPullbackEulerLeadingCoefficientStatement
import Langlands.AlgebraicGeometry.Picard.FiniteFlatEulerPolynomialCoefficientProof
import Langlands.AlgebraicGeometry.Picard.SmoothProperLineBundleEulerPolynomialProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedFiniteFlatGeometryProof

/-! # Leading Euler coefficients under native finite-flat pullback -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Exact source degree turns the actual native-rank comparison into the
leading-coefficient formula on a smooth proper geometrically connected scheme. -/
theorem smoothProperFiniteFlat_eulerPolynomial_leadingCoeff
    (K : Type u) [Field K] (X : Over (Spec (CommRingCat.of K))) (g : ℕ)
    (hs : SmoothOfRelativeDimension g X.hom) (hp : IsProper X.hom)
    (hc : GeometricallyConnected X.hom) (f : X ⟶ X)
    (hf : IsFinite f.left) (hflat : Flat f.left) (L : LineBundle X.left)
    (hL : ∀ n, HasFiniteCohomology X.hom (tensorPow L.obj n))
    (hF : ∀ n, HasFiniteCohomology X.hom
      (tensorPow ((Scheme.Modules.pullback f.left).obj L.obj) n))
    (P Q : Polynomial ℚ)
    (hP : ∀ n : ℕ, P.eval (n : ℚ) =
      (eulerCharacteristic X.hom (tensorPow L.obj n) (hL n) : ℚ))
    (hQ : ∀ n : ℕ, Q.eval (n : ℚ) = (eulerCharacteristic X.hom
      (tensorPow ((Scheme.Modules.pullback f.left).obj L.obj) n) (hF n) : ℚ))
    (hPn : P ≠ 0) (hPd : P.natDegree = g) (x : X.left) :
    Q.natDegree = g ∧ Q.leadingCoeff = (f.left.finrank x : ℚ) * P.leadingCoeff := by
  let : SmoothOfRelativeDimension g X.hom := hs
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth g X.hom
  let : IsProper X.hom := hp
  let : IsFinite f.left := hf
  let : Flat f.left := hflat
  obtain ⟨hi, hdim, _, _, hr⟩ :=
    Langlands.AlgebraicGeometry.smoothProperConnectedFiniteFlatGeometry
      K X g hs hp hc f hf hflat
  let : IsIntegral X.left := hi
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  let : IsNoetherian X.left := ⟨⟩
  let : X.left.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := X.hom)).mp inferInstance
  have hF' : ∀ n, HasFiniteCohomology (f.left ≫ X.hom)
      (tensorPow ((Scheme.Modules.pullback f.left).obj L.obj) n) := by
    simpa only [f.w] using hF
  have he := finiteFlat_topEulerDifference_eq_zero X.hom f.left g hdim.le L hL hF' x
  have hdiff : (fwdDiff 1)^[g]
      ((fun n : ℕ => Q.eval (n : ℚ)) -
        fun n : ℕ => (f.left.finrank x : ℚ) * P.eval (n : ℚ)) = 0 := by
    simpa only [f.w, ← hP, ← hQ] using he
  exact Langlands.Algebra.RationalPolynomial.natDegree_leadingCoeff_of_iterate_fwdDiff_sub_eq_zero
    P Q (f.left.finrank x : ℚ) g hPn hPd
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hr x))) hdiff

/-- Finite flat pullback multiplies the leading coefficient of an actual
ample line-bundle Euler polynomial by the native rank at every target point. -/
theorem finiteFlatPullbackEulerLeadingCoefficient :
    FiniteFlatPullbackEulerLeadingCoefficientStatement.{u} := by
  intro K _ X g hs hp hc f hf hflat L hample hL hF P Q hP hQ x
  obtain ⟨hA, A, hAeval, _, hAample⟩ := smoothProperLineBundleEulerPolynomial K X g hs hp hc L
  obtain ⟨hAd, hAc⟩ := hAample hample
  have hPA : P = A := Langlands.Algebra.RationalPolynomial.eq_of_eventually_nat_eval_eq
    P A (Filter.Eventually.of_forall (fun n => by rw [hP n, hAeval n]))
  have hPn : P ≠ 0 := by
    rw [hPA]
    exact Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hAc)
  have hPd : P.natDegree = g := by rw [hPA]; exact hAd
  exact (smoothProperFiniteFlat_eulerPolynomial_leadingCoeff K X g hs hp hc f hf hflat
    L hL hF P Q hP hQ hPn hPd x).2

end Langlands.AlgebraicGeometry.Picard
