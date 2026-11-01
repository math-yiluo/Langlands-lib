import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Mirabolic.MixedProducts

/-! # Equality transport for the second rank of left mixed and binary products -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Transport of the mirabolic input rank commutes with the actual left product. -/
theorem leftMixedProduct_rankCast (T : F.TopologicalData) (k : ℕ)
    {a b : ℕ} (h : a = b) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))).prod
        (mirabolicRankCast T h) ⋙ T.leftMixedProductFunctor k b =
      T.leftMixedProductFunctor k a ⋙ mirabolicRankCast T (congrArg (k + ·) h) := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

/-- Transport of the second GL input rank commutes with the actual binary product. -/
theorem binaryNormalizedProduct_rankCast_right (T : F.TopologicalData) (k : ℕ)
    {a b : ℕ} (h : a = b) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))).prod
        (generalLinearRankCast T h) ⋙ T.binaryNormalizedProductFunctor k b =
      T.binaryNormalizedProductFunctor k a ⋙ generalLinearRankCast T (congrArg (k + ·) h) := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

/-- Natural isomorphism form of left-product rank transport, in both variables. -/
def leftMixedProductRankCastIso (T : F.TopologicalData) (k : ℕ)
    {a b : ℕ} (h : a = b) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))).prod
        (mirabolicRankCast T h) ⋙ T.leftMixedProductFunctor k b ≅
      T.leftMixedProductFunctor k a ⋙ mirabolicRankCast T (congrArg (k + ·) h) :=
  letI := T.topology
  eqToIso (leftMixedProduct_rankCast T k h)

/-- Natural isomorphism form of binary-product rank transport, in both variables. -/
def binaryNormalizedProductRankCastRightIso (T : F.TopologicalData) (k : ℕ)
    {a b : ℕ} (h : a = b) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))).prod
        (generalLinearRankCast T h) ⋙ T.binaryNormalizedProductFunctor k b ≅
      T.binaryNormalizedProductFunctor k a ⋙ generalLinearRankCast T (congrArg (k + ·) h) :=
  letI := T.topology
  eqToIso (binaryNormalizedProduct_rankCast_right T k h)

end Langlands.Derivative
