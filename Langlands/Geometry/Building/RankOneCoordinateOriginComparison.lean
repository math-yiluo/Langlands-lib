import Langlands.Geometry.Building.IntegerOmegaApartmentRigidity
import Langlands.Geometry.Building.CentralizerCoordinateCompatibility
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-! # Rank-one coordinate depths from centralizer displacements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The midpoint of a point and its normalizer image, used as a candidate
origin for rank-one coordinates. -/
def normalizerMidpoint (n : normalizerPoints i) (x : D.Apartment) : D.Apartment :=
  midpoint ℝ x (n • x)

/-- An affine normalizer action whose square fixes a point fixes the midpoint
of that point and its image. -/
theorem smul_midpoint_eq_self_of_square (n : normalizerPoints i) (x : D.Apartment)
    (hn : n • (n • x) = x) :
    n • midpoint ℝ x (n • x) = midpoint ℝ x (n • x) := by
  have h := (D.normalizerAffineEquiv n).map_midpoint x (n • x)
  simp only [normalizerAffineEquiv_apply, hn] at h
  exact h.trans (midpoint_comm _ _)

/-- A normalizer whose square fixes the input point fixes the constructed origin. -/
theorem smul_normalizerMidpoint_eq_self (n : normalizerPoints i) (x : D.Apartment)
    (hn : n • (n • x) = x) :
    n • D.normalizerMidpoint n x = D.normalizerMidpoint n x :=
  D.smul_midpoint_eq_self_of_square n x hn

variable {v : Valuation k (WithZero (Multiplicative ℤ))}
  (A : KPApartmentData i (IntegerValuation.order v)) (C : CentralizerDatum i)
  (hA : IntegerValuation.IsOmegaCompatible v A C)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hA hG hi in
/-- If an actual opposite-pair representative is a centralizer point times
a normalizer fixing the chosen origin, its root value is half the positive
centralizer valuation. -/
theorem val_eq_half_centralizer_of_pair
    {a : relativeRoots i} {u : rationalPoints G}
    (hu : u ∈ rootGroupPoints i a) (hu1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (a : characterLattice S) u p)
    (x : A.Apartment) (n : normalizerPoints i) (hn : n • x = x)
    (z : rationalPoints C.Z)
    (hm : (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) = C.toNormalizer z * n) :
    x.val a u =
      ((eval S a (IntegerValuation.centralizerValuation v C.s C.bijective z).toAdd / 2 :
        ℝ) : WithTop ℝ) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
    (mt (x.isValuation.eq_top_iff a a.property u hu).1 hu1)
  have hdepth := A.rootForm_oppositeFactorPair_vsub hG hi hu hu1 hp x ht.symm
  rw [hm, mul_smul, hn, hA.smul_eq_vadd, vadd_vsub, rootForm_mk,
    IntegerValuation.centralizerTranslation_toAdd, map_neg] at hdepth
  rw [← ht, WithTop.coe_inj]
  linarith

end Langlands.Geometry.Building.KPApartmentData
