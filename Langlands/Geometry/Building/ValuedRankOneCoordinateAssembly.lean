import Langlands.Geometry.Building.AlgebraicRankOneCoordinateCalibration
import Langlands.Geometry.Building.RankOneCoordinateOriginComparison
import Langlands.GroupScheme.SpecialLinearBinaryRadicalGeneration
import Langlands.GroupScheme.Rational.RootFactorPairConsequences

/-! # Valued rank-one coordinates on supplied apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

namespace RankOneCoordinateMatrices

variable {E : Type u} [Field E]

/-- The square of the standard SL2 Weyl element is the diagonal at minus one. -/
theorem sl2_weyl_mul_self :
    (SpecialLinear.BinaryUpper.weylMatrix (A := E)) *
        SpecialLinear.BinaryUpper.weylMatrix =
      SpecialLinear.Root.contractingMatrix (by decide : (0 : Fin 2) ≠ 1) (-1) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [SpecialLinear.BinaryUpper.weylMatrix, SpecialLinear.Root.contractingMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The two lower factors for a nonzero upper parameter. -/
theorem sl2_opposite_factors (t : E) (ht : t ≠ 0) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (-t⁻¹) *
        Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t *
        Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (-t⁻¹) =
      SpecialLinear.Root.contractingMatrix (by decide : (0 : Fin 2) ≠ 1)
        (-Units.mk0 t ht) * SpecialLinear.BinaryUpper.weylMatrix := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [SpecialLinear.BinaryUpper.weylMatrix, SpecialLinear.Root.contractingMatrix,
      Matrix.SpecialLinearGroup.transvection, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, Matrix.mul_apply, Fin.sum_univ_two, ht]

end RankOneCoordinateMatrices

namespace CentralizerDatum

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}

/-- The represented centralizer, viewed as commutative when it is a torus. -/
abbrev asTorus (Z : CentralizerDatum i) (hZ : IsTorus Z.Z) :
    CommGroupScheme (Spec (CommRingCat.of k)) where
  toGrp := Z.Z
  comm := hZ.isCommMonObj

end CentralizerDatum

namespace IntegerValuation.IsOmegaCompatible

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {A : KPApartmentData i (IntegerValuation.order v)} {Z : CentralizerDatum i}

/-- A centralizer point of order dividing two has zero apartment translation. -/
theorem smul_eq_self_of_mul_self (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (z : rationalPoints Z.Z) (hz : z * z = 1) (x : A.Apartment) :
    Z.toNormalizer z • x = x := by
  have hzv := congrArg (fun q => (IntegerValuation.centralizerTranslation v Z.s Z.bijective q).toAdd) hz
  simp only [map_mul, map_one, toAdd_mul, toAdd_one] at hzv
  have hzero : (IntegerValuation.centralizerTranslation v Z.s Z.bijective z).toAdd = 0 := by
    have htwo : (2 : ℝ) •
        (IntegerValuation.centralizerTranslation v Z.s Z.bijective z).toAdd = 0 := by
      simpa only [two_smul] using hzv
    have hhalf := congrArg (fun q : V S => (1 / 2 : ℝ) • q) htwo
    simpa only [smul_smul, one_div_mul_cancel (by norm_num : (2 : ℝ) ≠ 0),
      one_smul, smul_zero] using hhalf
  rw [hA.smul_eq_vadd, hzero, Submodule.Quotient.mk_zero, zero_vadd]

end IntegerValuation.IsOmegaCompatible


namespace AlgebraicSL2RootCoordinates

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (Z : CentralizerDatum i) (hZ : IsTorus Z.Z) {b : characterLattice S}
  (C : AlgebraicSL2RootCoordinates (Z := Z.asTorus hZ) i Z.j Z.s b)

/-- The actual normalizer point induced by the standard Weyl matrix. -/
def weylNormalizer
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i) :
    normalizerPoints i :=
  ⟨C.rho SpecialLinear.BinaryUpper.weylMatrix, hn⟩

/-- Explicit opposite factors transported through the common rank-one homomorphism. -/
theorem opposite_factorization (t : C.extension) (ht : t ≠ 0) :
    (C.negative.equiv (Multiplicative.ofAdd (-t⁻¹)) : rationalPoints G) *
        (C.positive.equiv (Multiplicative.ofAdd t) : rationalPoints G) *
        (C.negative.equiv (Multiplicative.ofAdd (-t⁻¹)) : rationalPoints G) =
      rationalPoints.map Z.j (C.corootPoint (-Units.mk0 t ht)) *
        C.rho SpecialLinear.BinaryUpper.weylMatrix := by
  have h := congrArg C.rho (RankOneCoordinateMatrices.sl2_opposite_factors t ht)
  simpa only [map_mul, C.rho_upper, C.rho_lower, C.map_corootPoint] using h

/-- The explicit factors form an actual normalizing opposite pair. -/
theorem opposite_factor_pair
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i)
    (t : C.extension) (ht : t ≠ 0) :
    RelativeRoot.IsOppositeFactorPair i b
      (C.positive.equiv (Multiplicative.ofAdd t))
      ((C.negative.equiv (Multiplicative.ofAdd (-t⁻¹)) : rationalPoints G),
       (C.negative.equiv (Multiplicative.ofAdd (-t⁻¹)) : rationalPoints G)) := by
  refine ⟨(C.negative.equiv _).property, (C.negative.equiv _).property, ?_⟩
  change _ ∈ normalizerPoints i
  rw [C.opposite_factorization Z hZ t ht]
  exact (normalizerPoints i).mul_mem (Z.toNormalizer (C.corootPoint _)).property hn

/-- The square of the Weyl point is the centralizer coroot at minus one. -/
theorem weylNormalizer_mul_self
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i) :
    C.weylNormalizer Z hZ hn * C.weylNormalizer Z hZ hn =
      Z.toNormalizer (C.corootPoint (-1)) := by
  apply Subtype.ext
  change C.rho _ * C.rho _ = rationalPoints.map Z.j (C.corootPoint (-1))
  rw [← map_mul, RankOneCoordinateMatrices.sl2_weyl_mul_self, C.map_corootPoint]

/-- The coroot at minus one has order dividing two. -/
theorem corootPoint_neg_one_mul_self :
    C.corootPoint (-1) * C.corootPoint (-1) = 1 := by
  rw [← map_mul]
  simp

variable {v : Valuation k (WithZero (Multiplicative ℤ))}
  (A : KPApartmentData i (IntegerValuation.order v))

/-- A common apartment origin fixed by the standard Weyl image. -/
def coordinateOrigin
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i) :
    A.Apartment :=
  A.normalizerMidpoint (C.weylNormalizer Z hZ hn) (Classical.choice inferInstance)

/-- Full centralizer compatibility makes the chosen common origin Weyl fixed. -/
theorem weylNormalizer_smul_coordinateOrigin
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i) :
    C.weylNormalizer Z hZ hn • C.coordinateOrigin Z hZ A hn =
      C.coordinateOrigin Z hZ A hn := by
  apply A.smul_normalizerMidpoint_eq_self
  rw [← mul_smul, C.weylNormalizer_mul_self]
  exact hA.smul_eq_self_of_mul_self _ (C.corootPoint_neg_one_mul_self Z hZ) _


/-- The explicit pair representative factors in the normalizer through the coroot. -/
theorem opposite_factor_pair_normalizer
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i)
    (t : C.extension) (ht : t ≠ 0) :
    (⟨(C.negative.equiv (Multiplicative.ofAdd (-t⁻¹)) : rationalPoints G) *
        (C.positive.equiv (Multiplicative.ofAdd t) : rationalPoints G) *
        (C.negative.equiv (Multiplicative.ofAdd (-t⁻¹)) : rationalPoints G),
      (C.opposite_factor_pair Z hZ hn t ht).2.2⟩ : normalizerPoints i) =
      Z.toNormalizer (C.corootPoint (-Units.mk0 t ht)) *
        C.weylNormalizer Z hZ hn :=
  Subtype.ext (C.opposite_factorization Z hZ t ht)

/-- The common Weyl point negates the root character. -/
theorem weylNormalizer_root
    (hS : IsSplitTorus S.toGrp) (hb : b ≠ 0)
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i) :
    weylAction i (C.weylNormalizer Z hZ hn) b = -b := by
  have hu1 : (C.positive.equiv (Multiplicative.ofAdd (1 : C.extension)) :
      rationalPoints G) ≠ 1 := by
    intro h
    have hh : C.positive.equiv (Multiplicative.ofAdd (1 : C.extension)) =
        C.positive.equiv 1 := Subtype.ext (by simpa only [map_one, OneMemClass.coe_one] using h)
    have ht := congrArg Multiplicative.toAdd (C.positive.equiv.injective hh)
    exact one_ne_zero ht
  have hw := (C.opposite_factor_pair Z hZ hn 1 one_ne_zero).weylAction_eq_neg i hS hb
    (C.positive.equiv _).property hu1
  rw [C.opposite_factor_pair_normalizer Z hZ hn 1 one_ne_zero, map_mul,
    weylAction_centralizerToNormalizer Z.isRepresentedBy, one_mul] at hw
  exact hw

/-- Norm calibration forces the exact upper-coordinate depth at any Weyl-fixed point. -/
theorem val_positive_of_fixed [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (x : A.Apartment) (hx : C.weylNormalizer Z hZ hn • x = x) (t : C.extension) :
    x.val b (C.positive.equiv (Multiplicative.ofAdd t)) = w t := by
  by_cases ht : t = 0
  · subst t
    simpa only [ofAdd_zero, map_one, OneMemClass.coe_one, w.map_zero] using
      (x.isValuation.eq_top_iff b hb 1 (Subgroup.one_mem _)).2 rfl
  have hu1 : (C.positive.equiv (Multiplicative.ofAdd t) : rationalPoints G) ≠ 1 := by
    intro h
    have hh : C.positive.equiv (Multiplicative.ofAdd t) = C.positive.equiv 1 :=
      Subtype.ext (by simpa only [map_one, OneMemClass.coe_one] using h)
    exact ht (congrArg Multiplicative.toAdd (C.positive.equiv.injective hh))
  have hd := A.val_eq_half_centralizer_of_pair Z hA hG hi
    (a := ⟨b, hb⟩) (C.positive.equiv _).property hu1
    (C.opposite_factor_pair Z hZ hn t ht) x (C.weylNormalizer Z hZ hn) hx
    (C.corootPoint (-Units.mk0 t ht)) (C.opposite_factor_pair_normalizer Z hZ hn t ht)
  have hc := C.eval_corootPoint Z.bijective hw (-Units.mk0 t ht)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (mt (w.top_iff).mp ht)
  simp only [Units.val_neg, Units.val_mk0, w.map_neg, ← hr, two_smul,
    ← WithTop.coe_add, WithTop.coe_inj] at hc
  rw [hd, ← hr, WithTop.coe_inj]
  change eval S b _ / 2 = r
  linarith


/-- The lower-coordinate depth agrees with the same valuation at a Weyl-fixed point. -/
theorem val_negative_of_fixed [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (x : A.Apartment) (hx : C.weylNormalizer Z hZ hn • x = x) (t : C.extension) :
    x.val (-b) (C.negative.equiv (Multiplicative.ofAdd t)) = w t := by
  let n := C.weylNormalizer Z hZ hn
  have hwroot := C.weylNormalizer_root Z hZ hi.1.1 hb.1 hn
  have hwinv : weylAction i n⁻¹ (-b) = b := by
    rw [← hwroot, map_inv]
    exact (weylAction i n).symm_apply_apply b
  have hc := congrArg C.rho
    (SpecialLinear.BinaryRoot.weylMatrix_conjugate_upper C.extension (-t))
  simp only [map_mul, map_inv, C.rho_upper, C.rho_lower, neg_neg] at hc
  have hconj : (n : rationalPoints G)⁻¹ *
      (C.negative.equiv (Multiplicative.ofAdd t) : rationalPoints G) * n =
        (C.positive.equiv (Multiplicative.ofAdd (-t)) : rationalPoints G) := by
    change (C.rho SpecialLinear.BinaryUpper.weylMatrix)⁻¹ * _ *
      C.rho SpecialLinear.BinaryUpper.weylMatrix = _
    rw [← hc]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  dsimp only [n] at hwinv hconj
  have hval := congrArg
    (fun y : A.Apartment => y.val (-b) (C.negative.equiv (Multiplicative.ofAdd t))) hx
  simp only [KPApartmentData.val_smul, RootFunctionFamily.smul_apply, hwinv, hconj] at hval
  calc
    x.val (-b) (C.negative.equiv (Multiplicative.ofAdd t)) =
        x.val b (C.positive.equiv (Multiplicative.ofAdd (-t))) := hval.symm
    _ = w t := (C.val_positive_of_fixed Z hZ A hA hG hi hb hn hw x hx (-t)).trans
      (w.map_neg t)

/-- The constructed origin realizes both opposite field-coordinate depths. -/
theorem coordinateOrigin_depths [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w) :
    (∀ t, (C.coordinateOrigin Z hZ A hn).val b
      (C.positive.equiv (Multiplicative.ofAdd t)) = w t) ∧
    (∀ t, (C.coordinateOrigin Z hZ A hn).val (-b)
      (C.negative.equiv (Multiplicative.ofAdd t)) = w t) := by
  have hx := C.weylNormalizer_smul_coordinateOrigin Z hZ A hA hn
  exact ⟨C.val_positive_of_fixed Z hZ A hA hG hi hb hn hw _ hx,
    C.val_negative_of_fixed Z hZ A hA hG hi hb hn hw _ hx⟩

end AlgebraicSL2RootCoordinates

end Langlands.Geometry.Building
