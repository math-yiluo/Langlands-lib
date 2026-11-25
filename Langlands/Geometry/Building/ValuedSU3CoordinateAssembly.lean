import Langlands.Geometry.Building.ValuedRankOneCoordinateAssembly

/-! # Valued unitary rank-one coordinates on supplied apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

namespace RankOneCoordinateMatrices

variable {L : Type u} [Field L]

/-- The actual determinant-one unitary Weyl point. -/
def su3WeylPoint (c : SU3Root.RingInvolution L) : SU3Root.specialUnitarySubgroup c :=
  ⟨SU3Root.weylElement, SU3Root.weylElement_mem_specialUnitarySubgroup c⟩

@[simp] theorem su3WeylPoint_mul_self (c : SU3Root.RingInvolution L) :
    su3WeylPoint c * su3WeylPoint c = 1 :=
  Subtype.ext SU3Root.weylElement_mul_self

end RankOneCoordinateMatrices

namespace AlgebraicSU3RootCoordinates

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (Z : CentralizerDatum i) (hZ : IsTorus Z.Z) {b : characterLattice S}
  (C : AlgebraicSU3RootCoordinates (Z := Z.asTorus hZ) i Z.j Z.s b)

/-- The actual normalizer point induced by the unitary Weyl involution. -/
def weylNormalizer
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i) :
    normalizerPoints i :=
  ⟨C.rho (RankOneCoordinateMatrices.su3WeylPoint
    (SU3Root.fieldInvolution C.base C.extension)), hn⟩

/-- Explicit opposite factors transported through the common unitary homomorphism. -/
theorem opposite_factorization (p : SU3Root.rationalParameters C.base C.extension)
    (hp : p.second ≠ 0) :
    (C.negative.equiv (SU3Root.Parameters.leftOppositeParameter p hp) : rationalPoints G) *
        (C.positive.equiv p : rationalPoints G) *
        (C.negative.equiv (SU3Root.Parameters.rightOppositeParameter p hp) : rationalPoints G) =
      rationalPoints.map Z.j (C.corootPoint (Units.mk0 p.second hp)) *
        C.rho (RankOneCoordinateMatrices.su3WeylPoint
          (SU3Root.fieldInvolution C.base C.extension)) := by
  let c := SU3Root.fieldInvolution C.base C.extension
  have hm :
      (⟨SU3Root.oppositeEmbedding c (SU3Root.Parameters.leftOppositeParameter p hp),
        SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c _⟩ :
          SU3Root.specialUnitarySubgroup c) *
      ⟨SU3Root.Parameters.embedding c p, SU3Root.embedding_mem_specialUnitarySubgroup c p⟩ *
      ⟨SU3Root.oppositeEmbedding c (SU3Root.Parameters.rightOppositeParameter p hp),
        SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c _⟩ =
      ⟨SU3Root.diagonal c (Units.mk0 p.second hp),
        SU3Root.diagonal_mem_specialUnitarySubgroup c _⟩ *
      RankOneCoordinateMatrices.su3WeylPoint c :=
    Subtype.ext (SU3Root.opposite_factorization p hp)
  have hr := congrArg C.rho hm
  dsimp only [c] at hr
  simpa only [map_mul, C.rho_upper, C.rho_lower, C.map_corootPoint] using hr

/-- The explicit factors form an actual normalizing opposite pair. -/
theorem opposite_factor_pair
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i)
    (p : SU3Root.rationalParameters C.base C.extension) (hp : p.second ≠ 0) :
    RelativeRoot.IsOppositeFactorPair i b (C.positive.equiv p)
      ((C.negative.equiv (SU3Root.Parameters.leftOppositeParameter p hp) : rationalPoints G),
       (C.negative.equiv (SU3Root.Parameters.rightOppositeParameter p hp) : rationalPoints G)) := by
  refine ⟨(C.negative.equiv _).property, (C.negative.equiv _).property, ?_⟩
  change _ ∈ normalizerPoints i
  rw [C.opposite_factorization Z hZ p hp]
  exact (normalizerPoints i).mul_mem (Z.toNormalizer (C.corootPoint _)).property hn

/-- The unitary Weyl point is an involution in the actual normalizer. -/
theorem weylNormalizer_mul_self
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i) :
    C.weylNormalizer Z hZ hn * C.weylNormalizer Z hZ hn = 1 := by
  apply Subtype.ext
  change C.rho _ * C.rho _ = 1
  rw [← map_mul, RankOneCoordinateMatrices.su3WeylPoint_mul_self, map_one]

variable {v : Valuation k (WithZero (Multiplicative ℤ))}
  (A : KPApartmentData i (IntegerValuation.order v))

/-- A common apartment origin fixed by the unitary Weyl image. -/
def coordinateOrigin
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i) :
    A.Apartment :=
  A.normalizerMidpoint (C.weylNormalizer Z hZ hn) (Classical.choice inferInstance)

/-- The chosen unitary coordinate origin is fixed by the Weyl image. -/
theorem weylNormalizer_smul_coordinateOrigin
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i) :
    C.weylNormalizer Z hZ hn • C.coordinateOrigin Z hZ A hn =
      C.coordinateOrigin Z hZ A hn := by
  apply A.smul_normalizerMidpoint_eq_self
  rw [← mul_smul, C.weylNormalizer_mul_self, one_smul]

/-- The actual pair representative factors in the normalizer through the coroot. -/
theorem opposite_factor_pair_normalizer
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i)
    (p : SU3Root.rationalParameters C.base C.extension) (hp : p.second ≠ 0) :
    (⟨(C.negative.equiv (SU3Root.Parameters.leftOppositeParameter p hp) : rationalPoints G) *
        (C.positive.equiv p : rationalPoints G) *
        (C.negative.equiv (SU3Root.Parameters.rightOppositeParameter p hp) : rationalPoints G),
      (C.opposite_factor_pair Z hZ hn p hp).2.2⟩ : normalizerPoints i) =
      Z.toNormalizer (C.corootPoint (Units.mk0 p.second hp)) *
        C.weylNormalizer Z hZ hn :=
  Subtype.ext (C.opposite_factorization Z hZ p hp)

/-- The common Weyl point negates the unitary root character. -/
theorem weylNormalizer_root
    (hS : IsSplitTorus S.toGrp) (hb : b ≠ 0)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i) :
    weylAction i (C.weylNormalizer Z hZ hn) b = -b := by
  let p := SU3Root.rationalLift C.base C.extension (1 : C.extension)
  have hp1 : p ≠ 1 := by
    intro h
    have hh := congrArg SU3Root.Parameters.first h
    exact one_ne_zero (by
      simpa only [p, SU3Root.rationalLift_first, SU3Root.Parameters.first_one] using hh)
  have hp : p.second ≠ 0 := fun h => hp1 ((SU3Root.Parameters.second_eq_zero_iff p).mp h)
  have hu1 : (C.positive.equiv p : rationalPoints G) ≠ 1 := by
    intro h
    have hh : C.positive.equiv p = C.positive.equiv 1 :=
      Subtype.ext (by simpa only [map_one, OneMemClass.coe_one] using h)
    exact hp1 (C.positive.equiv.injective hh)
  have hw := (C.opposite_factor_pair Z hZ hn p hp).weylAction_eq_neg i hS hb
    (C.positive.equiv _).property hu1
  rw [C.opposite_factor_pair_normalizer Z hZ hn p hp, map_mul,
    weylAction_centralizerToNormalizer Z.isRepresentedBy, one_mul] at hw
  exact hw

/-- Norm calibration forces the exact upper unitary depth at any Weyl-fixed point. -/
theorem val_positive_of_fixed [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (hbar : ∀ t, w ((SU3Root.fieldInvolution C.base C.extension).bar t) = w t)
    (x : A.Apartment) (hx : C.weylNormalizer Z hZ hn • x = x)
    (p : SU3Root.rationalParameters C.base C.extension) :
    x.val b (C.positive.equiv p) = SU3Root.Parameters.depthA w p := by
  by_cases hp : p.second = 0
  · have hp1 := (SU3Root.Parameters.second_eq_zero_iff p).mp hp
    subst p
    simpa only [map_one, OneMemClass.coe_one, SU3Root.Parameters.depthA,
      SU3Root.Parameters.second_one, w.map_zero, SU3Root.halfTop_top] using
      (x.isValuation.eq_top_iff b hb 1 (Subgroup.one_mem _)).2 rfl
  have hu1 : (C.positive.equiv p : rationalPoints G) ≠ 1 := by
    intro h
    have hh : C.positive.equiv p = C.positive.equiv 1 :=
      Subtype.ext (by simpa only [map_one, OneMemClass.coe_one] using h)
    exact hp ((SU3Root.Parameters.second_eq_zero_iff p).mpr (C.positive.equiv.injective hh))
  have hd := A.val_eq_half_centralizer_of_pair Z hA hG hi
    (a := ⟨b, hb⟩) (C.positive.equiv p).property hu1
    (C.opposite_factor_pair Z hZ hn p hp) x (C.weylNormalizer Z hZ hn) hx
    (C.corootPoint (Units.mk0 p.second hp))
    (C.opposite_factor_pair_normalizer Z hZ hn p hp)
  have hc := C.eval_corootPoint Z.bijective hw hbar (Units.mk0 p.second hp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (mt (w.top_iff).mp hp)
  simp only [Units.val_mk0, ← hr, WithTop.coe_inj] at hc
  rw [hd, SU3Root.Parameters.depthA, ← hr, SU3Root.halfTop_coe, WithTop.coe_inj]
  change eval S b _ / 2 = r / 2
  rw [hc]

/-- The lower unitary coordinate has the same depth at a common Weyl-fixed point. -/
theorem val_negative_of_fixed [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (hbar : ∀ t, w ((SU3Root.fieldInvolution C.base C.extension).bar t) = w t)
    (x : A.Apartment) (hx : C.weylNormalizer Z hZ hn • x = x)
    (p : SU3Root.rationalParameters C.base C.extension) :
    x.val (-b) (C.negative.equiv p) = SU3Root.Parameters.depthA w p := by
  let c := SU3Root.fieldInvolution C.base C.extension
  let n := C.weylNormalizer Z hZ hn
  have hwroot := C.weylNormalizer_root Z hZ hi.1.1 hb.1 hn
  have hwinv : weylAction i n⁻¹ (-b) = b := by
    rw [← hwroot, map_inv]
    exact (weylAction i n).symm_apply_apply b
  have hm :
      (RankOneCoordinateMatrices.su3WeylPoint c)⁻¹ *
        ⟨SU3Root.oppositeEmbedding c p,
          SU3Root.oppositeEmbedding_mem_specialUnitarySubgroup c p⟩ *
        RankOneCoordinateMatrices.su3WeylPoint c =
      (⟨SU3Root.Parameters.embedding c p,
        SU3Root.embedding_mem_specialUnitarySubgroup c p⟩ :
          SU3Root.specialUnitarySubgroup c) := by
    apply Subtype.ext
    change SU3Root.weylElement⁻¹ * SU3Root.oppositeEmbedding c p *
      SU3Root.weylElement = SU3Root.Parameters.embedding c p
    simp only [SU3Root.oppositeEmbedding, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one]
  have hc := congrArg C.rho hm
  dsimp only [c] at hc
  simp only [map_mul, map_inv, C.rho_upper, C.rho_lower] at hc
  have hconj : (n : rationalPoints G)⁻¹ *
      (C.negative.equiv p : rationalPoints G) * n =
        (C.positive.equiv p : rationalPoints G) := hc
  dsimp only [n] at hwinv hconj
  have hval := congrArg
    (fun y : A.Apartment => y.val (-b) (C.negative.equiv p)) hx
  simp only [KPApartmentData.val_smul, RootFunctionFamily.smul_apply, hwinv, hconj] at hval
  exact hval.symm.trans (C.val_positive_of_fixed Z hZ A hA hG hi hb hn hw hbar x hx p)

/-- The constructed origin realizes both opposite unitary coordinate depths. -/
theorem coordinateOrigin_depths [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (hbar : ∀ t, w ((SU3Root.fieldInvolution C.base C.extension).bar t) = w t) :
    (∀ p, (C.coordinateOrigin Z hZ A hn).val b (C.positive.equiv p) =
      SU3Root.Parameters.depthA w p) ∧
    (∀ p, (C.coordinateOrigin Z hZ A hn).val (-b) (C.negative.equiv p) =
      SU3Root.Parameters.depthA w p) := by
  have hx := C.weylNormalizer_smul_coordinateOrigin Z hZ A hn
  exact ⟨C.val_positive_of_fixed Z hZ A hA hG hi hb hn hw hbar _ hx,
    C.val_negative_of_fixed Z hZ A hA hG hi hb hn hw hbar _ hx⟩

/-- V4 gives both doubled-root depths at the same constructed origin. -/
theorem coordinateOrigin_double_depths [IsAffine S.toGrp.X.left] [IsAffine Z.Z.X.left]
    (hA : IntegerValuation.IsOmegaCompatible v A Z)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hb : b ∈ relativeRoots i) (h2b : 2 • b ∈ relativeRoots i)
    (hn : C.rho (RankOneCoordinateMatrices.su3WeylPoint
      (SU3Root.fieldInvolution C.base C.extension)) ∈ normalizerPoints i)
    {w : AddValuation C.extension (WithTop ℝ)}
    (hw : IntegerValuation.IsNormCalibrated v w)
    (hbar : ∀ t, w ((SU3Root.fieldInvolution C.base C.extension).bar t) = w t) :
    (∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution C.base C.extension),
      (C.coordinateOrigin Z hZ A hn).val (2 • b) (C.positive.equiv q.val) =
        SU3Root.Parameters.depthDouble w q) ∧
    (∀ q : SU3Root.Parameters.central (SU3Root.fieldInvolution C.base C.extension),
      (C.coordinateOrigin Z hZ A hn).val (2 • (-b)) (C.negative.equiv q.val) =
        SU3Root.Parameters.depthDouble w q) := by
  let x := C.coordinateOrigin Z hZ A hn
  obtain ⟨hp, hm⟩ := C.coordinateOrigin_depths Z hZ A hA hG hi hb hn hw hbar
  have hdouble (a : characterLattice S) (ha : a ∈ relativeRoots i)
      (h2a : 2 • a ∈ relativeRoots i)
      (R : RootUnitaryCoordinatesOn i Z.j Z.s a C.base C.extension)
      (hd : ∀ p, x.val a (R.equiv p) = SU3Root.Parameters.depthA w p)
      (q : SU3Root.Parameters.central (SU3Root.fieldInvolution C.base C.extension)) :
      x.val (2 • a) (R.equiv q.val) = SU3Root.Parameters.depthDouble w q := by
    rw [x.isValuation.double a ha h2a _ ((R.double _).mpr ⟨q.val, q.property, rfl⟩),
      hd, SU3Root.Parameters.depthDouble_eq_double_depthA]
    cases h : SU3Root.Parameters.depthA w q.val using WithTop.recTopCoe with
    | top => simp only [two_nsmul, WithTop.top_add, SU3Root.doubleTop_top]
    | coe t =>
      simp only [two_nsmul, ← WithTop.coe_add, SU3Root.doubleTop_coe]
      congr 1
      ring
  have hnroot := C.weylNormalizer_root Z hZ hi.1.1 hb.1 hn
  have hmb : -b ∈ relativeRoots i := by
    rw [← hnroot]
    exact weylAction_mapsTo_relativeRoots i (C.weylNormalizer Z hZ hn) hb
  have hm2b : 2 • (-b) ∈ relativeRoots i := by
    have hh := weylAction_mapsTo_relativeRoots i (C.weylNormalizer Z hZ hn) h2b
    have hsm : ∀ (e : characterLattice S ≃ₗ[ℤ] characterLattice S) (y : characterLattice S),
        e (2 • y) = 2 • e y := fun e y => e.toLinearMap.toAddMonoidHom.map_nsmul 2 y
    simpa only [hsm, hnroot] using hh
  exact ⟨hdouble b hb h2b C.positive hp, hdouble (-b) hmb hm2b C.negative hm⟩

end AlgebraicSU3RootCoordinates

end Langlands.Geometry.Building
