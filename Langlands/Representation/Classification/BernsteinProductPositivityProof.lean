import Langlands.Representation.Classification.BernsteinProductPositivityStatement
import Langlands.Representation.Derivative.BinaryDerivativeSupportAggregation
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.SupercuspidalSupportTwist
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.ScalarSubReduction
import Langlands.Representation.Smooth.ConstituentSupport
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTwist
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary

/-! # Positivity of binary products with unitary top shifted derivatives -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis

universe uF uV uG uC

namespace BernsteinProductPositivity

section Scalar

variable {G : Type uG} [Group G] [TopologicalSpace G] {C : Type uC} [Group C]

/-- A scalar character of a smooth representation is inherited by each of its
actual subquotients. -/
theorem hasScalarCharacter_of_isSubquotient {D X : SmoothRep.{0, uG, uV} ℂ G}
    {z : C →* G} {ω : C →* ℂˣ} (h : SmoothRep.IsSubquotient D X)
    (hX : HasScalarCharacter X.representation z ω) :
    HasScalarCharacter D.representation z ω := by
  obtain ⟨Y, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp h
  exact (hX.of_injective (SmoothRep.hom i) hi).of_surjective (SmoothRep.hom q) hq

omit [TopologicalSpace G] in
/-- On a nonzero carrier a scalar character is unique. -/
theorem scalarCharacter_eq {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {ρ : Representation ℂ G V} {z : C →* G} {ω ω' : C →* ℂˣ}
    (h : HasScalarCharacter ρ z ω) (h' : HasScalarCharacter ρ z ω') : ω = ω' := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  ext c
  exact smul_left_injective ℂ hv ((h c v).symm.trans (h' c v))

end Scalar

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ## Exponents -/

/-- The real exponent of a power of the normalized absolute value is unique. -/
theorem exponent_eq {e e' : ℝ}
    (h : ∀ a : F.Carrierˣ,
      T.normalizedAbs (a : F.Carrier) ^ e = T.normalizedAbs (a : F.Carrier) ^ e') :
    e = e' := by
  have hq1 : (1 : ℝ) < T.residueCardinality := T.one_lt_residueCardinality_real
  have hq0 : (0 : ℝ) < T.residueCardinality := lt_trans zero_lt_one hq1
  set x := T.normalizedAbs (T.uniformizerUnit : F.Carrier) with hx
  have hxpos : 0 < x := T.normalizedAbs_pos T.uniformizerUnit.ne_zero
  have hx1 : x ≠ 1 := by
    rw [hx, T.uniformizerUnit_val, T.normalizedAbs_uniformizer, zpow_neg_one]
    intro h1
    have := inv_eq_one.mp h1
    linarith
  have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hxpos hx1
  have h1 := congrArg Real.log (h T.uniformizerUnit)
  rw [Real.log_rpow hxpos, Real.log_rpow hxpos] at h1
  exact mul_right_cancel₀ hlog h1

/-- Every irreducible smooth representation of `GL_n(F)`, including `n = 0`, has a
Bernstein central exponent: Schur's lemma gives the scalar character, and its
open kernel makes its absolute value a real power of `|·|`. -/
theorem exists_hasBernsteinCentralExponent {n : ℕ}
    (D : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hD : letI := T.topology; D.IsIrreducible) :
    ∃ e : ℝ, HasBernsteinCentralExponent T D e := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup n
  have := T.generalLinearSecondCountableTopology n
  have hrank := Whittaker.MirabolicRigidity.rank_le_aleph0 D.representation D.isSmooth hD
  have hc : ∀ a : F.Carrierˣ, ∃ c : ℂ,
      ∀ v, D.representation (GeneralLinear.scalar a) v = c • v := fun a =>
    Whittaker.MirabolicRigidity.exists_scalar_of_commute D.representation hrank hD _
      (fun g => congrArg D.representation (Matrix.GeneralLinearGroup.scalar_commute a g).symm)
  choose c hc using hc
  have : Nontrivial D := SegmentHeadSupport.nontrivial_of_isIrreducible hD
  obtain ⟨v, hv⟩ := exists_ne (0 : D)
  have c_one : c 1 = 1 := by
    apply smul_left_injective ℂ hv
    change c 1 • v = (1 : ℂ) • v
    rw [← hc, map_one, map_one, one_smul]
    rfl
  have c_mul (a b : F.Carrierˣ) : c (a * b) = c a * c b := by
    apply smul_left_injective ℂ hv
    change c (a * b) • v = (c a * c b) • v
    rw [← hc, map_mul, map_mul, Module.End.mul_apply, hc, hc, smul_smul]
  have c_ne (a : F.Carrierˣ) : c a ≠ 0 := by
    intro ha
    have h := c_mul a⁻¹ a
    rw [inv_mul_cancel, c_one, ha, mul_zero] at h
    exact one_ne_zero h
  let ω : F.Carrierˣ →* ℂˣ :=
    { toFun := fun a => Units.mk0 (c a) (c_ne a)
      map_one' := Units.ext c_one
      map_mul' := fun a b => Units.ext (c_mul a b) }
  have hω : HasScalarCharacter D.representation GeneralLinear.scalar ω := fun a w => hc a w
  have hker : IsOpen (ω.ker : Set F.Carrierˣ) :=
    hω.isOpen_ker (T.generalLinearScalar n).continuous D.isSmooth
  exact ⟨_, ω, hω, T.norm_eq_normalizedAbs_rpow_of_isOpen_ker ω hker⟩

/-- Twisting by `ν^s` shifts every Bernstein central exponent by `n s`. -/
theorem hasBernsteinCentralExponent_segmentFactor {n : ℕ}
    {D : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} {e : ℝ}
    (h : HasBernsteinCentralExponent T D e) (s : ℝ) :
    HasBernsteinCentralExponent T (T.segmentFactor D s) (e + n * s) := by
  let := T.topology
  obtain ⟨ω, hω, hn⟩ := h
  refine ⟨ω * (T.determinantPowerCharacter n s).comp GeneralLinear.scalar,
    T.hasScalarCharacter_segmentFactor D s hω, fun a => ?_⟩
  have hpos := T.normalizedAbs_pos a.ne_zero
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hn, MonoidHom.comp_apply,
    T.coe_determinantPowerCharacter_scalar, Complex.norm_real, Real.norm_eq_abs,
    T.normalizedAbsUnits_coe, abs_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← Real.rpow_add hpos]

/-- Exponents of actual irreducible subquotients move with the twist `ν^s`. -/
theorem mem_bernsteinCentralExponents_segmentFactor {n : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} {e : ℝ}
    (he : e ∈ bernsteinCentralExponents T X) (s : ℝ) :
    e + n * s ∈ bernsteinCentralExponents T (T.segmentFactor X s) := by
  let := T.topology
  obtain ⟨D, hD, hDX, hDe⟩ := he
  exact ⟨T.segmentFactor D s, (SmoothRep.isIrreducible_twist_iff _ _ D).mpr hD,
    hDX.twist _ _, hasBernsteinCentralExponent_segmentFactor T hDe s⟩

/-- `ν^(-s) (ν^s X) ≅ X`. -/
def segmentFactorNegIso {n : ℕ}
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (s : ℝ) :
    letI := T.topology
    T.segmentFactor (T.segmentFactor X s) (-s) ≅ X := by
  letI := T.topology
  refine SmoothRep.mkIso (equivOfRepresentationEq ?_)
  change twist (realPowerCharacter (T.determinantNorm n) (-s))
      (twist (realPowerCharacter (T.determinantNorm n) s) X.representation) = X.representation
  rw [twist_twist, ← realPowerCharacter_add, neg_add_cancel, realPowerCharacter_zero, twist_one]

/-- Conversely, an exponent of `ν^s X` comes from an exponent of `X`. -/
theorem mem_bernsteinCentralExponents_of_segmentFactor {n : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} {e s : ℝ}
    (he : e ∈ bernsteinCentralExponents T (T.segmentFactor X s)) :
    e - n * s ∈ bernsteinCentralExponents T X := by
  let := T.topology
  obtain ⟨D, hD, hDX, hDe⟩ := mem_bernsteinCentralExponents_segmentFactor T he (-s)
  refine ⟨D, hD, hDX.of_iso_right (segmentFactorNegIso T X s), ?_⟩
  convert hDe using 1
  ring

/-! ## Unitarizable representations -/

/-- On an actual irreducible subquotient of a finite-length unitarizable
representation, every scalar matrix acts by a complex number of absolute value one. -/
theorem norm_scalarCharacter_eq_one {n : ℕ}
    {U D : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hU : letI := T.topology; U.HasFiniteLength)
    (hu : letI := T.topology; IsUnitarizable U.representation)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDU : letI := T.topology; SmoothRep.IsSubquotient D U) {ω : F.Carrierˣ →* ℂˣ}
    (hω : letI := T.topology; HasScalarCharacter D.representation GeneralLinear.scalar ω)
    (a : F.Carrierˣ) : ‖(ω a : ℂ)‖ = 1 := by
  let := T.topology
  obtain ⟨X, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hDU
  have hX : X.HasFiniteLength := hU.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom i)) hi
  have hni := ScalarSubReduction.centralDefect_not_injective hX hD
    (GeneralLinear.scalarToCenter a) (ω a : ℂ) (fun w => hω a w) (SmoothRep.hom q) hq
  obtain ⟨x, hx0, hx⟩ : ∃ x : X, x ≠ 0 ∧
      X.representation (GeneralLinear.scalar a) x = (ω a : ℂ) • x := by
    by_contra hne
    push Not at hne
    apply hni
    intro x y hxy
    by_contra hxy'
    apply hne (x - y) (sub_ne_zero.mpr hxy')
    rw [ScalarSubReduction.centralDefect_apply, ScalarSubReduction.centralDefect_apply] at hxy
    rw [map_sub, smul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp hxy
  obtain ⟨b⟩ := hu
  set c : ℂ := (ω a : ℂ) with hc
  let y : U := SmoothRep.hom i x
  have hy0 : y ≠ 0 := fun h => hx0 (hi (h.trans (map_zero _).symm))
  have hy : U.representation (GeneralLinear.scalar a) y = c • y := by
    change U.representation _ (SmoothRep.hom i x) = c • SmoothRep.hom i x
    rw [← Representation.IntertwiningMap.isIntertwining, hx, map_smul]
  have hinv := b.invariant (GeneralLinear.scalar a) y y
  rw [hy] at hinv
  have hsl : ∀ (r : ℂ) (u w : U), b.inner (r • u) w = (starRingEnd ℂ) r * b.inner u w :=
    fun r u w => b.smul_left u w r
  have hsr : ∀ (r : ℂ) (u w : U), b.inner u (r • w) = r * b.inner u w := by
    intro r u w
    rw [← b.conj_inner_symm, hsl, map_mul, Complex.conj_conj, b.conj_inner_symm]
  change b.inner (c • y) (c • y) = b.inner y y at hinv
  rw [hsl, hsr] at hinv
  have hI : b.inner y y ≠ 0 := fun h => hy0 (b.definite y h)
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    apply mul_right_cancel₀ hI
    linear_combination hinv
  rw [Complex.mul_conj, Complex.ofReal_eq_one, Complex.normSq_eq_norm_sq] at hcc
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hcc

/-- Every exponent of an actual irreducible subquotient of a finite-length
unitarizable representation is zero. -/
theorem exponent_eq_zero_of_isUnitarizable {n : ℕ}
    {U : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hU : letI := T.topology; U.HasFiniteLength)
    (hu : letI := T.topology; IsUnitarizable U.representation) {e : ℝ}
    (he : e ∈ bernsteinCentralExponents T U) : e = 0 := by
  let := T.topology
  obtain ⟨D, hD, hDU, ω, hω, hn⟩ := he
  apply exponent_eq T
  intro a
  rw [← hn a, norm_scalarCharacter_eq_one T hU hu hD hDU hω a, Real.rpow_zero]

/-! ## Binary products -/

/-- The entry-preserving reindex fixes scalar matrices. -/
theorem reindex_scalar {m n : ℕ} (h : m = n) (a : F.Carrierˣ) :
    GeneralLinear.reindex (R := F.Carrier) (finCongr h) (GeneralLinear.scalar a) =
      GeneralLinear.scalar a := by
  apply Units.ext
  ext i j
  rw [GeneralLinear.reindex_finCongr_apply]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Fin.ext_iff]

/-- On `GL_0` the scalar character of a nonzero representation is trivial. -/
theorem scalarCharacter_eq_one_of_rank_eq_zero {m : ℕ} (hm : m = 0)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    {ρ : Representation ℂ (GeneralLinear m F.Carrier) V} {ω : F.Carrierˣ →* ℂˣ}
    (h : HasScalarCharacter ρ GeneralLinear.scalar ω) : ω = 1 := by
  apply scalarCharacter_eq h
  intro a v
  rw [GeneralLinear.representation_apply_of_rank_eq_zero hm ρ, MonoidHom.one_apply,
    Units.val_one, one_smul]
  rfl

/-- The scalar character of the actual binary normalized product is the product of
the scalar characters of its nonzero factors, in all ranks. -/
theorem hasScalarCharacter_binaryProduct {m n : ℕ}
    {E : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)}
    {H : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    {ω₁ ω₂ : F.Carrierˣ →* ℂˣ}
    (hE : letI := T.topology; HasScalarCharacter E.representation GeneralLinear.scalar ω₁)
    (hH : letI := T.topology; HasScalarCharacter H.representation GeneralLinear.scalar ω₂)
    [Nontrivial E] [Nontrivial H] :
    letI := T.topology
    HasScalarCharacter ((T.binaryNormalizedProductFunctor m n).obj (E, H)).representation
      GeneralLinear.scalar (ω₁ * ω₂) := by
  let := T.topology
  by_cases hm : m = 0
  · have h1 : ω₁ = 1 := scalarCharacter_eq_one_of_rank_eq_zero hm hE
    have h1' : ω₁ * ω₂ = ω₂ := MonoidHom.ext fun x => by
      rw [MonoidHom.mul_apply, h1, MonoidHom.one_apply, one_mul]
    rw [T.binaryNormalizedProductFunctor_of_left_eq_zero hm, h1']
    rintro a ⟨w⟩
    change ULift.up (BinaryTensor.rankZeroLeft hm E H.representation
      (GeneralLinear.scalar a) w) = ULift.up ((ω₂ a : ℂ) • w)
    congr 1
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      rw [BinaryTensor.rankZeroLeft_tmul, reindex_scalar, hH, TensorProduct.tmul_smul]
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  by_cases hn : n = 0
  · have h2 : ω₂ = 1 := scalarCharacter_eq_one_of_rank_eq_zero hn hH
    have h2' : ω₁ * ω₂ = ω₁ := MonoidHom.ext fun x => by
      rw [MonoidHom.mul_apply, h2, MonoidHom.one_apply, mul_one]
    rw [T.binaryNormalizedProductFunctor_of_right_eq_zero hm hn, h2']
    rintro a ⟨w⟩
    change ULift.up (BinaryTensor.rankZeroRight hn E.representation H
      (GeneralLinear.scalar a) w) = ULift.up ((ω₁ a : ℂ) • w)
    congr 1
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      rw [BinaryTensor.rankZeroRight_tmul, reindex_scalar, hE, TensorProduct.smul_tmul']
    | add x y hx hy => rw [map_add, hx, hy, smul_add]
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  rw [T.binaryNormalizedProductFunctor_of_pos hm' hn']
  let c : Fin (BlockShape.binary m n hm' hn').length → (F.Carrierˣ →* ℂˣ) :=
    Fin.cases ω₁ (fun _ => ω₂)
  have key := T.hasScalarCharacter_normalizedProductInduced (BlockShape.binary m n hm' hn')
    (σ := fun i => ((T.binaryPairFamilyFunctor hm' hn').obj (E, H) i).representation)
    (c := c) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hE
      · exact hH)
  have hprod : (∏ i, c i) = ω₁ * ω₂ := Fin.prod_univ_two c
  rw [hprod] at key
  exact key

/-- The rank transport keeps the scalar character. -/
theorem hasScalarCharacter_rankCast {m n : ℕ} (h : m = n)
    {X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)}
    {ω : F.Carrierˣ →* ℂˣ}
    (hX : letI := T.topology; HasScalarCharacter X.representation GeneralLinear.scalar ω) :
    letI := T.topology
    HasScalarCharacter ((Derivative.generalLinearRankCast T h).obj X).representation
      GeneralLinear.scalar ω := by
  subst h
  exact hX

/-- The exponent of an actual irreducible subquotient of a rank-cast binary product
of irreducible representations is the sum of exponents of the two factors. -/
theorem exists_exponent_add_of_product {m n r : ℕ} (h : m + n = r)
    {E : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)}
    {H : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    {D : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
    (hE : letI := T.topology; E.IsIrreducible) (hH : letI := T.topology; H.IsIrreducible)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((Derivative.generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor m n).obj (E, H))))
    {e : ℝ} (he : HasBernsteinCentralExponent T D e) :
    ∃ e₁ e₂ : ℝ, HasBernsteinCentralExponent T E e₁ ∧
      HasBernsteinCentralExponent T H e₂ ∧ e = e₁ + e₂ := by
  let := T.topology
  obtain ⟨e₁, ω₁, hω₁, hn₁⟩ := exists_hasBernsteinCentralExponent T E hE
  obtain ⟨e₂, ω₂, hω₂, hn₂⟩ := exists_hasBernsteinCentralExponent T H hH
  have : Nontrivial E := SegmentHeadSupport.nontrivial_of_isIrreducible hE
  have : Nontrivial H := SegmentHeadSupport.nontrivial_of_isIrreducible hH
  have : Nontrivial D := SegmentHeadSupport.nontrivial_of_isIrreducible hD
  have hP := hasScalarCharacter_rankCast T h (hasScalarCharacter_binaryProduct T hω₁ hω₂)
  have hDω := hasScalarCharacter_of_isSubquotient hDP hP
  obtain ⟨ω, hω, hn⟩ := he
  have heq := scalarCharacter_eq hω hDω
  refine ⟨e₁, e₂, ⟨ω₁, hω₁, hn₁⟩, ⟨ω₂, hω₂, hn₂⟩, exponent_eq T fun a => ?_⟩
  have hpos := T.normalizedAbs_pos a.ne_zero
  rw [← hn a, heq, MonoidHom.mul_apply, Units.val_mul, norm_mul, hn₁, hn₂,
    ← Real.rpow_add hpos]

/-! ## Exponents of the shifted derivatives of one factor -/

/-- The hypotheses on one factor bound the exponents of its unshifted derivatives:
nothing occurs above the supplied order, exponents are at least `-(a-i)/2`, and
strictly larger below the supplied order. -/
theorem derivative_exponent_bound
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a r : ℕ} (hr : r ≤ a)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    (hA : letI := T.topology; A.HasFiniteLength)
    (hvan : letI := T.topology
      ∀ (j : ℕ) (hj : j ≤ a), r < j →
        Subsingleton ((Derivative.generalLinearDerivative T ψ a j hj).obj A))
    (hpos : BernsteinShiftedDerivativePositiveBelow T ψ A r)
    (hunit : letI := T.topology
      IsUnitarizable (bernsteinShiftedDerivative T ψ A r hr).representation)
    {i : ℕ} (hi : i ≤ a) {e : ℝ}
    (he : e ∈ bernsteinCentralExponents T
      ((Derivative.generalLinearDerivative T ψ a i hi).obj A)) :
    i ≤ r ∧ 0 ≤ e + ((a - i : ℕ) : ℝ) * (1 / 2) ∧
      (i < r → 0 < e + ((a - i : ℕ) : ℝ) * (1 / 2)) := by
  let := T.topology
  have hir : i ≤ r := by
    by_contra hlt
    push Not at hlt
    obtain ⟨D, hD, hDX, -⟩ := he
    have hs := SegmentHeadSupport.subsingleton_of_isSubquotient hDX (hvan i hi hlt)
    have := SegmentHeadSupport.nontrivial_of_isIrreducible hD
    exact not_subsingleton D hs
  have he' := mem_bernsteinCentralExponents_segmentFactor T he (1 / 2)
  rcases lt_or_eq_of_le hir with hlt | heq
  · have := hpos i hi hlt _ he'
    exact ⟨hir, this.le, fun _ => this⟩
  · subst heq
    have hfin : ((Derivative.generalLinearDerivative T ψ a i hi).obj A).HasFiniteLength :=
      Derivative.generalLinearDerivativeFiniteLength.{uF, uV} F T ψ a i hi A hA
    have hfin' : (bernsteinShiftedDerivative T ψ A i hi).HasFiniteLength :=
      (finiteLength_twist_iff _ _).mpr hfin
    have h0 := exponent_eq_zero_of_isUnitarizable T hfin' hunit he'
    exact ⟨hir, h0.ge, fun h => absurd h (lt_irrefl _)⟩

end BernsteinProductPositivity

open BernsteinProductPositivity

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Bernstein's product positivity with unitary top shifted derivatives. -/
theorem bernsteinUnitaryTopDerivativeProductPositivity :
    BernsteinUnitaryTopDerivativeProductPositivity.{uF, uV} F T := by
  let := T.topology
  intro ψ a b A B hA hB r s hr hs hvA hvB hpA hpB huA huB k hk hkrs e he
  have he0 := mem_bernsteinCentralExponents_of_segmentFactor T he
  obtain ⟨D, hD, hDZ, hDe⟩ := he0
  have hfin := Derivative.generalLinearDerivativeFiniteLength.{uF, max uF uV} F T ψ
  let f := Derivative.BinaryDerivativeSupport.factorData.{uF, uV} T ψ hk A B
    (fun i hi => hfin a i hi A hA) (fun j hj => hfin b j hj B hB) D hD hDZ
  have hDP : SmoothRep.IsSubquotient D ((Derivative.generalLinearRankCast T
      (Derivative.leibnizIndices_rank f.index.property)).obj
        ((T.binaryNormalizedProductFunctor (a - f.index.val.1) (b - f.index.val.2)).obj
          (f.left, f.right))) :=
    ⟨f.subspace, f.kernel, ⟨f.occurrenceIso⟩⟩
  obtain ⟨e₁, e₂, he₁, he₂, hsum⟩ := exists_exponent_add_of_product T
    (Derivative.leibnizIndices_rank f.index.property) f.left_irreducible f.right_irreducible
    hD hDP hDe
  obtain ⟨hir, hi0, hipos⟩ := derivative_exponent_bound T ψ hr A hA hvA hpA huA
    (Derivative.leibnizIndices_left_le f.index.property)
    ⟨f.left, f.left_irreducible, f.left_occurs, he₁⟩
  obtain ⟨hjs, hj0, hjpos⟩ := derivative_exponent_bound T ψ hs B hB hvB hpB huB
    (Derivative.leibnizIndices_right_le f.index.property)
    ⟨f.right, f.right_irreducible, f.right_occurs, he₂⟩
  have hijk := Derivative.leibnizIndices_sum f.index.property
  have hrank := Derivative.leibnizIndices_rank f.index.property
  have hcast : (((a + b - k : ℕ)) : ℝ) =
      ((a - f.index.val.1 : ℕ) : ℝ) + ((b - f.index.val.2 : ℕ) : ℝ) := by
    rw [← hrank]
    push_cast
    ring
  have he_eq : e = (e₁ + ((a - f.index.val.1 : ℕ) : ℝ) * (1 / 2)) +
      (e₂ + ((b - f.index.val.2 : ℕ) : ℝ) * (1 / 2)) := by
    have : e = (e - ((a + b - k : ℕ) : ℝ) * (1 / 2)) + ((a + b - k : ℕ) : ℝ) * (1 / 2) := by
      ring
    rw [this, hsum, hcast]
    ring
  rcases Nat.lt_or_ge f.index.val.1 r with hlt | hge
  · have := hipos hlt
    rw [he_eq]
    linarith
  · have hlt : f.index.val.2 < s := by omega
    have := hjpos hlt
    rw [he_eq]
    linarith

end Langlands.Classification
