import Langlands.Geometry.Analytic.AffineAnalytificationImmersionStatement
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.AnalytificationCenter
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Valuation.Quotient
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-! # Proof: affine analytification preserves closed and basic open immersions -/

noncomputable section

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open Set Topology
open scoped NNReal

namespace ImmersionComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type v} [CommRing A] [Algebra K A]

/-- Regard an extending seminorm as a nonnegative-real valuation. -/
def valuationOfSeminorm (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν) :
    Valuation A ℝ≥0 where
  toFun a := ⟨ν a, apply_nonneg ν a⟩
  map_zero' := Subtype.ext (map_zero ν)
  map_one' := Subtype.ext (map_one ν)
  map_mul' a b := Subtype.ext (map_mul ν a b)
  map_add_le_max' a b := SeminormComparison.add_le_max hν a b

theorem valuationOfSeminorm_eq_zero (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (a : A) (ha : ν a = 0) : valuationOfSeminorm ν hν a = 0 := by
  apply Subtype.ext
  exact ha

/-- Regard a nonnegative-real valuation as a real multiplicative seminorm. -/
def seminormOfValuation {D : Type*} [CommRing D] (ν : Valuation D ℝ≥0) :
    MulRingSeminorm D where
  toFun a := ν a
  map_zero' := congrArg NNReal.toReal ν.map_zero
  map_one' := congrArg NNReal.toReal ν.map_one
  map_mul' a b := congrArg NNReal.toReal (ν.map_mul a b)
  add_le' a b := (show (ν (a + b) : ℝ) ≤ max (ν a : ℝ) (ν b : ℝ) from
    ν.map_add a b).trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
  neg' a := congrArg NNReal.toReal (ν.map_neg a)

variable {B : Type w} [CommRing B] [Algebra K B]

theorem ker_le_valuation_support (f : A →ₐ[K] B)
    (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hker : ∀ a, f a = 0 → ν a = 0) :
    RingHom.ker f ≤ (valuationOfSeminorm ν hν).supp := by
  intro a ha
  exact valuationOfSeminorm_eq_zero ν hν a (hker a (RingHom.mem_ker.mp ha))

/-- Descent of a seminorm annihilating the kernel of a surjective algebra map. -/
def quotientSeminorm (f : A →ₐ[K] B) (hf : Function.Surjective f)
    (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hker : ∀ a, f a = 0 → ν a = 0) : MulRingSeminorm B :=
  seminormOfValuation (((valuationOfSeminorm ν hν).onQuot
    (ker_le_valuation_support f ν hν hker)).comap
      ((f : A →+* B).quotientKerEquivOfSurjective hf).symm.toRingHom)

@[simp]
theorem quotientSeminorm_apply_map (f : A →ₐ[K] B) (hf : Function.Surjective f)
    (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hker : ∀ a, f a = 0 → ν a = 0) (a : A) :
    quotientSeminorm f hf ν hν hker (f a) = ν a := by
  change (((valuationOfSeminorm ν hν).onQuot
    (ker_le_valuation_support f ν hν hker))
    (((f : A →+* B).quotientKerEquivOfSurjective hf).symm (f a)) : ℝ) = _
  erw [RingHom.quotientKerEquivOfSurjective_symm_apply (f := (f : A →+* B)) hf]
  rfl

theorem quotientSeminorm_extendsNorm (f : A →ₐ[K] B) (hf : Function.Surjective f)
    (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hker : ∀ a, f a = 0 → ν a = 0) :
    ExtendsNorm K (quotientSeminorm f hf ν hν hker) := by
  intro c
  rw [← f.commutes, quotientSeminorm_apply_map]
  exact hν c

variable [CompleteSpace K]
variable (K) (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)

/-- Surjective algebra maps induce embeddings for the evaluation topologies. -/
theorem isEmbedding_baseMap_surjective (f : A →ₐ[K] B) (hf : Function.Surjective f) :
    IsEmbedding (baseMap K P Q f) := by
  have hcomp : (fun (y : Space K Q) (a : A) =>
      pointSeminorm K P (baseMap K P Q f y) a) =
      (fun s : B → ℝ => s ∘ f) ∘
        (fun (y : Space K Q) (b : B) => pointSeminorm K Q y b) := by
    funext y a
    exact pointSeminorm_baseMap K P Q f y a
  apply IsEmbedding.of_comp (baseMap K P Q f).continuous
    (SeminormComparison.isEmbedding_pointSeminorm K P).continuous
  rw [show ((fun (z : Space K P) (a : A) => pointSeminorm K P z a) ∘
      baseMap K P Q f) = _ from hcomp]
  exact (hf.isEmbedding_comp f).comp (SeminormComparison.isEmbedding_pointSeminorm K Q)

/-- The image of a quotient map consists of seminorms annihilating its kernel. -/
theorem range_baseMap_surjective (f : A →ₐ[K] B) (hf : Function.Surjective f) :
    range (baseMap K P Q f) =
      {z | ∀ a, f a = 0 → pointSeminorm K P z a = 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩ a ha
    rw [pointSeminorm_baseMap, ha, map_zero]
  · intro hz
    let ν := quotientSeminorm f hf (pointSeminorm K P z)
      (pointSeminorm_extendsNorm K P z) hz
    have hν : ExtendsNorm K ν := quotientSeminorm_extendsNorm _ _ _ _ _
    obtain ⟨y, hy⟩ := (SeminormComparison.range_pointSeminorm K Q).symm ▸
      (show ν ∈ {ν | ExtendsNorm K ν} from hν)
    refine ⟨y, SeminormComparison.pointSeminorm_injective K P ?_⟩
    ext a
    rw [pointSeminorm_baseMap, hy]
    exact quotientSeminorm_apply_map f hf _ _ hz a

/-- A surjective algebra map induces a closed embedding of analytifications. -/
theorem isClosedEmbedding_baseMap_surjective (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : IsClosedEmbedding (baseMap K P Q f) := by
  refine ⟨isEmbedding_baseMap_surjective K P Q f hf, ?_⟩
  rw [range_baseMap_surjective K P Q f hf]
  have e : {z : Space K P | ∀ a, f a = 0 → pointSeminorm K P z a = 0} =
      ⋂ (a : A) (_ha : f a = 0), {z | pointSeminorm K P z a = 0} := by
    ext z
    simp
  rw [e]
  exact isClosed_iInter fun a => isClosed_iInter fun _ha =>
    isClosed_eq (continuous_pointSeminorm_apply K P a) continuous_const

/-- Quotienting by the generator cuts out precisely its vanishing locus. -/
theorem range_baseMap_quotient_singleton (g : A) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) (hker : RingHom.ker f = Ideal.span {g}) :
    range (baseMap K P Q f) = {z | pointSeminorm K P z g = 0} := by
  rw [range_baseMap_surjective K P Q f hf]
  ext z
  constructor
  · intro hz
    apply hz g
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (by simp)
  · intro hz a ha
    have hspan : Ideal.span {g} ≤ kernel K P z :=
      (Ideal.span_singleton_le_iff_mem (kernel K P z)).mpr ((mem_kernel K P z g).mpr hz)
    apply (mem_kernel K P z a).mp
    apply hspan
    rw [← hker]
    exact RingHom.mem_ker.mpr ha

/-- Choose the point represented by an extending seminorm. -/
def pointOfSeminorm (ν : MulRingSeminorm B) (hν : ExtendsNorm K ν) : Space K Q :=
  Classical.choose ((SeminormComparison.range_pointSeminorm K Q).symm ▸
    (show ν ∈ {ν | ExtendsNorm K ν} from hν))

@[simp]
theorem pointSeminorm_pointOfSeminorm (ν : MulRingSeminorm B) (hν : ExtendsNorm K ν) :
    pointSeminorm K Q (pointOfSeminorm K Q ν hν) = ν :=
  Classical.choose_spec ((SeminormComparison.range_pointSeminorm K Q).symm ▸
    (show ν ∈ {ν | ExtendsNorm K ν} from hν))

section Away

variable (g : A) [Algebra A B] [IsScalarTower K A B] [IsLocalization.Away g B]

omit [CompleteSpace K] in
/-- The denominators avoid the support precisely when the generator has nonzero value. -/
theorem awayDenominators (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hg : ν g ≠ 0) :
    Submonoid.powers g ≤ (valuationOfSeminorm ν hν).supp.primeCompl := by
  intro a ha
  change valuationOfSeminorm ν hν a ≠ 0
  obtain ⟨n, rfl⟩ := ha
  rw [map_pow]
  exact pow_ne_zero _ (fun h => hg (congrArg NNReal.toReal h))

/-- Extend a seminorm uniquely across the principal localization. -/
def awaySeminorm (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν) (hg : ν g ≠ 0) :
    MulRingSeminorm B :=
  seminormOfValuation ((valuationOfSeminorm ν hν).extendToLocalization
    (awayDenominators K g ν hν hg) B)

omit [Algebra K B] [CompleteSpace K] [IsScalarTower K A B] in
@[simp]
theorem awaySeminorm_apply_map (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hg : ν g ≠ 0) (a : A) :
    awaySeminorm K (B := B) g ν hν hg (algebraMap A B a) = ν a := by
  change ((valuationOfSeminorm ν hν).extendToLocalization
    (awayDenominators K g ν hν hg) B (algebraMap A B a) : ℝ) = _
  rw [Valuation.extendToLocalization_apply_map_apply]
  rfl

omit [CompleteSpace K] in
theorem awaySeminorm_extendsNorm (ν : MulRingSeminorm A) (hν : ExtendsNorm K ν)
    (hg : ν g ≠ 0) : ExtendsNorm K (awaySeminorm K (B := B) g ν hν hg) := by
  intro c
  rw [IsScalarTower.algebraMap_apply K A B, awaySeminorm_apply_map]
  exact hν c

/-- A multiplicative seminorm cannot vanish at the invertible localization generator. -/
theorem seminorm_map_generator_ne_zero (ν : MulRingSeminorm B) :
    ν (algebraMap A B g) ≠ 0 := by
  intro h
  have e := congrArg (fun b : B => ν b) (IsLocalization.Away.mul_invSelf g (S := B))
  rw [map_mul, h, zero_mul, map_one] at e
  exact zero_ne_one e

/-- The value of a fraction is its numerator value divided by the denominator value. -/
theorem seminorm_fraction (ν : MulRingSeminorm B) (b : B) :
    ν b = ν (algebraMap A B (IsLocalization.Away.sec g b).1) /
      ν (algebraMap A B g) ^ (IsLocalization.Away.sec g b).2 := by
  apply (eq_div_iff (pow_ne_zero _ (seminorm_map_generator_ne_zero g ν))).2
  have e := congrArg (fun b : B => ν b) (IsLocalization.Away.sec_spec g b)
  simpa only [map_mul, map_pow] using e

include g in
/-- A seminorm on the localization is determined by its restriction. -/
theorem seminorm_away_ext (ν μ : MulRingSeminorm B)
    (h : ∀ a : A, ν (algebraMap A B a) = μ (algebraMap A B a)) : ν = μ := by
  ext b
  rw [seminorm_fraction g ν b, seminorm_fraction g μ b, h, h]

/-- The nonvanishing locus maps back to the localization analytification. -/
def awaySection (z : {z : Space K P // pointSeminorm K P z g ≠ 0}) : Space K Q :=
  pointOfSeminorm K Q
    (awaySeminorm K g (pointSeminorm K P z) (pointSeminorm_extendsNorm K P z) z.property)
    (awaySeminorm_extendsNorm K g _ _ z.property)

theorem awaySection_apply_map
    (z : {z : Space K P // pointSeminorm K P z g ≠ 0}) (a : A) :
    pointSeminorm K Q (awaySection K P Q g z) (algebraMap A B a) =
      pointSeminorm K P z a := by
  rw [awaySection, pointSeminorm_pointOfSeminorm, awaySeminorm_apply_map]

theorem baseMap_awaySection (z : {z : Space K P // pointSeminorm K P z g ≠ 0}) :
    baseMap K P Q (IsScalarTower.toAlgHom K A B) (awaySection K P Q g z) = z := by
  apply SeminormComparison.pointSeminorm_injective K P
  ext a
  rw [pointSeminorm_baseMap]
  exact awaySection_apply_map K P Q g z a

/-- The principal localization image is exactly the nonvanishing locus. -/
theorem range_baseMap_away :
    range (baseMap K P Q (IsScalarTower.toAlgHom K A B)) =
      {z | pointSeminorm K P z g ≠ 0} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    change pointSeminorm K P (baseMap K P Q (IsScalarTower.toAlgHom K A B) y) g ≠ 0
    rw [pointSeminorm_baseMap]
    exact seminorm_map_generator_ne_zero g (pointSeminorm K Q y)
  · intro hz
    exact ⟨awaySection K P Q g ⟨z, hz⟩, baseMap_awaySection K P Q g ⟨z, hz⟩⟩

theorem continuous_awaySection : Continuous (awaySection K P Q g) := by
  apply (SeminormComparison.isEmbedding_pointSeminorm K Q).continuous_iff.2
  apply continuous_pi
  intro b
  have e : (fun z : {z : Space K P // pointSeminorm K P z g ≠ 0} =>
      pointSeminorm K Q (awaySection K P Q g z) b) =
      (fun z : {z : Space K P // pointSeminorm K P z g ≠ 0} =>
        pointSeminorm K P z (IsLocalization.Away.sec g b).1 /
        pointSeminorm K P z g ^ (IsLocalization.Away.sec g b).2) := by
    funext z
    rw [seminorm_fraction g, awaySection_apply_map, awaySection_apply_map]
  change Continuous (fun z : {z : Space K P // pointSeminorm K P z g ≠ 0} =>
    pointSeminorm K Q (awaySection K P Q g z) b)
  rw [e]
  exact ((continuous_pointSeminorm_apply K P _).comp continuous_subtype_val).div
    (((continuous_pointSeminorm_apply K P g).comp continuous_subtype_val).pow _)
    (fun z => pow_ne_zero _ z.property)

include g in
/-- A principal localization induces an open embedding of analytifications. -/
theorem isOpenEmbedding_baseMap_away :
    IsOpenEmbedding (baseMap K P Q (IsScalarTower.toAlgHom K A B)) := by
  let F : Space K Q → {z : Space K P // pointSeminorm K P z g ≠ 0} :=
    fun y => ⟨baseMap K P Q (IsScalarTower.toAlgHom K A B) y, by
      rw [pointSeminorm_baseMap]
      exact seminorm_map_generator_ne_zero g (pointSeminorm K Q y)⟩
  have hF : Continuous F :=
    (baseMap K P Q (IsScalarTower.toAlgHom K A B)).continuous.subtype_mk _
  have hi : Function.LeftInverse (awaySection K P Q g) F := by
    intro y
    apply SeminormComparison.pointSeminorm_injective K Q
    apply seminorm_away_ext g
    intro a
    rw [awaySection_apply_map, pointSeminorm_baseMap]
    rfl
  refine ⟨IsEmbedding.subtypeVal.comp
    (hi.isEmbedding (continuous_awaySection K P Q g) hF), ?_⟩
  rw [range_baseMap_away K P Q g]
  exact isOpen_ne_fun (continuous_pointSeminorm_apply K P g) continuous_const

variable {C : Type x} [CommRing C] [Algebra K C] [Algebra A C] [IsScalarTower K A C]

/-- The principal localization and the quotient by its generator have complementary images. -/
theorem range_baseMap_away_compl (R : FinitePolynomialPresentation K C)
    (hf : Function.Surjective (algebraMap A C))
    (hker : RingHom.ker (algebraMap A C) = Ideal.span {g}) :
    range (baseMap K P Q (IsScalarTower.toAlgHom K A B)) =
      (range (baseMap K P R (IsScalarTower.toAlgHom K A C)))ᶜ := by
  rw [range_baseMap_away K P Q g,
    range_baseMap_quotient_singleton K P R g (IsScalarTower.toAlgHom K A C) hf hker]
  rfl

end Away

end ImmersionComparison

/-- Affine analytification preserves closed and principal open immersions, with complementary
images for a principal localization and the quotient by the same generator. -/
theorem affineAnalytificationImmersion :
    AffineAnalytificationImmersionStatement.{u, v, w, x} := by
  intro K _ _ _ A _ _ P
  refine ⟨?_, ?_, ?_⟩
  · intro B _ _ Q f hf
    exact ImmersionComparison.isClosedEmbedding_baseMap_surjective K P Q f hf
  · intro g B _ _ _ _ _ Q
    exact ImmersionComparison.isOpenEmbedding_baseMap_away K P Q g
  · intro g B _ _ _ _ _ C _ _ _ _ Q R hf hker
    exact ImmersionComparison.range_baseMap_away_compl K P Q g R hf hker

end Langlands.Analytic.AffineAnalytification
