import Langlands.Global.AdelicMinimalIwasawaCompactRepresentatives
import Langlands.Global.LeftCosetExponentialHeightMoment

/-! # Finite weighted measure from minimal-parabolic Iwasawa coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set Topology
open scoped CategoryTheory.MonObj Pointwise ENNReal

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus

variable (F : Type u) [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {T T₀ : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (j : T₀ ⟶ T)
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

local notation "P" => Standard.parabolicScheme i ν ∅
local notation "p" => Standard.parabolicHom i ν ∅
local notation "tP" => torusToStandardParabolic F G T i ν
local notation "A" => intrinsicSubgroup F T
local notation "Gₐ" => AdelicGroupPoints F G
local notation "Z" => WeightedSiegel.DomainQuotient F p

private instance : IsClosedImmersion (p).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν ∅

private instance : IsAffine (P).X.left := isAffine_of_isAffineHom (p).hom.hom.left

/-- Actual real log coordinates at a positive point of the split torus. -/
def positiveLogCoordinates (a : A) : I → ℝ :=
  dualCoordinates F T I e (characterLog F T.toGrp a.val)

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The actual positive point with a supplied vector of log coordinates, regarded as
an adelic group-valued continuous homomorphism of the additive coordinate space. -/
def positivePointOfLogCoordinates : Multiplicative (I → ℝ) →ₜ* Gₐ :=
  let c : Multiplicative (I → ℝ) →ₜ* Multiplicative (RealCharacterDual F T.toGrp) :=
    { toMonoidHom := (dualCoordinatesContinuousEquiv F T I e).symm.toLinearEquiv.toLinearMap.toAddMonoidHom.toMultiplicative
      continuous_toFun := (dualCoordinatesContinuousEquiv F T I e).symm.continuous }
  let logInv := (positiveLogEquiv F T I e).symm
  let a : Multiplicative (RealCharacterDual F T.toGrp) →ₜ* A :=
    { toMonoidHom := logInv.toMulEquiv.toMonoidHom
      continuous_toFun := logInv.continuous }
  (positivePointMap F G T i).comp (a.comp c)

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem positivePointOfLogCoordinates_apply (a : A) :
    positivePointOfLogCoordinates F i I e (Multiplicative.ofAdd (positiveLogCoordinates F I e a)) =
      positivePointMap F G T i a := by
  have hc : (dualCoordinatesContinuousEquiv F T I e).symm (positiveLogCoordinates F I e a) =
      characterLog F T.toGrp a.val :=
    (dualCoordinatesContinuousEquiv F T I e).symm_apply_apply _
  change positivePointMap F G T i ((positiveLogEquiv F T I e).symm
      (Multiplicative.ofAdd ((dualCoordinatesContinuousEquiv F T I e).symm
        (positiveLogCoordinates F I e a)))) = _
  rw [hc]
  exact congrArg (positivePointMap F G T i) ((positiveLogEquiv F T I e).symm_apply_apply a)

/-- A continuous full-height section with compact Iwasawa factors admits sufficiently
large positive log weights of finite mass on every region where the weight grows at
least linearly in the coordinate norm, up to an additive constant. -/
def AdelicMinimalIwasawaFiniteWeightStatement : Prop :=
  IsSiegelAlgebraicSetup F G T i ν T₀ j →
  ∀ (K : Subgroup Gₐ) (hK : IsIwasawaCompact p K),
    ∃ (a : RealCharacterDual F P → A) (Ω : Set (normOneSubgroup F P)),
      Continuous a ∧ IsCompact Ω ∧
      (∀ h, characterLog F P (positivePointMap F P T tP (a h)) = h) ∧
      (∀ x : Gₐ, ∃ (q : RationalGroupPoints F P), ∃ z ∈ Ω, ∃ k ∈ K,
        map F P G p (rational F P q) * x =
          map F P G p z * positivePointMap F G T i (a (hK.height x)) * k) ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ (ell : RealCharacterDual F P → ℝ) (S : Set Z), MeasurableSet S →
        ∀ b : ℝ, (∀ z ∈ S, c * ‖positiveLogCoordinates F I e (a (WeightedSiegel.domainHeight F p hK z))‖ ≤
            2 * ell (WeightedSiegel.domainHeight F p hK z) + b) →
        IsFiniteMeasure (WeightedSiegel.domainMeasure F p hK ell S)

theorem adelicMinimalIwasawaFiniteWeight :
    AdelicMinimalIwasawaFiniteWeightStatement F i ν j I e := by
  intro hsetup K hK
  obtain ⟨a, Ω, ha, hΩ, hLog, hrep⟩ := minimalIwasawaCompactRepresentatives F i ν j hsetup K hK
  refine ⟨a, Ω, ha, hΩ, hLog, hrep, ?_⟩
  let Γ := WeightedSiegel.parabolicPrincipalSubgroup F p
  let Ω' := (fun z : normOneSubgroup F P => map F P G p z) '' Ω
  have hΩ' : IsCompact Ω' := hΩ.image ((map F P G p).continuous.comp continuous_subtype_val)
  let h (z : Z) := positiveLogCoordinates F I e (a (WeightedSiegel.domainHeight F p hK z))
  have hh : Continuous h := (continuous_dualCoordinates F T I e).comp
    ((continuous_characterLog F T.toGrp).comp
      (continuous_subtype_val.comp (ha.comp (WeightedSiegel.continuous_domainHeight F p hK))))
  have hcov (z : Z) : ∃ x ∈ Ω', ∃ k ∈ K,
      LeftCosetSpace.mk Γ (x * positivePointOfLogCoordinates F i I e (Multiplicative.ofAdd (h z)) * k) = z := by
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ z
    obtain ⟨q, b, hb, k, hk, heq⟩ := hrep x
    have hq : map F P G p (rational F P q) ∈ Γ := ⟨_, ⟨q, rfl⟩, rfl⟩
    refine ⟨_, ⟨b, hb, rfl⟩, k, hk, ?_⟩
    change LeftCosetSpace.mk Γ (map F P G p b * positivePointOfLogCoordinates F i I e
      (Multiplicative.ofAdd (positiveLogCoordinates F I e (a (hK.height x)))) * k) = _
    rw [positivePointOfLogCoordinates_apply, ← heq]
    exact LeftCosetSpace.mk_subgroup_mul Γ ⟨_, hq⟩ x
  let ν₀ := WeightedSiegel.domainHaarMeasure F p
  obtain ⟨c, hc, hExp⟩ := LeftCosetSpace.leftCosetExponentialHeightMoment
    (ν := (Measure.haar : Measure Gₐ)) Γ (WeightedSiegel.isDiscrete_parabolicPrincipalSubgroup F p)
    (I → ℝ) (positivePointOfLogCoordinates F i I e) h hh.norm.measurable
    Ω' (K : Set Gₐ) hΩ' hK.isCompact hcov inferInstance
  refine ⟨c, hc, fun ell S hS b hle => ⟨?_⟩⟩
  let g (z : Z) := ENNReal.ofReal (Real.exp (-c * ‖h z‖))
  have hg : (∫⁻ z, g z ∂ν₀) < ∞ := hExp c le_rfl
  change ((ν₀.restrict S).withDensity (WeightedSiegel.domainDensity F p hK ell)) Set.univ < ∞
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hval : ∀ᵐ z ∂ν₀.restrict S,
      WeightedSiegel.domainDensity F p hK ell z ≤ ENNReal.ofReal (Real.exp b) * g z := by
    filter_upwards [ae_restrict_mem hS] with z hz
    rw [show g z = ENNReal.ofReal (Real.exp (-c * ‖h z‖)) from rfl,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := hle z hz
    change c * ‖h z‖ ≤ 2 * ell (WeightedSiegel.domainHeight F p hK z) + b at hh
    change -2 * ell (WeightedSiegel.domainHeight F p hK z) ≤ b + -c * ‖h z‖
    linarith
  refine (lintegral_mono_ae hval).trans_lt ?_
  refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt ?_
  rw [lintegral_const_mul' _ g ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg

end Langlands.Global.AdelicSiegelFactors
