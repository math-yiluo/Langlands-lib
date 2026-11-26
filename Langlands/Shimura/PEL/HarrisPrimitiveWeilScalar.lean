import Langlands.Shimura.PEL.HarrisPrimitiveSourceForm
import Langlands.AbelianScheme.Tate.FullTwistBasis
import Langlands.AbelianScheme.Tate.WeilIntegralPerfectness
import Langlands.AbelianScheme.Tate.WeilAlongHom0

/-! # The integral similitude of the primitive Harris Weil form -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Global
open Global.RationalProfiniteIntegerAdeleComparison (integralEquiv)
open GroupScheme.Tate (Index)

local notation "PAll" => (fun _ : ℕ => True)
local notation "Af" => FiniteAdeles ℚ
local notation "Rf" => integralFiniteAdeles ℚ
local notation "ZR" => ProfiniteIntegerRing

private theorem isUnit_of_prime_reduction_ne_zero (a : ZR)
    (h : ∀ p : Nat.Primes, ProfiniteIntegerRing.reduction ⟨p.val, p.property.pos⟩ a ≠ 0) :
    IsUnit a := by
  let (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩
  let e := TateAdelicRank.fullScalarEquiv
  have hu : IsUnit (e a) := by
    apply Pi.isUnit_iff.mpr
    intro p
    by_contra hp
    have hm : e a p ∈ IsLocalRing.maximalIdeal (PadicInt p.val) :=
      (IsLocalRing.mem_maximalIdeal _).mpr hp
    have hz : PadicInt.toZModPow 1 (e a p) = 0 := by
      apply RingHom.mem_ker.mp
      rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p]
      exact hm
    change PadicInt.toZModPow 1 (ProfiniteIntegerRing.toPadic p a) = 0 at hz
    rw [ProfiniteIntegerRing.toZModPow_toPadic] at hz
    have hm' : ProfiniteIntegerRing.primePowerModulus p 1 = ⟨p.val, p.property.pos⟩ :=
      Subtype.ext (pow_one p.val)
    have hz' : (fun m : ℕ+ => ProfiniteIntegerRing.reduction m a = 0)
        (ProfiniteIntegerRing.primePowerModulus p 1) := hz
    exact h p (hm' ▸ hz')
  exact e.symm_apply_apply a ▸ hu.map e.symm.toRingHom

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0}) {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (s : Spec (.of Ω) ⟶ S)

local notation "T" => Over.mk s
local notation "R" => Γ((Over.mk s).left, ⊤)
local notation "Vf" => Af ⊗[ℚ] A
local notation "L" => D.harrisHodgePELIntegralLattice C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "prim" => D.harrisHodgePELPrimitiveAdelicForm C
local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (S := S)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "DOf" X:max =>
  letI := auxiliaryStarRing D C
  dualAbelianSchemeFromEvaluation (BOf X) (X).hasDual (X).geometry P.preservation
    (X).inversePoincare (X).evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry
local notation:max "ActionOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.action
local notation:max "polOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).polarization
local notation:max "Full" X:max => GroupScheme.Tate.Full (BOf X).toGrp T
local notation:max "toRat" X:max => GroupScheme.Tate.toRational (BOf X).toGrp T PAll
local notation:max "Rat" X:max => GroupScheme.Tate.RationalFull (BOf X).toGrp T
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation "AdeleAlong" X:max =>
  letI := auxiliaryStarRing D C
  adelicWeilAlongHomBilinearMap P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility T
local notation "IntAlong" X:max =>
  letI := auxiliaryStarRing D C
  integralWeilAlongHomBilinearMap P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility T
local notation "IntBasis" => TateTwist.Divisibility.geometricFullIntegralBasis Ω
local notation "AdeleBasis" => TateTwist.Divisibility.finiteAdeleBasisOf h (IntBasis)

omit [IsAlgClosed Ω] [CharZero Ω] in
private theorem adelicWeilAlong_nsmul (X : PObj) (mu : BOf X ⟶ DOf X)
    (k : ℕ) (v w : Rat X) :
    let := TateTwist.Divisibility.finiteAdeleModule R PAll h
    (AdeleAlong X) (k • mu) PAll h v w =
      (algebraMap ℚ Af (k : ℚ)) • (AdeleAlong X) mu PAll h v w := by
  let := auxiliaryStarRing D C
  let := TateTwist.Divisibility.finiteAdeleModule R PAll h
  change (AdeleAlong X) (k • mu) PAll h v w =
    TateTwist.Divisibility.finiteAdeleAction R PAll h (algebraMap ℚ Af (k : ℚ))
      ((AdeleAlong X) mu PAll h v w)
  rw [TateTwist.Divisibility.finiteAdeleAction_diagonal,
    adelicWeilAlongHomBilinearMap_apply, adelicWeilAlongHomBilinearMap_apply,
    ← rationalWeilAlongHom0BilinearMap_ofHom, ← rationalWeilAlongHom0BilinearMap_ofHom]
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, rationalWeilAlongHom0BilinearMap_smul]

omit [IsAlgClosed Ω] [CharZero Ω] in
private theorem adelicWeilAlong_toRational (X : PObj) (mu : BOf X ⟶ DOf X)
    (v w : Full X) :
    (AdeleAlong X) mu PAll h ((toRat X) v) ((toRat X) w) =
      TateTwist.Divisibility.toRational R PAll ((IntAlong X) mu PAll v w) := by
  rw [adelicWeilAlongHomBilinearMap_apply, rationalWeilAlongHomBilinearMap_toRational]

include s in
/-- A primitive homomorphism in a normalized Harris polarization ray has
an integral multiplier relative to the fixed primitive source form. -/
theorem harrisPrimitiveWeil_exists_integralScalar (X : PObj) (eta : Frame X)
    (hn : Normalized X eta) (mu : BOf X ⟶ DOf X)
    (hmu : HarrisPrimitivePolarization D C P X mu) :
    let := TateTwist.Divisibility.finiteAdeleModule R PAll h
    ∃ r : Rf, ∀ v w : Vf, (AdeleAlong X) mu PAll h (eta.1 v) (eta.1 w) =
      AdeleBasis ((r : Af) * prim v w) := by
  let := auxiliaryStarRing D C
  let := TateTwist.Divisibility.finiteAdeleModule R PAll h
  let := scalarExtensionAlgebraModule A A Af
  let := GroupScheme.Tate.finiteAdeleModule (BOf X).toGrp T PAll h
  let := Tate.finiteAdeleAlgebraModule (BOf X) T PAll h (ActionOf X)
  let e : Af ≃ₗ[Af] TateTwist.Divisibility.RationalFull R := AdeleBasis
  obtain ⟨a, ha⟩ := (formCompatible_iff ((D.harrisHodgePELForm C).baseChange Af)
    ((AdeleAlong X) (polOf X) PAll h) eta.1 e).mp eta.2
  obtain ⟨-, k, hk, hpol⟩ := hmu
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  let inverse := algebraMap ℚ Af (k : ℚ)⁻¹
  let r := inverse * (a : Af) * algebraMap ℚ Af (D.harrisHodgePELPairingContent C : ℚ)
  have hr (v w : Vf) : (AdeleAlong X) mu PAll h (eta.1 v) (eta.1 w) =
      e (r * prim v w) := by
    have hpol' := congrArg
      (fun p : BOf X ⟶ DOf X => (AdeleAlong X) p PAll h (eta.1 v) (eta.1 w)) hpol
    have hscale := hpol'.symm.trans (adelicWeilAlong_nsmul D C P compatibility h s
      X mu k (eta.1 v) (eta.1 w))
    calc
      _ = inverse • (AdeleAlong X) (polOf X) PAll h (eta.1 v) (eta.1 w) := by
        rw [hscale, smul_smul, show inverse * algebraMap ℚ Af (k : ℚ) = 1 by
            dsimp only [inverse]
            rw [← map_mul, inv_mul_cancel₀ hkQ, map_one], one_smul]
      _ = inverse • e ((a : Af) * (D.harrisHodgePELForm C).baseChange Af v w) :=
        congrArg (inverse • ·) (ha v w)
      _ = e (r * prim v w) := by
        rw [← e.map_smul, smul_eq_mul, ← D.harrisHodgePELPrimitiveAdelicForm_mul C v w]
        simp only [r, mul_assoc]
  have hi (v w : Vf) (hv : v ∈ Λf) (hw : w ∈ Λf) : r * prim v w ∈ Rf := by
    obtain ⟨x, hx⟩ := (hn v).mp hv
    obtain ⟨y, hy⟩ := (hn w).mp hw
    obtain ⟨b, hb⟩ := (IntBasis).surjective ((IntAlong X) mu PAll x y)
    have hval : e (r * prim v w) = e (integralEquiv h b : Af) := by
      rw [← hr, ← hx, ← hy, adelicWeilAlong_toRational D C P compatibility h s, ← hb]
      exact (TateTwist.Divisibility.finiteAdeleBasisOf_integral h (IntBasis) b).symm
    rw [e.injective hval]
    exact (integralEquiv h b).property
  let J := ((Rf).toAddSubgroup.toIntSubmodule).comap (LinearMap.toSpanSingleton ℤ Af r)
  have hspan : Submodule.span ℤ (Set.range
      (fun p : L × L => D.harrisHodgePELPrimitivePairing C p.1 p.2)) ≤ J := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have hx := D.harrisHodgePELIntegralAdeleSpan_tmul C x
    have hy := D.harrisHodgePELIntegralAdeleSpan_tmul C y
    have hab := hi _ _ hx hy
    rw [D.harrisHodgePELPrimitiveAdelicForm_tmul C x y] at hab
    change (D.harrisHodgePELPrimitivePairing C x y : ℤ) • r ∈ Rf
    rw [zsmul_eq_mul, mul_comm]
    exact hab
  have h1 : (1 : ℤ) ∈ J := by
    apply hspan
    rw [show Submodule.span ℤ (Set.range
      (fun p : L × L => D.harrisHodgePELPrimitivePairing C p.1 p.2)) =
      (⊤ : Submodule ℤ ℤ) from D.harrisHodgePELPrimitivePairing_span C]
    trivial
  change (1 : ℤ) • r ∈ Rf at h1
  rw [one_smul] at h1
  exact ⟨⟨r, h1⟩, hr⟩

section Primitive

variable [IsLocallyNoetherian S] [ConnectedSpace S]
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index PAll, IsUnit (k.val : Γ(S, ⊤)))

include htor hu in
/-- Primitivity of the dual-valued homomorphism makes its integral
multiplier a unit. -/
theorem harrisPrimitiveWeil_isUnit (X : PObj) (eta : Frame X)
    (hn : Normalized X eta) (mu : BOf X ⟶ DOf X) (hmu : Tate.IsPrimitiveHom mu)
    (r : Rf) (hr : ∀ v w : Vf, (AdeleAlong X) mu PAll h (eta.1 v) (eta.1 w) =
      AdeleBasis ((r : Af) * prim v w)) :
    IsUnit r := by
  let := auxiliaryStarRing D C
  let := TateTwist.Divisibility.finiteAdeleModule R PAll h
  let e : Af ≃ₗ[Af] TateTwist.Divisibility.RationalFull R := AdeleBasis
  suffices hunit : IsUnit ((integralEquiv h).symm r) by
    have hu' := hunit.map (integralEquiv h).toRingHom
    change IsUnit (integralEquiv h ((integralEquiv h).symm r)) at hu'
    exact (integralEquiv h).apply_symm_apply r ▸ hu'
  apply isUnit_of_prime_reduction_ne_zero
  intro p hp
  let N : Index PAll := ⟨p.val, p.property.pos, trivial⟩
  obtain ⟨u, hru⟩ := (harrisIntegralAdeleResidue_eq_zero_iff h
    ⟨p.val, p.property.pos⟩ r).mp hp
  change (p.val : Rf) * u = r at hru
  have hdiv (x y : Full X) :
      ∃ z, (IntAlong X) mu PAll x y = p.val • z := by
    obtain ⟨v, hv⟩ := eta.1.surjective ((toRat X) x)
    obtain ⟨w, hw⟩ := eta.1.surjective ((toRat X) y)
    have hv' := (hn v).mpr ⟨x, hv.symm⟩
    have hw' := (hn w).mpr ⟨y, hw.symm⟩
    let a : Rf := ⟨prim v w, D.harrisHodgePELPrimitiveAdelicForm_mem C hv' hw'⟩
    let z := (integralEquiv h).symm (u * a)
    refine ⟨(IntBasis) z, ?_⟩
    apply TateTwist.Divisibility.full_toRational_injective
    rw [map_nsmul, ← adelicWeilAlong_toRational D C P compatibility h s,
      ← hv, ← hw, hr]
    have heInt : e (integralEquiv h z : Af) =
        TateTwist.Divisibility.toRational R PAll ((IntBasis) z) :=
      TateTwist.Divisibility.finiteAdeleBasisOf_integral h (IntBasis) z
    change e ((r : Af) * prim v w) =
      p.val • TateTwist.Divisibility.toRational R PAll ((IntBasis) z)
    rw [← heInt, ← map_nsmul e]
    apply congrArg e
    have he : r * a = (p.val : Rf) * integralEquiv h z := by
      dsimp only [z]
      rw [RingEquiv.apply_symm_apply, ← mul_assoc, hru]
    rw [nsmul_eq_mul]
    simpa only [Subring.coe_mul, Subring.coe_natCast] using
      congrArg (fun a : Rf => (a : Af)) he
  have hzero : ∀ y : GroupScheme.Tate.Level (BOf X).toGrp T N.val,
      GroupScheme.Tate.levelMap T (groupHom mu) N.val y = 0 := by
    intro y
    obtain ⟨y', rfl⟩ := Tate.full_evaluation_surjective_at hu (BOf X) s N y
    obtain ⟨z, hz⟩ := integralWeil_exists_nsmul_of_forall P.preservation
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry
      P.stability X.hasDual X.inversePoincare X.evaluation compatibility P.square
      P.universality X.geometry hu s N (GroupScheme.Tate.map T PAll (groupHom mu) y')
      (fun x => hdiv x y')
    rw [← GroupScheme.Tate.evaluation_map, ← hz, map_nsmul]
    exact GroupScheme.Tate.level_nsmul_eq_zero (DOf X).toGrp T N.val _
  obtain ⟨g, hg⟩ :=
    (Tate.exists_nsmul_eq_iff_levelMap_eq_zero htor hu s mu p.property.pos).mpr hzero
  exact p.property.ne_one (hmu p.val g hg)

include htor hu in
/-- The unit-valued comparison is on the original normalized frame of the
polarized action. The primitive homomorphism and fixed source use the same
integral Tate module. -/
theorem harrisPrimitiveWeil_exists_unit (X : PObj) (eta : Frame X)
    (hn : Normalized X eta) (mu : BOf X ⟶ DOf X)
    (hmu : HarrisPrimitivePolarization D C P X mu) :
    ∃ r : Rfˣ, ∀ v w : Vf, (AdeleAlong X) mu PAll h (eta.1 v) (eta.1 w) =
      AdeleBasis (((r.val : Rf) : Af) * prim v w) := by
  obtain ⟨r, hr⟩ := harrisPrimitiveWeil_exists_integralScalar D C P compatibility h s
    X eta hn mu hmu
  obtain ⟨u, rfl⟩ := harrisPrimitiveWeil_isUnit D C P compatibility h s htor hu
    X eta hn mu hmu.1 r hr
  exact ⟨u, hr⟩

include htor hu in
/-- The integral similitude multiplier relative to the chosen full Tate
twist basis and the fixed primitive Harris source form. -/
def harrisPrimitiveWeilUnit (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (mu : BOf X ⟶ DOf X) (hmu : HarrisPrimitivePolarization D C P X mu) : Rfˣ :=
  Classical.choose (harrisPrimitiveWeil_exists_unit D C P compatibility h s htor hu
    X eta hn mu hmu)

include htor hu in
theorem harrisPrimitiveWeilUnit_spec (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (mu : BOf X ⟶ DOf X) (hmu : HarrisPrimitivePolarization D C P X mu) (v w : Vf) :
    (AdeleAlong X) mu PAll h (eta.1 v) (eta.1 w) =
      AdeleBasis ((((harrisPrimitiveWeilUnit D C P compatibility h s htor hu X eta hn mu hmu).val
        : Rf) : Af) * prim v w) :=
  Classical.choose_spec (harrisPrimitiveWeil_exists_unit D C P compatibility h s htor hu
    X eta hn mu hmu) v w

/-- A primitive source pairing value regarded in the actual integral adeles. -/
def harrisPrimitiveSourceAdeleValue (v w : Λf) : Rf :=
  ⟨prim (v : Vf) (w : Vf), D.harrisHodgePELPrimitiveAdelicForm_mem C v.property w.property⟩

include htor hu in
/-- For any natural multiple of the primitive homomorphism, the comparison
on integral Tate vectors is the original integral twist basis applied to the
same multiple of the rescaled source pairing value. -/
theorem harrisPrimitiveWeilUnit_integralAlong_nsmul
    (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (mu : BOf X ⟶ DOf X) (hmu : HarrisPrimitivePolarization D C P X mu)
    (a : ℕ) (v w : Λf) :
    (IntAlong X) (a • mu) PAll
      (harrisIntegralFrameFull D C P compatibility h s X eta hn v)
      (harrisIntegralFrameFull D C P compatibility h s X eta hn w) =
      (IntBasis) ((integralEquiv h).symm ((a : Rf) *
        (harrisPrimitiveWeilUnit D C P compatibility h s htor hu X eta hn mu hmu).val *
        harrisPrimitiveSourceAdeleValue D C v w)) := by
  let := auxiliaryStarRing D C
  let := TateTwist.Divisibility.finiteAdeleModule R PAll h
  let e : Af ≃ₗ[Af] TateTwist.Divisibility.RationalFull R := AdeleBasis
  let r := harrisPrimitiveWeilUnit D C P compatibility h s htor hu X eta hn mu hmu
  let z := (integralEquiv h).symm ((a : Rf) * r.val * harrisPrimitiveSourceAdeleValue D C v w)
  apply TateTwist.Divisibility.full_toRational_injective
  rw [← adelicWeilAlong_toRational D C P compatibility h s,
    harrisIntegralFrameFull_toRational, harrisIntegralFrameFull_toRational,
    adelicWeilAlong_nsmul D C P compatibility h s,
    harrisPrimitiveWeilUnit_spec D C P compatibility h s htor hu X eta hn mu hmu]
  change (algebraMap ℚ Af (a : ℚ)) • e ((r.val : Af) * prim (v : Vf) (w : Vf)) =
    TateTwist.Divisibility.toRational R PAll ((IntBasis) z)
  refine (e.map_smul (algebraMap ℚ Af (a : ℚ)) _).symm.trans ?_
  refine (congrArg e ?_).trans (TateTwist.Divisibility.finiteAdeleBasisOf_integral h (IntBasis) z)
  dsimp only [z]
  rw [RingEquiv.apply_symm_apply, Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast,
    map_natCast, smul_eq_mul, mul_assoc]
  rfl

end Primitive

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
