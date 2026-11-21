import Langlands.Shimura.PEL.HarrisTaylorCMIntegralNormalSublevel
import Langlands.Shimura.PEL.HarrisIntegralCongruenceCofinality

/-! # Reduction of ordinary Harris representability to principal levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel (Prerequisites)
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (h : Global.RationalProfiniteIntegerAdeleComparison)

local notation "G" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U
local notation "Cong" => harrisIntegralAdeleCongruence D C
local notation "Stab" => (harrisIntegralAdeleStabilizer D C : Subgroup G)

omit [IsCMField F] [IsScalarTower ℚ F A] in
include h in
/-- A source-stabilizing original small level has a relative normal small
refinement whose transported subgroup is principal of modulus divisible by `M`. -/
theorem exists_smallCMPrincipalNormalSublevel (U : SmallCMLevel D)
    (hU : (lev U.obj).toSubgroup ≤ Stab) (M : ℕ+) :
    ∃ (V : SmallCMLevel D) (m : ℕ+), M.val ∣ m.val ∧ V.obj.subgroup ≤ U.obj.subgroup ∧
      (V.obj.subgroup.subgroupOf U.obj.subgroup).Normal ∧
      (lev V.obj).toSubgroup = Cong m.val := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let e := D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
  obtain ⟨k, hk⟩ := exists_harrisIntegralAdeleCongruence_le D C h (lev U.obj).openSubgroup
  let m := k * M
  have hk' : Cong m.val ≤ (lev U.obj).toSubgroup :=
    (harrisIntegralAdeleCongruence_le_of_dvd D C (dvd_mul_right k.val M.val)).trans hk
  let H := (harrisIntegralAdeleOpenCongruence D C m.val m.property.ne').comap
    e.toMonoidHom e.continuous
  have hle : H.toSubgroup ≤ U.obj.subgroup := fun g hg =>
    (hodgeLevelFunctor_obj_mem D C U.obj g).mp (hk' hg)
  let W : HarrisLevel D := ⟨H, U.obj.isCompact.of_isClosed_subset H.isClosed hle⟩
  let V : SmallCMLevel D := ⟨W, U.property.mono hle⟩
  have hV : (lev V.obj).toSubgroup = Cong m.val := by
    ext g
    obtain ⟨u, rfl⟩ := e.surjective g
    exact (hodgeLevelFunctor_obj_mem D C W u).trans Iff.rfl
  refine ⟨V, m, dvd_mul_left M.val k.val, hle, ?_, hV⟩
  constructor
  intro x hx g
  have hxK : e x.val ∈ Cong m.val := hx
  have hgS : e g.val ∈ Stab := hU ((hodgeLevelFunctor_obj_mem D C U.obj g.val).mpr g.property)
  let xS : Stab := ⟨e x.val, harrisIntegralAdeleCongruence_le D C m.val hxK⟩
  let gS : Stab := ⟨e g.val, hgS⟩
  have hc := (harrisIntegralAdeleCongruence_normal D C m.val).conj_mem xS hxK gS
  change e (g.val * x.val * g.val⁻¹) ∈ Cong m.val
  rw [map_mul, map_mul, map_inv]
  exact hc

variable (P : Prerequisites.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "OrdinaryQP" => CMOrdinaryQuasiProjectiveRepresentation D C P
  dualityNaturality compatibility h htor
local notation "NormalQuotient" => CMQuasiProjectiveNormalQuotientStatement D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality dualityNaturality P.polarizationBaseChange compatibility h htor
local notation "NormalSublevel" => DivisionCMNormalSublevelRepresentabilityStatement D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality dualityNaturality P.polarizationBaseChange compatibility h htor

/-- Ordinary quasi-projective representability at small principal levels of
modulus divisible by the prescribed positive integer `M`, in the division case. -/
def DivisionCMPrincipalOrdinaryRepresentabilityStatement (M : ℕ+) : Prop :=
  D.IsDivision → ∀ (U : SmallCMLevel D) (m : ℕ+), M.val ∣ m.val →
    (lev U.obj).toSubgroup = Cong m.val →
    ∀ hU : (lev U.obj).toSubgroup ≤ Stab, Nonempty (OrdinaryQP U hU)

/-- It suffices to construct ordinary representers at the principal levels:
first take a stabilizing normal refinement, then a principal normal refinement
of that level, and use the normal quotient premise for the inner step. -/
theorem divisionCMNormalSublevelRepresentabilityStatement_of_principalOrdinary
    {M : ℕ+} (hq : NormalQuotient)
    (hp : DivisionCMPrincipalOrdinaryRepresentabilityStatement
      D C h P dualityNaturality compatibility htor M) : NormalSublevel := by
  intro hD U
  obtain ⟨W, hWU, hWnorm, hWstab⟩ := exists_smallCMNormalSublevel_le_hodgeOpenSubgroup D C U
    (harrisIntegralAdeleOpenStabilizer D C)
  obtain ⟨V, m, hdiv, hVW, hVnorm, hVprin⟩ :=
    exists_smallCMPrincipalNormalSublevel D C h W hWstab M
  have hVstab : (lev V.obj).toSubgroup ≤ Stab := by
    rw [hVprin]
    exact harrisIntegralAdeleCongruence_le D C m.val
  obtain ⟨R⟩ := hp hD V m hdiv hVprin hVstab
  refine ⟨W, hWU, hWnorm, hq V W hVW hVnorm ?_⟩
  exact ⟨R.toQuasiProjective D C P dualityNaturality compatibility h htor⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
