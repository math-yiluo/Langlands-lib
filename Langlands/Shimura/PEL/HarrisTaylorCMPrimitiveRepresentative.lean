import Langlands.Shimura.PEL.HarrisTaylorCMOrdinaryIsomorphisms
import Langlands.Shimura.PEL.HarrisNormalizedPolarizationTransport
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationRayPositivityProof

/-! # Primitive representatives for normalized Harris polarization rays -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale

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
  (P : Prerequisites.{0})
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Z.obj.left)
  (hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "NRep" => TateNormalizedCMRepresentative D C P Z compatibility h s hs htor
local notation:max "BOf" x:max =>
  letI := auxiliaryStarRing D C
  (x).data.1.actionObj.abelianScheme
local notation:max "WOf" x:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction.dualWitness P (x).data.1
local notation:max "DOf" x:max => (WOf x).dual P
local notation:max "pol" x:max =>
  letI := auxiliaryStarRing D C
  (x).data.1.polarization

variable {U : HarrisLevel D}

/-- The selected primitive homomorphism of the normalized representative is
on its original abelian scheme and dual. -/
def tateNormalizedCMPrimitiveRepresentative (x : NRep U) :
    {mu : BOf x ⟶ DOf x //
      letI := auxiliaryStarRing D C
      HarrisPrimitivePolarization D C P x.data.1 mu} := by
  let := auxiliaryStarRing D C
  let eta := Classical.choose x.normalized
  have heta := (Classical.choose_spec x.normalized).1
  exact ⟨harrisPrimitivePolarizationOf D C P compatibility h s Z.property.torsionUnits
    x.data.1 eta heta, harrisPrimitivePolarizationOf_spec D C P compatibility h s
    Z.property.torsionUnits x.data.1 eta heta⟩

local notation:max "primitive" x:max =>
  tateNormalizedCMPrimitiveRepresentative D C P Z compatibility h s hs htor x
local notation:max "transport" x:max y:max e:max => DualWitness.transportMap P e (WOf x) (WOf y)

omit [IsCMField F] in
/-- An actual isomorphism with the original integral cross-multiple relation
identifies the two primitive homomorphisms. -/
theorem tateNormalizedCMPrimitiveRepresentative_transport
    (x y : NRep U) (e : BOf x ≅ BOf y) (q : ℚ)
    (hq : Rationalization.IntegralMultipleData (transport x y e (pol y)) (pol x) q) :
    transport x y e (primitive y).val = (primitive x).val := by
  let := auxiliaryStarRing D C
  let g := Module.finrank ℚ E * n ^ 2
  have hg : 0 < g := Nat.mul_pos Module.finrank_pos
    (pow_pos (lt_trans Nat.zero_lt_one D.rank_gt_one) 2)
  exact harrisPrimitivePolarization_pullback D C P s Z.property.torsionUnits htor
    polarizationRayPositivity x.data.1 y.data.1 e q hq g hg x.condition.2
    (primitive x).property (primitive y).property

omit [IsCMField F] in
/-- Equality of the transported primitive homomorphisms recovers a
nonzero rational multiplier and its exact integer equation for the
original polarizations. -/
theorem tateNormalizedCMPrimitiveRepresentative_originalMultiple
    (x y : NRep U) (e : BOf x ≅ BOf y)
    (he : transport x y e (primitive y).val = (primitive x).val) :
    ∃ q : ℚˣ, Nonempty
      (Rationalization.IntegralMultipleData (transport x y e (pol y)) (pol x) (q : ℚ)) := by
  let := auxiliaryStarRing D C
  have hx := (primitive x).property
  have hy := (primitive y).property
  obtain ⟨-, k, hk, hkx⟩ := hx
  obtain ⟨-, l, hl, hly⟩ := hy
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hlq : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  let q : ℚˣ := Units.mk0 ((l : ℚ) / k) (div_ne_zero hlq hkq)
  refine ⟨q, ⟨⟨(k : ℤ), (l : ℤ), Int.natCast_ne_zero.mpr hk.ne', ?_, ?_⟩⟩⟩
  · change ((l : ℤ) : ℚ) = ((k : ℤ) : ℚ) * ((l : ℚ) / k)
    rw [Int.cast_natCast, Int.cast_natCast, mul_comm (k : ℚ), div_mul_cancel₀ _ hkq]
  · have h₁ : transport x y e (pol y) = l • (primitive x).val := by
      rw [← hly, DualWitness.transportMap_nsmul, he]
    simp only [natCast_zsmul, h₁, ← hkx, smul_smul, Nat.mul_comm]

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
