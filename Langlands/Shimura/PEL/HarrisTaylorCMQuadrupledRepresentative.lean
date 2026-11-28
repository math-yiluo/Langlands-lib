import Langlands.Shimura.PEL.HarrisTaylorCMPrimitiveRepresentative
import Langlands.Shimura.PEL.HarrisPrimitiveOrdinaryDegree
import Langlands.Shimura.PEL.HarrisPolarizationRayFrames
import Langlands.Shimura.PEL.HarrisIntegralLatticeIsogeny

/-! # Normalized Harris representatives with the ordinary polarization -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open HarrisPolarizedWeilLevel
open Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A] [IsScalarTower ℚ E F]
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
  (htor : TorsionFiniteEtaleStatement.{0})
  (a : HarrisGeometricPoint Z.obj.left)

local notation "NRep" =>
  TateNormalizedCMRepresentative D C P Z compatibility h a.hom a.finiteFibers htor
local notation "PObj" =>
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    (S := Z.obj.left)
local notation:max "POf" x:max =>
  letI := auxiliaryStarRing D C
  (x).data.1
local notation:max "BOf" x:max => (POf x).actionObj.abelianScheme
local notation:max "WOf" x:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction.dualWitness P (POf x)
local notation:max "primitive" x:max =>
  tateNormalizedCMPrimitiveRepresentative D C P Z compatibility h a.hom a.finiteFibers htor x
local notation:max "quad" x:max => (4 : ℕ) • (primitive x).val
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.property.pairAdditivity
local notation "levelTransport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) a.hom a.finiteFibers htor Z.property.torsionUnits
  Z.property.pairAdditivity
local notation "K" => fun U => (hodgeLevelFunctor D C).obj U

variable {U : HarrisLevel D}

omit [IsCMField F] [IsScalarTower ℚ E F] in
private theorem exists_quadrupleScale (x : NRep U) :
    letI := auxiliaryStarRing D C
    ∃ q : ℚˣ, Rationalization.ofHom (quad x) =
      rationalUnitMultiple q (Rationalization.ofHom (POf x).polarization) := by
  let := auxiliaryStarRing D C
  obtain ⟨-, k, hk, hl⟩ := (primitive x).property
  have hkq : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  let q : ℚˣ := Units.mk0 (4 / (k : ℚ)) (div_ne_zero (by decide) hkq)
  refine ⟨q, ?_⟩
  change Rationalization.ofHom (quad x) = (q : ℚ) • Rationalization.ofHom (POf x).polarization
  apply (Rationalization.ofHom_eq_smul_iff_nonempty_integralMultipleData _ _ _).mpr
  refine ⟨⟨(k : ℤ), 4, Int.natCast_ne_zero.mpr hk.ne', ?_, ?_⟩⟩
  · change ((4 : ℤ) : ℚ) = ((k : ℤ) : ℚ) * (4 / (k : ℚ))
    rw [Int.cast_natCast, mul_comm (k : ℚ), div_mul_cancel₀ _ hkq]
    norm_num
  · rw [← hl, natCast_zsmul, show (4 : ℤ) = ((4 : ℕ) : ℤ) by decide, natCast_zsmul,
      smul_smul, smul_smul, Nat.mul_comm k 4]

private def quadrupleScale (x : NRep U) : ℚˣ :=
  Classical.choose (exists_quadrupleScale D C P Z compatibility h htor a x)

local notation "qOf" => quadrupleScale D C P Z compatibility h htor a

private abbrev quadrupledAction (x : NRep U) : PObj :=
  harrisRescalePolarization D C P (POf x) (quad x) (qOf x)
    (primitivePolarization_four_isPolarization D C P (POf x) (primitive x).val
      (primitive x).property)
    (Classical.choose_spec (exists_quadrupleScale D C P Z compatibility h htor a x))

local notation "quadrupled" => quadrupledAction D C P Z compatibility h htor a

omit [IsCMField F] [IsScalarTower ℚ E F] in
private theorem quadrupledMultiple (x : NRep U) :
    letI := auxiliaryStarRing D C
    Mult (POf x) (quadrupled x) (qOf x) (Iso.refl _) := by
  let := auxiliaryStarRing D C
  change IsRationalDualPullbackMultiple P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (POf x).hasDual (POf x).hasDual
    (POf x).geometry (POf x).geometry (POf x).inversePoincare (POf x).evaluation
    (POf x).inversePoincare (POf x).evaluation
    (Z.property.pairAdditivity (POf x) (quadrupled x)) (qOf x : ℚ) (id0 (BOf x))
    (Rationalization.ofHom (POf x).polarization) (Rationalization.ofHom (quad x))
  rw [IsRationalDualPullbackMultiple, rationalDualPullbackHom0_id]
  exact Classical.choose_spec (exists_quadrupleScale D C P Z compatibility h htor a x)

local notation "multOf" => quadrupledMultiple D C P Z compatibility h htor a

/-- On the original family, replace the polarization by four times its
primitive homomorphism and carry the actual level by the identity isogeny. -/
def tateNormalizedCMQuadrupledRepresentative
    (hK : (K U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (x : NRep U) : NRep U := by
  let := auxiliaryStarRing D C
  let y := quadrupled x
  let e : (POf x).actionObj ≅ y.actionObj := Iso.refl _
  let z := levelTransport (POf x) y (K U) (qOf x) e (multOf x) x.data.2
  refine { data := ⟨y, z⟩, condition := x.condition, restriction := ?_, normalized := ?_ }
  · exact ⟨x.restriction.action, x.restriction.agrees⟩
  · apply (harrisIntegralLevelCondition_isogeny_iff D C P compatibility h a.hom
      Z.property.pairAdditivity a.finiteFibers htor Z.property.torsionUnits
      (POf x) y (K U) hK (qOf x) e (multOf x) x.data.2).mpr
    have hLat := (harrisIntegralLevelCondition_iff_lattice D C P compatibility h a.hom
      a.finiteFibers htor Z.property.torsionUnits (POf x) _ hK x.data.2).mp x.normalized
    intro w
    change w ∈ (harrisIntegralLevelLattice D C P compatibility h a.hom a.finiteFibers htor
        Z.property.torsionUnits (POf x) (K U) hK x.data.2 : Set _) ↔
      ∃ b : GroupScheme.Tate.Full (BOf x).toGrp (Over.mk a.hom),
        Tate.rationalHomMap (Over.mk a.hom) (fun _ => True) (Rationalization.identity (BOf x))
          (GroupScheme.Tate.toRational (BOf x).toGrp (Over.mk a.hom) (fun _ => True) b) = w
    rw [hLat, Tate.rationalHomMap_identity]
    rfl

local notation "rescaled" =>
  tateNormalizedCMQuadrupledRepresentative D C P Z compatibility h htor a

omit [IsCMField F] [IsScalarTower ℚ E F] in
/-- The rescaled representative has the prescribed square degree on its
literal polarization. -/
theorem tateNormalizedCMQuadrupledRepresentative_degree
    {d : ℕ} (hd : HarrisPrimitiveOrdinaryDegreeUniform D C P compatibility h d)
    (hK : (K U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (x : NRep U) :
    letI := auxiliaryStarRing D C
    HasDegreeSquare (POf (rescaled hK x)).polarization d := by
  let := auxiliaryStarRing D C
  let := harrisCMGeometricPoint_charZero D C P Z a
  let eta := Classical.choose x.normalized
  exact hd Z.obj.left a.Ω a.hom Z.property.torsionUnits (POf x) eta
    (Classical.choose_spec x.normalized).1 (primitive x).val (primitive x).property

omit [IsCMField F] [IsScalarTower ℚ E F] in
/-- This change stays in the original ordinary equivalence class and uses the
identity of the original abelian scheme as its actual isomorphism. -/
theorem tateNormalizedCMQuadrupledRepresentative_ordinaryRelated
    (hK : (K U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) (x : NRep U) :
    TateNormalizedCMOrdinaryRelated D C P Z compatibility h a.hom a.finiteFibers htor
      x (rescaled hK x) := by
  let := auxiliaryStarRing D C
  let y := rescaled hK x
  let g : BOf x ≅ BOf y := Iso.refl _
  have hg (r : D.harrisHodgePELIntegralOrder C) :
      (x.restriction.action r).asHom ≫ g.hom = g.hom ≫ (y.restriction.action r).asHom := by
    change (x.restriction.action r).asHom ≫ 𝟙 _ = 𝟙 _ ≫ (x.restriction.action r).asHom
    rw [Category.comp_id, Category.id_comp]
  let e := tateNormalizedCMOrdinaryRationalIso D C P Z compatibility h
    a.hom a.finiteFibers htor x y g hg
  have he : e = Iso.refl _ := by
    apply Iso.ext
    apply RationalAlgebraAction.hom_ext
    rfl
  have hm : Mult (POf x) (POf y) (qOf x) e := he.symm ▸ multOf x
  let hm' := (tateNormalizedCMOrdinary_multiple_iff D C P Z compatibility h
    a.hom a.finiteFibers htor x y (qOf x) g hg).mp hm
  refine ⟨qOf x, g, hg, hm', ?_⟩
  have hlevel (v : (POf x).actionObj ≅ (POf y).actionObj)
      (hv : Mult (POf x) (POf y) (qOf x) v) (h : v = Iso.refl _) :
      levelTransport (POf x) (POf y) (K U) (qOf x) v hv x.data.2 = y.data.2 := by
    subst v
    rfl
  exact hlevel e hm he

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
