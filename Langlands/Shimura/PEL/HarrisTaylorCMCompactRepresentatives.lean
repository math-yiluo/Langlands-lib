import Langlands.Shimura.PEL.HarrisTaylorCMCompactTateNormalization
import Langlands.Shimura.PEL.HarrisCompactOrbitLatticeTransport
import Langlands.Shimura.PEL.HarrisTaylorCMUniversalClass
import Langlands.Shimura.PEL.HarrisTaylorCMTateGeometricFamilies

/-! # Compact Tate-normalized representatives of connected CM classes -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

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
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "BaseProperty" Z:max => AdmissibleCMBase D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (Z).obj
local notation "baseProperty" Z:max => ((Z).property : BaseProperty Z)
local notation "DataAt" Z:max a:max U:max =>
  HarrisLevelData D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h (a).hom (a).finiteFibers htor (baseProperty Z).torsionUnits U
local notation "Good" Z:max => PositiveObjectCondition D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C (Z).obj.hom)
local notation "Numerical" Z:max => HarrisNumericalWeilLevel.NumericalObjectCondition D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality L (Z).obj.hom
local notation "Normalized[" Z ", " a ", " U "]" =>
  HarrisCompactTateNormalized D C P Z compatibility h (a).hom (a).finiteFibers htor (U := U)
local notation "classOfAt[" Z ", " a ", " U "]" => HarrisNumericalWeilLevel.classOf D C hΦ
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality (D.harrisTaylorReflexStructure C (Z).obj.hom)
  compatibility h (a).hom (a).finiteFibers htor (baseProperty Z).torsionUnits
  (baseProperty Z).pairAdditivity L (Z).obj.hom (U := U)
local notation "classesAt[" Z ", " a "]" => geometricClassTower D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (Z).obj.hom compatibility h htor (baseProperty Z).torsionUnits
  (baseProperty Z).pairAdditivity a
local notation "tower" => unpointedClassTower D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality compatibility h htor
local notation "fibreAt" a:max => fiberFunctor (HarrisGeometricPoint.hom a)
  (HarrisGeometricPoint.finiteFibers a)

/-- A representative at one point satisfying the determinant, dimension and compact
Tate lattice conditions on the original Harris level data. -/
structure CompactTateCMRepresentative (S : Bases) (a : HarrisGeometricPoint S.obj.left)
    (U : HarrisLevel D) where
  data : DataAt S a U
  good : (Good S) data.1
  numerical : (Numerical S) data.1
  normalized : Normalized[S, a, U] data

local notation "Rep" => CompactTateCMRepresentative D C P compatibility h htor

local notation "classAt[" Z ", " z ", " U "]" x:max =>
  classOfAt[Z, z, U] (x).data (x).good (x).numerical

local notation "moveData[" S₀ "]" => HarrisTaylorLieWeilLevel.pointMapRepresentative D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
  P.stability P.square P.universality compatibility h htor (baseProperty S₀).torsionUnits

set_option maxHeartbeats 4800000 in
/-- Geometric point transport preserves compact Tate normalization on the
same polarized object. -/
theorem compactTateCMPointMap_normalized {S : Bases} {a b : HarrisGeometricPoint S.obj.left}
    {U : HarrisLevel D} (x : Rep S a U) (p : fibreAt a ≅ fibreAt b) :
    Normalized[S, b, U] (moveData[S] p U x.data) := by
  exact (harrisCompactOrbitLatticeCondition_point D C P compatibility h htor
    (baseProperty S).torsionUnits x.data.1 p ((hodgeLevelFunctor D C).obj U) x.data.2).mpr
    x.normalized

set_option maxHeartbeats 1600000 in
/-- The original pointed class admits a compact Tate-normalized representative
on the same admissible base. -/
theorem exists_compactTateCMRepresentative {U : HarrisLevel D} (S : Bases) (a : HarrisGeometricPoint S.obj.left)
    (q : (classesAt[S, a]).obj U) : ∃ x : Rep S a U, (classAt[S, a, U] x) = q := by
  let := auxiliaryStarRing D C
  let := harrisCMGeometricPoint_charZero D C P S a
  obtain ⟨x, hx, hn, rfl⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability P.square P.universality (D.harrisTaylorReflexStructure C S.obj.hom)
    compatibility h a.hom a.finiteFibers htor (baseProperty S).torsionUnits
    (baseProperty S).pairAdditivity L S.obj.hom (U := U) q
  let joint := determinantDimensionCondition_iff D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
    S.obj.hom
  have hc := (joint x.1).mpr ⟨hx, hn⟩
  obtain ⟨y, hy, hyTate, hyq⟩ := exists_harrisCompactTateNormalized D C P S compatibility h
    a.hom a.finiteFibers htor (U := U) x hc
  let r : Rep S a U :=
    { data := y
      good := ((joint y.1).mp hy).1
      numerical := ((joint y.1).mp hy).2
      normalized := hyTate }
  exact ⟨r, hyq⟩

set_option maxHeartbeats 4800000 in
/-- Transport of a normalized representative along any path from its anchor
point represents the value of the unpointed class at the new point. -/
theorem compactTateCMPointMap_pointedClass {S : Bases} {a b : HarrisGeometricPoint S.obj.left}
    {U : HarrisLevel D} (x : Rep S a U) (v : (tower S).obj U) (hr : (classAt[S, a, U] x) = v.val a)
    (p : fibreAt a ≅ fibreAt b) : classOfAt[S, b, U] (moveData[S] p U x.data) x.good x.numerical = v.val b :=
  let e : (classesAt[S, a]) ≅ (classesAt[S, b]) :=
    geometricClassComparison D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality S.obj.hom
    compatibility h htor (baseProperty S).torsionUnits (baseProperty S).pairAdditivity
    a b
  let hp : e.hom.app U (classAt[S, a, U] x) = classOfAt[S, b, U] (moveData[S] p U x.data) x.good x.numerical :=
    congrArg (fun (i : (classesAt[S, a]) ≅ (classesAt[S, b])) => i.hom.app U (classAt[S, a, U] x))
      (classGeometricPointTowerIso_eq_path D C P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability P.square P.universality S.obj.hom
        compatibility h htor (baseProperty S).torsionUnits (baseProperty S).pairAdditivity p)
  let hv : e.hom.app U (v.val a) = v.val b := v.property a b
  hp.symm.trans ((congrArg (e.hom.app U) hr).trans hv)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
