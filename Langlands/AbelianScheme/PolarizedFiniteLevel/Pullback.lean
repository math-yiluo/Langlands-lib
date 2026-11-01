import Langlands.AbelianScheme.PolarizedFiniteLevel.Presentation
import Langlands.AbelianScheme.PolarizedFiniteLevel.DualWitnessBaseChange
import Langlands.AbelianScheme.PolarizedFiniteLevel.LevelCoherence
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeCoherence

/-! # Constructed pullback of actual polarized finite-level data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules GroupScheme.Tate

variable (P : Prerequisites.{u}) {S S' S'' : Scheme.{u}} {A B : AbelianScheme S}

/-- Derive all changed-dual witnesses from the particular original datum.
No dual-existence or inverse-existence assertion for arbitrary abelian schemes
is an input to this construction. -/
def DualWitness.pullback (W : DualWitness A) (b : S' ⟶ S) :
    DualWitness ((baseChange b).obj A) where
  hasDual := hasDualScheme_baseChange P.universality b A W.hasDual
  geometry := dualSchemeGeometry_baseChange P.universality b A W.hasDual W.geometry _
  inverseBundle := dualWitnessBaseChangeInverseBundle P.universality b A W.hasDual W.inverseBundle
  evaluation := dualWitnessBaseChangeEvaluation P.universality b A W.hasDual W.inverseBundle
    P.preservation W.evaluation

/-- The existing canonical actual dual base-change comparison with a specified
changed presentation. -/
def DualWitness.baseChangeIso (W : DualWitness A) (b : S' ⟶ S)
    (W' : DualWitness ((baseChange b).obj A)) :
    (baseChange b).obj (W.dual P) ≅ W'.dual P :=
  dualAbelianBaseChangeIso P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality P.compatibility b A
    W.hasDual W.geometry W.inverseBundle W.evaluation
    W'.hasDual W'.geometry W'.inverseBundle W'.evaluation

/-- Pull back an actual dual-valued map by the actual scheme pullback and the
canonical dual comparison. -/
def DualWitness.pullbackMap (W : DualWitness A) (b : S' ⟶ S)
    (W' : DualWitness ((baseChange b).obj A)) (lam : A ⟶ W.dual P) :
    (baseChange b).obj A ⟶ W'.dual P :=
  (baseChange b).map lam ≫ (W.baseChangeIso P b W').hom

/-- The underlying actual parameter map is the existing canonical pullback map,
independent of the changed auxiliary evaluation. -/
theorem DualWitness.parameterMap_pullbackMap (W : DualWitness A) (b : S' ⟶ S)
    (W' : DualWitness ((baseChange b).obj A)) (lam : A ⟶ W.dual P) :
    W'.parameterMap P (W.pullbackMap P b W' lam) =
      dualBaseChangeMap A W.hasDual P.universality b (W.parameterMap P lam) :=
  dualAbelianBaseChangeMap_hom P.preservation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.universality P.compatibility b A
    W.hasDual W.geometry W.inverseBundle W.evaluation
    W'.hasDual W'.geometry W'.inverseBundle W'.evaluation lam

variable {P} {g d n : ℕ}

/-- Actual pullback using a specified changed auxiliary presentation.
The ordinary restriction operation below derives that presentation itself. -/
def Datum.pullbackWith (a : Datum P S g d n) (b : S' ⟶ S)
    (W : DualWitness ((baseChange b).obj a.abelian)) : Datum P S' g d n where
  abelian := (baseChange b).obj a.abelian
  dimension := hasRelativeDimension_baseChange a.abelian g a.dimension b
  dualWitness := W
  polarization := a.dualWitness.pullbackMap P b W a.polarization
  polarized := P.polarizationBaseChange P.preservation P.square P.universality P.stability
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.compatibility
    S S' b a.abelian a.dualWitness.hasDual a.dualWitness.geometry
    a.dualWitness.inverseBundle a.dualWitness.evaluation
    W.hasDual W.geometry W.inverseBundle W.evaluation a.polarization a.polarized
  degree := HasDegreeSquare.post_iso (a.polarized.1.baseChange b)
    (HasDegreeSquare.baseChange a.polarized.1 a.degree b)
    (a.dualWitness.baseChangeIso P b W)
  level := a.level.pullback b

/-- Actual pullback, with every changed-dual witness constructed from the original
datum and the named canonical comparison. It works along every base morphism. -/
def Datum.pullback (a : Datum P S g d n) (b : S' ⟶ S) : Datum P S' g d n :=
  a.pullbackWith b (a.dualWitness.pullback P b)

@[simp] theorem Datum.pullback_abelian (a : Datum P S g d n) (b : S' ⟶ S) :
    (a.pullback b).abelian = (baseChange b).obj a.abelian := rfl

@[simp] theorem Datum.pullback_level (a : Datum P S g d n) (b : S' ⟶ S) :
    (a.pullback b).level.sections = pullbackTuple b a.level.sections := rfl

end Langlands.AbelianScheme.PolarizedFiniteLevel
