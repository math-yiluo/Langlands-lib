import Langlands.AlgebraicGeometry.Picard.RelativePolarization
import Langlands.AlgebraicGeometry.Picard.RationalPolarizationCompatibility
import Langlands.AbelianScheme.GeometricEndomorphismTrace
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! # Actual rational Rosati conjugation by a geometric polarization -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme.Rosati

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Exactly the tensor and Picard inputs used to construct the dual and the
existing geometric polarization predicate. No positivity or finiteness input. -/
structure Prerequisites : Prop where
  preservation : pullbackTensorComparisonIsIsoStatement.{u}
  composition : PullbackTensorCompositionStatement.{u}
  unitCoherence : PullbackTensorUnitCoherenceStatement.{u}
  associativity : ExplicitPullbackTensorAssociativityStatement.{u}
  comparison : TensorMonoidalLeftUnitorComparisonStatement.{u}
  symmetry : PullbackTensorSymmetryStatement.{u}
  stability : PicardZeroPullbackStatement.{u}
  square : MumfordBundlePicardZeroStatement.{u}
  universality : PicardZeroUniversalBaseChangeStatement.{u}

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Per-object witnesses for the existing constructed dual and its actual
additive endomorphism dualization. -/
structure DualData where
  hasDual : HasDualScheme A
  geometry : DualSchemeGeometry A hasDual
  inversePoincare : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hasDual))
  evaluation : tensorObj (poincareFamily A hasDual).obj.carrier inversePoincare.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hasDual))

variable (P : Prerequisites.{u}) {A}

/-- The existing actual abelian-scheme dual with this datum's witnesses. -/
def DualData.dual (W : DualData A) : AbelianScheme S :=
  dualAbelianSchemeFromEvaluation A W.hasDual W.geometry P.preservation W.inversePoincare
    W.evaluation P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry

/-- The exact pointwise additivity prerequisite for the existing dual map. -/
abbrev DualData.Additivity (W : DualData A) : Prop :=
  DualSchemeMapAdditivity P.preservation P.stability A A W.hasDual W.hasDual

/-- The actual rational dualization used by RationalPolarizationCompatibility. -/
def DualData.dual0 (W : DualData A) (hadd : W.Additivity P) :
    End0 A →ₗ[ℚ] End0 (W.dual P) :=
  dualHom0 P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability W.hasDual W.hasDual hadd W.inversePoincare W.evaluation
    W.inversePoincare W.evaluation W.geometry W.geometry

/-- The existing actual geometric polarization predicate, without added conditions. -/
abbrev DualData.IsPolarization (W : DualData A) (lam : A ⟶ W.dual P) : Prop :=
  AbelianScheme.IsPolarization P.preservation P.square P.universality A W.hasDual W.geometry
    W.inversePoincare W.evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry lam

variable (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)

/-- Rational invertibility of the particular actual polarization homomorphism. -/
abbrev HasRationalInverse : Prop := IsIso ((rationalization S).map lam)

variable [HasRationalInverse P W lam]

/-- The actual inverse in the existing rational category; no inverse map is supplied. -/
def polarizationInverse : Hom0 (W.dual P) A := inv ((rationalization S).map lam)

@[simp] theorem polarization_comp_inverse :
    comp0 A (W.dual P) A (homToHom0 lam) (polarizationInverse P W lam) = id0 A :=
  IsIso.hom_inv_id ((rationalization S).map lam)

@[simp] theorem inverse_comp_polarization :
    comp0 (W.dual P) A (W.dual P) (polarizationInverse P W lam) (homToHom0 lam) =
      id0 (W.dual P) :=
  IsIso.inv_hom_id ((rationalization S).map lam)

/-- Actual Rosati conjugation: alpha maps to lambda inverse after alpha dual after lambda. -/
def involution : End0 A →ₗ[ℚ] End0 A :=
  { toFun a := comp0 A (W.dual P) A
      (comp0 A (W.dual P) (W.dual P) (homToHom0 lam) (W.dual0 P hadd a))
      (polarizationInverse P W lam)
    map_add' a b := by simp only [map_add, LinearMap.add_apply]
    map_smul' q a := by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }

/-- The defining formula uses the actual rational dual, polarization and inverse. -/
theorem involution_apply (a : End0 A) :
    involution P W hadd lam a = comp0 A (W.dual P) A
      (comp0 A (W.dual P) (W.dual P) (homToHom0 lam) (W.dual0 P hadd a))
      (polarizationInverse P W lam) := rfl

variable {k : Type u} [Field k]
  {A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))}

/-- The actual trace form Tr(alpha composed with beta dagger). End0 multiplication
is composition with the right factor applied first. -/
def traceForm (W : DualData A) (hadd : W.Additivity P) (lam : A ⟶ W.dual P)
    [HasRationalInverse P W lam] : LinearMap.BilinForm ℚ (End0 A) where
  toFun a := (geometricEndomorphismTrace A).comp
    ((comp0 A A A).flip a |>.comp (involution P W hadd lam))
  map_add' a b := by
    ext c
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, map_add,
      LinearMap.add_apply]
  map_smul' q a := by
    ext c
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem traceForm_apply (W : DualData A) (hadd : W.Additivity P)
    (lam : A ⟶ W.dual P) [HasRationalInverse P W lam] (a b : End0 A) :
    traceForm P W hadd lam a b =
      geometricEndomorphismTrace A (a * involution P W hadd lam b) := rfl

end Langlands.AbelianScheme.Rosati
