import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange
import Langlands.AbelianScheme.Isogeny

/-! # Polarizations over a field via ample Mumford maps -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable (k : Type u) [Field k]
variable (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
variable (hA : HasDualScheme A)

/-- The ample-Mumford equality holds after some extension of the ground field,
using the canonical Poincare-compatible comparison of the actual duals. -/
def HasFieldAmpleMumfordPresentation (f : A.X ⟶ dualScheme A hA) : Prop :=
  ∃ (K : Type u) (_ : Field K) (ι : k →+* K),
    HasAmpleMumfordAfterBaseChange preservation square A hA universality
      (Spec.map (CommRingCat.ofHom ι)) f

variable (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- A polarization is an actual homomorphism to the constructed dual, isogenous over k,
and equal to an ample Mumford map after some field extension. -/
def IsFieldPolarization (lam : A ⟶ DA) : Prop :=
  Langlands.GroupScheme.IsIsogeny (groupHom lam) ∧
    HasFieldAmpleMumfordPresentation preservation square universality k A hA
      (groupHom lam).hom.hom

/-- A principal polarization is a polarization whose actual abelian-scheme
homomorphism is an isomorphism. -/
def IsPrincipalFieldPolarization (lam : A ⟶ DA) : Prop :=
  IsFieldPolarization preservation square universality k A hA geometryA MA evaluationA
    stability composition unitCoherence associativity comparison symmetry lam ∧ IsIso lam

end Langlands.AbelianScheme
