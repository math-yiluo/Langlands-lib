import Langlands.AlgebraicGeometry.Picard.RigidifiedClassMonoid
import Langlands.AlgebraicGeometry.Picard.RigidifiedInverse
import Langlands.AlgebraicGeometry.Picard.LocalComparisonStatement
import Mathlib.Algebra.Category.Grp.Basic

/-! # The abelian-group presheaf of rigidified line-bundle classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped MonoidalCategory

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (localComparison : ∀ Y : Scheme.{u}, LocallyFreeRankOneIffTensorInvertibleStatement Y)
variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

include localComparison in
/-- Each actual rigidified class is a unit, using the named rank-one comparison
and the existing evaluation-induced rigidification of an inverse. -/
lemma classes_isUnit (T : Over S) (q : Classes f ε section_eq T) :
    letI := classesCommMonoid preservation unitCoherence associativity comparison symmetry
      f ε section_eq T
    IsUnit q := by
  let := classesCommMonoid preservation unitCoherence associativity comparison symmetry
    f ε section_eq T
  induction q using Quotient.inductionOn with
  | h L =>
    obtain ⟨N, ⟨e⟩⟩ :=
      (localComparison ((relativeSpace f).obj T) L.obj.carrier).mpr L.property
    have hN : IsLocallyFreeRankOne N :=
      (localComparison ((relativeSpace f).obj T) N).mp
        ⟨L.obj.carrier, ⟨(β_ N L.obj.carrier) ≪≫ e⟩⟩
    let M : LineBundle ((relativeSpace f).obj T) := ⟨N, hN⟩
    let evaluation : tensorObj L.obj.carrier M.obj ≅
        structureSheaf ((relativeSpace f).obj T) :=
      (localizedTensorIso ((relativeSpace f).obj T) L.obj.carrier N).symm ≪≫ e
    apply isUnit_iff_exists_inv.mpr
    exact ⟨classOf f ε section_eq (rigidifyInverse preservation L M evaluation),
      classesTensor_rigidifyInverse preservation f ε section_eq L M evaluation⟩

/-- The proved class monoid is a commutative group because each class is a unit. -/
@[instance_reducible]
def classesCommGroup (T : Over S) : CommGroup (Classes f ε section_eq T) := by
  letI := classesCommMonoid preservation unitCoherence associativity comparison symmetry
    f ε section_eq T
  exact commGroupOfIsUnit (classes_isUnit preservation unitCoherence associativity comparison
    symmetry localComparison f ε section_eq T)

/-- The same compatible-isomorphism classes with tensor written additively. -/
abbrev AdditiveClasses (T : Over S) := Additive (Classes f ε section_eq T)

@[instance_reducible]
def classesAddCommGroup (T : Over S) : AddCommGroup (AdditiveClasses f ε section_eq T) := by
  letI := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq T
  exact Additive.addCommGroup

variable (composition : PullbackTensorCompositionStatement.{u})

/-- Actual relative pullback on the additive groups of rigidified classes. -/
def classesPullbackAddHom {T U : Over S} (h : T ⟶ U) :
    letI := classesAddCommGroup preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq U
    letI := classesAddCommGroup preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq T
    AdditiveClasses f ε section_eq U →+ AdditiveClasses f ε section_eq T := by
  letI := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq U
  letI := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq T
  exact (classesPullbackMonoidHom preservation unitCoherence associativity comparison symmetry
    f ε section_eq composition h).toAdditive

set_option maxRecDepth 2000 in
/-- The presheaf of actual rigidified line-bundle classes valued in abelian groups. -/
def classGroupPresheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := by
  letI (T : Over S) := classesAddCommGroup preservation unitCoherence associativity comparison
    symmetry localComparison f ε section_eq T
  exact
    { obj T := AddCommGrpCat.of (AdditiveClasses f ε section_eq T.unop)
      map h := AddCommGrpCat.ofHom (classesPullbackAddHom preservation unitCoherence associativity
        comparison symmetry localComparison f ε section_eq composition h.unop)
      map_id T := by
        ext q
        exact ConcreteCategory.congr_hom
          ((classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq).map_id T) q
      map_comp h k := by
        ext q
        exact ConcreteCategory.congr_hom
          ((classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq).map_comp h k) q }

/-- Forgetting the group structure recovers the original presheaf of classes. -/
def classGroupPresheafForgetIso :
    classGroupPresheaf preservation unitCoherence associativity comparison symmetry
        localComparison f ε section_eq composition ⋙ CategoryTheory.forget AddCommGrpCat ≅
      classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro T U h; rfl)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
