import Langlands.AlgebraicGeometry.Picard.RigidifiedClassGroup
import Langlands.AlgebraicGeometry.Picard.PicardZeroMonoid
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZeroInverse
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof

/-! # The abelian-group presheaf of geometric Picard-zero classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped MonoidalCategory

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (localComparison : ∀ Y : Scheme.{u}, LocallyFreeRankOneIffTensorInvertibleStatement Y)
variable {S : Scheme.{u}} (A : AbelianScheme S)

include localComparison in
/-- Each geometric Picard-zero class has an inverse in the same subset. -/
lemma picardZeroClasses_isUnit (T : Over S) (q : PicardZeroClasses A T) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    IsUnit q := by
  let := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  rcases q with ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h L =>
    obtain ⟨N, ⟨e⟩⟩ :=
      (localComparison ((relativeSpace A.X.hom).obj T) L.obj.carrier).mpr L.property
    have hN : IsLocallyFreeRankOne N :=
      (localComparison ((relativeSpace A.X.hom).obj T) N).mp
        ⟨L.obj.carrier, ⟨(β_ N L.obj.carrier) ≪≫ e⟩⟩
    let M : LineBundle ((relativeSpace A.X.hom).obj T) := ⟨N, hN⟩
    let evaluation : tensorObj L.obj.carrier M.obj ≅
        structureSheaf ((relativeSpace A.X.hom).obj T) :=
      (localizedTensorIso ((relativeSpace A.X.hom).obj T) L.obj.carrier N).symm ≪≫ e
    apply isUnit_iff_exists_inv.mpr
    exact ⟨picardZeroInverseClass preservation A L M evaluation hq,
      picardZeroClassesTensor_inverseClass preservation A L M evaluation hq⟩

/-- The existing geometric Picard-zero monoid with the proved inverse laws. -/
@[instance_reducible]
def picardZeroClassesCommGroup (T : Over S) : CommGroup (PicardZeroClasses A T) := by
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  exact commGroupOfIsUnit (picardZeroClasses_isUnit preservation unitCoherence associativity
    comparison symmetry localComparison A T)

/-- The geometric Picard-zero classes with tensor product written as addition. -/
abbrev AdditivePicardZeroClasses (T : Over S) := Additive (PicardZeroClasses A T)

@[instance_reducible]
def picardZeroClassesAddCommGroup (T : Over S) :
    AddCommGroup (AdditivePicardZeroClasses A T) := by
  letI := picardZeroClassesCommGroup preservation unitCoherence associativity comparison
    symmetry localComparison A T
  exact Additive.addCommGroup

/-- Forgetting the geometric condition is an additive homomorphism. -/
def picardZeroInclusionAddHom (T : Over S) :
    letI := picardZeroClassesAddCommGroup preservation unitCoherence associativity comparison
      symmetry localComparison A T
    letI := RigidifiedLineBundle.classesAddCommGroup preservation unitCoherence associativity
      comparison symmetry localComparison A.X.hom (unitSection A) (unitSection_comp A) T
    AdditivePicardZeroClasses A T →+
      RigidifiedLineBundle.AdditiveClasses A.X.hom (unitSection A) (unitSection_comp A) T := by
  letI := picardZeroClassesCommGroup preservation unitCoherence associativity comparison
    symmetry localComparison A T
  letI := RigidifiedLineBundle.classesCommGroup preservation unitCoherence associativity
    comparison symmetry localComparison A.X.hom (unitSection A) (unitSection_comp A) T
  exact (picardZeroInclusionMonoidHom preservation unitCoherence associativity comparison
    symmetry A T).toAdditive

variable (composition : PullbackTensorCompositionStatement.{u})

/-- Actual parameter pullback on the additive geometric Picard-zero groups. -/
def picardZeroClassesPullbackAddHom {T U : Over S} (h : T ⟶ U) :
    letI := picardZeroClassesAddCommGroup preservation unitCoherence associativity comparison
      symmetry localComparison A U
    letI := picardZeroClassesAddCommGroup preservation unitCoherence associativity comparison
      symmetry localComparison A T
    AdditivePicardZeroClasses A U →+ AdditivePicardZeroClasses A T := by
  letI := picardZeroClassesCommGroup preservation unitCoherence associativity comparison
    symmetry localComparison A U
  letI := picardZeroClassesCommGroup preservation unitCoherence associativity comparison
    symmetry localComparison A T
  exact (picardZeroClassesPullbackMonoidHom preservation unitCoherence associativity comparison
    symmetry A composition picardZeroPullback h).toAdditive

set_option maxRecDepth 2000 in
/-- The abelian-group presheaf of geometric Picard-zero classes. -/
def picardZeroGroupPresheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := by
  letI (T : Over S) := picardZeroClassesAddCommGroup preservation unitCoherence associativity
    comparison symmetry localComparison A T
  exact
    { obj T := AddCommGrpCat.of (AdditivePicardZeroClasses A T.unop)
      map h := AddCommGrpCat.ofHom (picardZeroClassesPullbackAddHom preservation unitCoherence
        associativity comparison symmetry localComparison A composition h.unop)
      map_id T := by
        ext q
        exact ConcreteCategory.congr_hom
          ((picardZeroPresheaf picardZeroPullback A RigidifiedModule.pullbackCoherence).map_id T) q
      map_comp h k := by
        ext q
        exact ConcreteCategory.congr_hom
          ((picardZeroPresheaf picardZeroPullback A
            RigidifiedModule.pullbackCoherence).map_comp h k) q }

/-- Forgetting the group structure recovers the geometric Picard-zero presheaf. -/
def picardZeroGroupPresheafForgetIso :
    picardZeroGroupPresheaf preservation unitCoherence associativity comparison symmetry
        localComparison A composition ⋙ CategoryTheory.forget AddCommGrpCat ≅
      picardZeroPresheaf picardZeroPullback A RigidifiedModule.pullbackCoherence :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro T U h; rfl)

set_option maxRecDepth 2000 in
/-- The geometric Picard-zero inclusion is a natural family of additive homomorphisms. -/
def picardZeroGroupInclusion :
    picardZeroGroupPresheaf preservation unitCoherence associativity comparison symmetry
        localComparison A composition ⟶
      RigidifiedLineBundle.classGroupPresheaf preservation unitCoherence associativity
        comparison symmetry localComparison A.X.hom (unitSection A) (unitSection_comp A)
        composition := by
  letI (T : Over S) := picardZeroClassesAddCommGroup preservation unitCoherence associativity
    comparison symmetry localComparison A T
  letI (T : Over S) := RigidifiedLineBundle.classesAddCommGroup preservation unitCoherence
    associativity comparison symmetry localComparison A.X.hom (unitSection A)
    (unitSection_comp A) T
  exact
    { app T := AddCommGrpCat.ofHom (picardZeroInclusionAddHom preservation unitCoherence
        associativity comparison symmetry localComparison A T.unop)
      naturality T U h := by ext q; rfl }

end Langlands.AbelianScheme
