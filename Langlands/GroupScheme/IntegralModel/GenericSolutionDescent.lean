import Langlands.GroupScheme.IntegralModel.AffineDatumDescent
import Langlands.GroupScheme.Descent.AffineDatumMorphisms
import Langlands.GroupScheme.BaseChangeReflection

/-! # Generic comparisons for effective integral group descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

open Descent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {A L : Type u} [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {N : IntegralModel A L ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)}
  {D : Datum (Spec.algebraMap R A) N.group}
  (s : Solution D)
  [Surjective (Spec.algebraMap R A)] [Flat (Spec.algebraMap R A)]
  [IsAffine s.obj.X.left]

/-- The solution as a smooth model of its own actual generic fibre. -/
def solutionModel (hN : N.IsSmooth) :
    IntegralModel R K ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj) := by
  let : Smooth N.group.X.hom := hN
  let : Smooth s.obj.X.hom := s.smooth
  exact { group := s.obj, genericIso := Iso.refl _ }

omit [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L] in
theorem isSmooth_solutionModel (hN : N.IsSmooth) :
    (solutionModel s hN).IsSmooth := by
  let : Smooth N.group.X.hom := hN
  exact s.smooth

/-- The solution and the original model supply an actual generic comparison
after extension to the upstairs fraction field. -/
def solutionGenericComparison (hN : N.IsSmooth) :
    (GroupScheme.baseChange (Spec.algebraMap K L)).obj
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj) ≅
      (GroupScheme.baseChange (Spec.algebraMap K L)).obj G :=
  ((solutionModel s hN).baseChangeGenericIso A L).symm ≪≫
    (GroupScheme.baseChange (Spec.algebraMap A L)).mapIso s.iso ≪≫ N.genericIso

/-- A downstairs generic isomorphism recovering the solution's upstairs
comparison gives exactly the required compatible isomorphism of models. -/
def isoOfSolutionGenericRecovery (hN : N.IsSmooth)
    (e : (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G)
    (he : (GroupScheme.baseChange (Spec.algebraMap K L)).mapIso e =
      solutionGenericComparison s hN) :
    ((ofAffineSolution s hN e).baseChange A L).Iso N (Iso.refl _) :=
  isoOfAffineSolution s hN e (by
    have h := congrArg (fun q => q.hom) he
    simp only [Functor.mapIso_hom, solutionGenericComparison, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom] at h
    have he' :
        ((solutionModel s hN).baseChangeGenericIso A L).hom ≫
            (GroupScheme.baseChange (Spec.algebraMap K L)).map e.hom =
          (GroupScheme.baseChange (Spec.algebraMap A L)).map s.iso.hom ≫
            N.genericIso.hom := by
      rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← he']
    simp only [baseChangeGenericIso, solutionModel, ofAffineSolution,
      Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
    rw [(GroupScheme.baseChange (Spec.algebraMap K L)).map_id, Category.comp_id])

/-- Čech compatibility of the comparison on the fraction fields. -/
def SolutionGenericCompatible (hN : N.IsSmooth) : Prop :=
  Compatible
    (canonicalDatum (Spec.algebraMap K L)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj))
    (canonicalDatum (Spec.algebraMap K L) G)
    (solutionGenericComparison s hN).hom

/-- Descend the supplied compatible upstairs generic comparison along the
faithfully flat fraction-field extension. -/
def solutionGenericIso (hN : N.IsSmooth) (hc : SolutionGenericCompatible s hN) :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G := by
  let : Surjective (Spec.algebraMap K L) := (fieldExtension_fpqc K L).1
  let : Flat (Spec.algebraMap K L) := (fieldExtension_fpqc K L).2.1
  exact Solution.descendIso (canonicalSolution (Spec.algebraMap K L)
    ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj))
    (canonicalSolution (Spec.algebraMap K L) G) (solutionGenericComparison s hN) hc

/-- The descended generic isomorphism recovers the original comparison exactly. -/
theorem baseChange_solutionGenericIso (hN : N.IsSmooth)
    (hc : SolutionGenericCompatible s hN) :
    (GroupScheme.baseChange (Spec.algebraMap K L)).mapIso
        (solutionGenericIso s hN hc) = solutionGenericComparison s hN := by
  let : Surjective (Spec.algebraMap K L) := (fieldExtension_fpqc K L).1
  let : Flat (Spec.algebraMap K L) := (fieldExtension_fpqc K L).2.1
  apply Iso.ext
  change (GroupScheme.baseChange (Spec.algebraMap K L)).map
    (Solution.descendHom (canonicalSolution (Spec.algebraMap K L)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj))
      (canonicalSolution (Spec.algebraMap K L) G) (solutionGenericComparison s hN).hom hc) =
    (solutionGenericComparison s hN).hom
  simpa only [canonicalSolution, Iso.refl_hom, Category.comp_id, Category.id_comp] using
    Solution.baseChange_descendHom (canonicalSolution (Spec.algebraMap K L)
      ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj))
      (canonicalSolution (Spec.algebraMap K L) G) (solutionGenericComparison s hN).hom hc

/-- An actual affine solution whose generic comparison is compatible yields
an actual smooth integral model of the prescribed generic group. -/
def ofGenericCompatibleSolution (hN : N.IsSmooth)
    (hc : SolutionGenericCompatible s hN) : IntegralModel R K G :=
  ofAffineSolution s hN (solutionGenericIso s hN hc)

theorem isSmooth_ofGenericCompatibleSolution (hN : N.IsSmooth)
    (hc : SolutionGenericCompatible s hN) :
    (ofGenericCompatibleSolution s hN hc).IsSmooth :=
  isSmooth_ofAffineSolution s hN _

/-- The constructed model has the prescribed upstairs model over the generic
identity, with its actual comparison supplied by the solution. -/
def isoOfGenericCompatibleSolution (hN : N.IsSmooth)
    (hc : SolutionGenericCompatible s hN) :
    ((ofGenericCompatibleSolution s hN hc).baseChange A L).Iso N (Iso.refl _) :=
  isoOfSolutionGenericRecovery s hN _ (baseChange_solutionGenericIso s hN hc)

end Langlands.GroupScheme.IntegralModel
