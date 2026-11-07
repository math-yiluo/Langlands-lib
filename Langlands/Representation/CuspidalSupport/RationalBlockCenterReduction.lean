import Langlands.CategoryTheory.Renard.GeneratorCenter
import Langlands.Representation.CuspidalSupport.RationalSummandBlockCenterStatement
import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! Conditional VI.4.5 evaluation-center reduction retaining the VI.4.1 input. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Block

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalBlockCenterReductionTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Forgetting full-subcategory membership identifies the two endomorphism rings. -/
def rationalInertiaBlockEndRingEquiv
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (X : RationalInertiaBlock G π) : End X ≃+* End X.obj where
  toFun f := f.hom
  invFun f := ObjectProperty.homMk f
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Evaluation at an object with fully faithful Hom functor, with codomain the
complex algebra center of its ambient endomorphism ring. -/
def rationalInertiaBlockCenterEquiv
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (X : RationalInertiaBlock G π)
    [(preadditiveCoyonedaObj X).Full] [(preadditiveCoyonedaObj X).Faithful] :
    CatCenter (RationalInertiaBlock G π) ≃+* Subalgebra.center ℂ (End X.obj) :=
  (Langlands.Renard.generatorCenterEquiv X).trans
    (Subring.centerCongr (rationalInertiaBlockEndRingEquiv G π X))

@[simp]
theorem rationalInertiaBlockCenterEquiv_apply
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G))
    (X : RationalInertiaBlock G π)
    [(preadditiveCoyonedaObj X).Full] [(preadditiveCoyonedaObj X).Faithful]
    (z : CatCenter (RationalInertiaBlock G π)) :
    (rationalInertiaBlockCenterEquiv G π X z : End X.obj) = (z.app X).hom := rfl

end Block

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- The VI.4.1 Hom equivalence implies the exact VI.4.5 block-center assertion.
The representation-theoretic hypothesis is retained explicitly. -/
theorem rationalSummandBlockCenter_of_homEquivalence
    (hHom : RationalSummandHomEquivalenceStatement.{uF, uV}) :
    RationalSummandBlockCenterStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  obtain ⟨hmem, hEquiv⟩ := hHom F G hG S i hi ν hν hStandard hRoots hU π hπ hcusp ρ hρ j hj
  let := hEquiv
  refine ⟨hmem, rationalInertiaBlockCenterEquiv G (rationalInertiaBaseLift G π) ⟨_, hmem⟩, ?_⟩
  intro z
  rfl

end Langlands.CuspidalSupport
