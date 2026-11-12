import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFiniteProductSections
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestriction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange

/-!
# Full-test finite-product decomposition of Weil restriction

Weil restriction from a finite product algebra is the product of the
restrictions of the original sheaf to its factor bases. The comparison
is a natural isomorphism on all test schemes.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace WeilRestrictionFiniteProduct

variable (A : Type u) [CommRing A]
  {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
  [∀ i, Algebra A (B i)]
  (X : AlgebraicSpace (Spec (CommRingCat.of (∀ i, B i))))

/-- The factor algebraic space is the ordinary base change along the
original product projection. -/
abbrev factorSpace (i : ι) : AlgebraicSpace (Spec (CommRingCat.of (B i))) :=
  baseChange (finiteProductSpecProjection B i) X

/-- The dependent product of the actual factor Weil presheaves. -/
def productPresheaf : Presheaf (Spec (CommRingCat.of A)) where
  obj T := ∀ i, ((ringWeilRestriction A (B i)).obj (factorSpace B X i).toSheaf).obj.obj T
  map a := ↾fun x i =>
    ((ringWeilRestriction A (B i)).obj (factorSpace B X i).toSheaf).obj.map a (x i)
  map_id T := by
    ext x i
    exact congrArg (fun f => f (x i))
      (((ringWeilRestriction A (B i)).obj (factorSpace B X i).toSheaf).obj.map_id T)
  map_comp a b := by
    ext x i
    exact congrArg (fun f => f (x i))
      (((ringWeilRestriction A (B i)).obj (factorSpace B X i).toSheaf).obj.map_comp a b)

/-- The factor test maps to the original product-base test by its actual
pullback projection and the iterated-base-change comparison. -/
def testMap (T : Over (Spec (CommRingCat.of A))) (i : ι) :
    (Over.map (finiteProductSpecProjection B i)).obj (ringBaseChange A (B i) T) ⟶
      ringBaseChange A (∀ i, B i) T :=
  (Over.map (finiteProductSpecProjection B i)).map
      (finiteProductBaseChangeTestIso B A T i).inv ≫
    FiniteProductSections.inclusion B (ringBaseChange A (∀ i, B i) T) i

/-- The comparison on all test-scheme sections. -/
def sectionsEquiv (T : Over (Spec (CommRingCat.of A))) :
    ((ringWeilRestriction A (∀ i, B i)).obj X.toSheaf).obj.obj (op T) ≃
      (productPresheaf A B X).obj (op T) :=
  (FiniteProductSections.equiv B (ringBaseChange A (∀ i, B i) T) X.toSheaf).trans
    (Equiv.piCongrRight fun i =>
      (X.presheaf.mapIso
        ((Over.map (finiteProductSpecProjection B i)).mapIso
          (finiteProductBaseChangeTestIso B A T i)).op).toEquiv.symm)

/-- Every component is restriction along the specified original factor test. -/
theorem sectionsEquiv_apply (T : Over (Spec (CommRingCat.of A)))
    (x : ((ringWeilRestriction A (∀ i, B i)).obj X.toSheaf).obj.obj (op T)) (i : ι) :
    sectionsEquiv A B X T x i = X.presheaf.map (testMap A B T i).op x := by
  change X.presheaf.map
      ((Over.map (finiteProductSpecProjection B i)).map
        (finiteProductBaseChangeTestIso B A T i).inv).op
      (X.presheaf.map (FiniteProductSections.inclusion B
        (ringBaseChange A (∀ i, B i) T) i).op x) = _
  rw [testMap, op_comp, Functor.map_comp]
  rfl

omit [Finite ι] X in
/-- Naturality of the actual factor-test map. -/
theorem testMap_natural
    {T U : Over (Spec (CommRingCat.of A))} (a : T ⟶ U) (i : ι) :
    (Over.map (finiteProductSpecProjection B i)).map
        ((Over.pullback (Spec.algebraMap A (B i))).map a) ≫ testMap A B U i =
      testMap A B T i ≫
        (Over.pullback (Spec.algebraMap A (∀ i, B i))).map a := by
  dsimp only [testMap]
  rw [← Functor.map_comp_assoc, ← finiteProductBaseChangeTestIso_inv_natural,
    Functor.map_comp, Category.assoc,
    FiniteProductSections.inclusion_natural]
  exact (Category.assoc _ _ _).symm

end WeilRestrictionFiniteProduct

open WeilRestrictionFiniteProduct

variable (A : Type u) [CommRing A]
  {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
  [∀ i, Algebra A (B i)]
  (X : AlgebraicSpace (Spec (CommRingCat.of (∀ i, B i))))

/-- Weil restriction from a finite product base is the product of the
factor Weil presheaves, naturally on the full test category. -/
def ringWeilRestrictionFiniteProductPresheafIso :
    ((ringWeilRestriction A (∀ i, B i)).obj X.toSheaf).obj ≅
      productPresheaf A B X :=
  NatIso.ofComponents (fun T => (sectionsEquiv A B X T.unop).toIso) (by
    intro T U a
    ext x
    funext i
    change X.presheaf.obj
      (op ((Over.pullback (Spec.algebraMap A (∀ i, B i))).obj T.unop)) at x
    change sectionsEquiv A B X U.unop
        (X.presheaf.map
          ((Over.pullback (Spec.algebraMap A (∀ i, B i))).map a.unop).op x) i =
      X.presheaf.map
        ((Over.map (finiteProductSpecProjection B i)).map
          ((Over.pullback (Spec.algebraMap A (B i))).map a.unop)).op
        (sectionsEquiv A B X T.unop x i)
    rw [sectionsEquiv_apply, sectionsEquiv_apply]
    change @Eq (X.presheaf.obj
      (op ((Over.map (finiteProductSpecProjection B i)).obj
        ((Over.pullback (Spec.algebraMap A (B i))).obj U.unop)))) _ _
    have ht := congrArg (fun f => X.presheaf.map f.op)
      (testMap_natural A B a.unop i)
    have hx := (ConcreteCategory.congr_hom ht x).symm
    simp only [op_comp, Functor.map_comp, types_comp_apply] at hx
    convert hx using 1)

/-- The natural isomorphism retains the original test restriction in each
component. -/
theorem ringWeilRestrictionFiniteProductPresheafIso_hom_app
    (T : Over (Spec (CommRingCat.of A)))
    (x : ((ringWeilRestriction A (∀ i, B i)).obj X.toSheaf).obj.obj (op T)) (i : ι) :
    (ringWeilRestrictionFiniteProductPresheafIso A B X).hom.app (op T) x i =
      X.presheaf.map (testMap A B T i).op x :=
  sectionsEquiv_apply A B X T x i

end Langlands.AlgebraicGeometry.AlgebraicSpace
