import Langlands.GroupScheme.Reductive.AffineCommutatorTriviality
import Langlands.GroupScheme.Reductive.WeilFactorRigidityReduction
import Langlands.GroupScheme.Reductive.WeilChartFactorGroup
import Langlands.GroupScheme.AffineWeilUnit

/-! # Homomorphisms from a Weil restriction restricted to the diagonal factor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.WeilAbelianImage

open WeilFactor

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

section Base

variable (B) in
/-- `B ⊗[A] T` as a `B`-algebra. -/
abbrev tensorT (T : CommAlgCat.{u} (CommRingCat.of A)) : CommAlgCat.{u} (CommRingCat.of B) :=
  WeilFactor.tensorB B T

variable (B) in
/-- The inclusion `T → B ⊗[A] T`, into the `A`-algebra restricted from `B`. -/
def inclT (T : CommAlgCat.{u} (CommRingCat.of A)) : T ⟶ (resA A B).obj (tensorT B T) :=
  WeilFactor.incl B T

/-- A `(B ⊗[A] T)`-algebra, regarded as a `T`-algebra. -/
abbrev underA {T : CommAlgCat.{u} (CommRingCat.of A)} (Y : Under (tensorT B T)) : Under T :=
  WeilFactor.liftU A Y

/-- A map of `(B ⊗[A] T)`-algebras, as a map of `T`-algebras. -/
def underAMap {T : CommAlgCat.{u} (CommRingCat.of A)} {Y Y' : Under (tensorT B T)} (χ : Y ⟶ Y') :
    underA Y ⟶ underA Y' :=
  Under.homMk ((resA A B).map χ.right) (by
    change inclT B T ≫ (resA A B).map Y.hom ≫ (resA A B).map χ.right =
      inclT B T ≫ (resA A B).map Y'.hom
    rw [← Functor.map_comp, Under.w χ])

variable (M : GroupScheme (Spec (CommRingCat.of A)))

/-- Points of `M_B` over a `B`-algebra are points of `M` over the underlying `A`-algebra. -/
def pointsEquivB (X : CommAlgCat.{u} (CommRingCat.of B)) :
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj M).affinePoints X ≃*
      M.affinePoints ((resA A B).obj X) :=
  WeilChart.bPointsEquiv M X

theorem pointsEquivB_symm_naturality {X Y : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ Y)
    (p : M.affinePoints ((resA A B).obj X)) :
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj M).affinePointMap χ
        ((pointsEquivB M X).symm p) =
      (pointsEquivB M Y).symm (M.affinePointMap ((resA A B).map χ) p) :=
  WeilChart.bPointsEquiv_symm_naturality M χ p

end Base

section Transfer

variable [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B]
  (G' : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G'.X.left] [LocallyOfFiniteType G'.X.hom]
  {M : GroupScheme (Spec (CommRingCat.of A))} {T : CommAlgCat.{u} (CommRingCat.of A)}
  (c : Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor ⟶
    Under.forget T ⋙ M.affinePointFunctor)

/-- The homomorphism `c` restricted to the diagonal factor: on a `(B ⊗[A] T)`-algebra `Y`, it
sends a point of `G'` over `Y` to `c` of its image under `embNat`, viewed in `M_B`. -/
def transferApp (Y : Under (tensorT B T)) :
    G'.affinePoints Y.right →*
      ((GroupScheme.baseChange (Spec.algebraMap A B)).obj M).affinePoints Y.right :=
  (pointsEquivB M Y.right).symm.toMonoidHom.comp
    ((c.app (underA Y)).hom.comp ((embNat A G').app Y.right).hom)

/-- The restricted homomorphism, as a natural transformation. -/
def transfer : Under.forget (tensorT B T) ⋙ G'.affinePointFunctor ⟶
    Under.forget (tensorT B T) ⋙
      ((GroupScheme.baseChange (Spec.algebraMap A B)).obj M).affinePointFunctor where
  app Y := GrpCat.ofHom (transferApp G' c Y)
  naturality Y Y' χ := by
    refine GrpCat.ext fun y => ?_
    change transferApp G' c Y' (G'.affinePointMap χ.right y) =
      ((GroupScheme.baseChange (Spec.algebraMap A B)).obj M).affinePointMap χ.right
        (transferApp G' c Y y)
    have hemb := congrArg (fun h => GrpCat.Hom.hom h y) ((embNat A G').naturality χ.right)
    have hc := congrArg (fun h => GrpCat.Hom.hom h (((embNat A G').app Y.right).hom y))
      (c.naturality (underAMap χ))
    simp only [transferApp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [pointsEquivB_symm_naturality]
    congr 1
    change (c.app (underA Y')).hom (((embNat A G').app Y'.right).hom (G'.affinePointMap χ.right y)) = _
    have hemb' : ((embNat A G').app Y'.right).hom (G'.affinePointMap χ.right y) =
        (AffineWeil.groupScheme A B G').affinePointMap ((resA A B).map χ.right)
          (((embNat A G').app Y.right).hom y) := hemb
    rw [hemb']
    exact hc

variable (hc : ∀ (X : Under T)
  (x y : (Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor).obj X),
  Commute (c.app X x) (c.app X y))

include hc in
/-- **The diagonal factor is killed.** If `G'` is reductive with semisimple geometric fibres,
then `c` is trivial on the image of `embNat`. -/
theorem app_embNat_eq_one (hred : IsReductive G')
    (hss : ∀ s, IsSemisimple (geometricFiber G' s)) (Y : Under (tensorT B T))
    (y : G'.affinePoints Y.right) :
    c.app (underA Y) (((embNat A G').app Y.right).hom y) = 1 := by
  have hc' : ∀ (Y : Under (tensorT B T))
      (x y : (Under.forget (tensorT B T) ⋙ G'.affinePointFunctor).obj Y),
      Commute ((transfer G' c).app Y x) ((transfer G' c).app Y y) := by
    intro Y x y
    exact (hc (underA Y) _ _).map (pointsEquivB M Y.right).symm
  have h := CommutatorTriviality.app_eq_one_of_semisimple (transfer G' c) hc' hred hss Y y
  change (pointsEquivB M Y.right).symm (c.app (underA Y) (((embNat A G').app Y.right).hom y)) =
    1 at h
  rw [← map_one (pointsEquivB M Y.right).symm] at h
  exact (pointsEquivB M Y.right).symm.injective h

end Transfer

end Langlands.GroupScheme.WeilAbelianImage
