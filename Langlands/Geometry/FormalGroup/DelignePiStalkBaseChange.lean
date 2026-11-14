import Langlands.Geometry.FormalGroup.DeligneFrameStalkBaseChange

/-! # Actual rational Pi and its integer powers under inverse image -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O : Type u} [CommRing O] {X Y : TopCat.{u}}
variable (F : Type u) [Field F] [Algebra O F] {d : ℕ} [NeZero d] {π : O}

/-- The actual total rational sheaf comparison intertwines the Pi automorphisms. -/
theorem inverseImageRationalLatticeIso_pi (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
        (rationalPiAut F Y d π M hπ).hom ≫
          (inverseImageRationalLatticeIso F f M).hom =
      (inverseImageRationalLatticeIso F f M).hom ≫
        (rationalPiAut F X d π
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ).hom := by
  simp only [rationalPiAut_hom]
  change (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
      ((rationalSheafFunctor F Y).map (latticePi d π Y M)) ≫
        ((inverseImageRationalIso (F := F) f).hom.app (latticeScalarSheaf d π Y M) ≫
          (rationalSheafFunctor F X).map (inverseImageLatticeScalarIso f M).hom) =
    ((inverseImageRationalIso (F := F) f).hom.app (latticeScalarSheaf d π Y M) ≫
      (rationalSheafFunctor F X).map (inverseImageLatticeScalarIso f M).hom) ≫
        (rationalSheafFunctor F X).map (latticePi d π X
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M))
  rw [← Category.assoc, inverseImageRationalIso_naturality, Category.assoc,
    ← Functor.map_comp, inverseImageLatticeScalarIso_pi, Functor.map_comp,
    Category.assoc]

/-- The actual F-linear stalk comparison intertwines the Pi automorphisms. -/
theorem rationalPiStalkAut_pullback (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0)
    (x : X) :
    (rationalPiStalkAut F Y d π M hπ (f x)).hom ≫
        (rationalLatticeStalkPullbackIso F f M x).hom =
      (rationalLatticeStalkPullbackIso F f M x).hom ≫
        (rationalPiStalkAut F X d π
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ x).hom := by
  let T := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
  have h := congrArg (fun k => T.map k) (inverseImageRationalLatticeIso_pi F f M hπ)
  simp only [Functor.map_comp] at h
  change (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) (f x)).map
      (rationalPiAut F Y d π M hπ).hom.hom ≫
        ((inverseImageStalkIso f (rationalLattice F Y d π M) x).hom ≫
          T.map (inverseImageRationalLatticeIso F f M).hom) =
    ((inverseImageStalkIso f (rationalLattice F Y d π M) x).hom ≫
      T.map (inverseImageRationalLatticeIso F f M).hom) ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
          (rationalPiAut F X d π
            ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ).hom.hom
  rw [← Category.assoc, inverseImageStalkIso_naturality, Category.assoc,
    Category.assoc]
  exact congrArg (fun k => (inverseImageStalkIso f (rationalLattice F Y d π M) x).hom ≫ k) h

/-- Transport of the original actual Pi automorphism by the actual stalk isomorphism. -/
def rationalPiStalkPullbackAut (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0)
    (x : X) :
    Aut (rationalLatticeStalk F X d π
      ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) x) :=
  Aut.autMulEquivOfIso (rationalLatticeStalkPullbackIso F f M x)
    (rationalPiStalkAut F Y d π M hπ (f x))

/-- The transported operator is the actual rational Pi on the pulled stalk. -/
theorem rationalPiStalkPullbackAut_eq (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0)
    (x : X) :
    rationalPiStalkPullbackAut F f M hπ x =
      rationalPiStalkAut F X d π
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ x := by
  apply Aut.ext
  change (rationalLatticeStalkPullbackIso F f M x).inv ≫
      (rationalPiStalkAut F Y d π M hπ (f x)).hom ≫
        (rationalLatticeStalkPullbackIso F f M x).hom = _
  rw [rationalPiStalkAut_pullback, Iso.inv_hom_id_assoc]

/-- The actual stalk comparison intertwines every integer power, including negative powers. -/
theorem rationalPiStalkAut_zpow_pullback (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (hπ : algebraMap O F π ≠ 0)
    (n : ℤ) (x : X) :
    (rationalPiStalkAut F Y d π M hπ (f x) ^ n).hom ≫
        (rationalLatticeStalkPullbackIso F f M x).hom =
      (rationalLatticeStalkPullbackIso F f M x).hom ≫
        (rationalPiStalkAut F X d π
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) hπ x ^ n).hom := by
  have h := map_zpow (Aut.autMulEquivOfIso (rationalLatticeStalkPullbackIso F f M x))
    (rationalPiStalkAut F Y d π M hπ (f x)) n
  change Aut.autMulEquivOfIso (rationalLatticeStalkPullbackIso F f M x)
      (rationalPiStalkAut F Y d π M hπ (f x) ^ n) =
        rationalPiStalkPullbackAut F f M hπ x ^ n at h
  rw [rationalPiStalkPullbackAut_eq] at h
  have hh := congrArg (fun a => a.hom) h
  change (rationalLatticeStalkPullbackIso F f M x).inv ≫
      (rationalPiStalkAut F Y d π M hπ (f x) ^ n).hom ≫
        (rationalLatticeStalkPullbackIso F f M x).hom = _ at hh
  have hhh := congrArg (fun k => (rationalLatticeStalkPullbackIso F f M x).hom ≫ k) hh
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hhh

end Langlands.DeligneFormalSpace
