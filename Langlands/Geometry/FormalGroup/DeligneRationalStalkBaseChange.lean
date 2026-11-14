import Langlands.Geometry.FormalGroup.DeligneDeterminantLattice
import Langlands.Geometry.FormalGroup.DeligneStalkUBaseChange

/-! # Actual rational stalk comparisons for Deligne lattices -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O R : Type u} [CommRing O] [CommRing R] {X Y : TopCat.{u}}

/-- The coefficient-extension comparison preserves the two composite adjunction units. -/
theorem inverseImageExtensionIso_unit_section (ρ : O →+* R) (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} O)) (U : Opens Y) (m : M.obj.obj (.op U)) :
    ((inverseImageExtensionIso ρ f).hom.app M).hom.app (.op ((Opens.map f).obj U))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f).unit.app
          ((coefficientExtension ρ Y).obj M)).hom.app (.op U))
            (((coefficientExtensionAdjunction ρ Y).unit.app M).hom.app (.op U) m)) =
      ((coefficientExtensionAdjunction ρ X).unit.app
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M)).hom.app
        (.op ((Opens.map f).obj U))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app
            M).hom.app (.op U) m) := by
  let A := (coefficientExtensionAdjunction ρ Y).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) f)
  let B := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).comp
    (coefficientExtensionAdjunction ρ X)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app A B M
  simp only [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k => k.hom.app (.op U) m) h

variable {F : Type u} [Field F] [Algebra O F]

/-- Rationalization followed by inverse image preserves the actual integral section map. -/
theorem inverseImageRationalIso_unit_section (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} O)) (U : Opens Y) (m : M.obj.obj (.op U)) :
    ((inverseImageRationalIso (F := F) f).hom.app M).hom.app
        (.op ((Opens.map f).obj U))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} F) f).unit.app
            ((rationalSheafFunctor F Y).obj M)).hom.app (.op U))
              ((rationalUnit F Y M).hom.app (.op U) m)) =
      (rationalUnit F X ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M)).hom.app
        (.op ((Opens.map f).obj U))
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app
            M).hom.app (.op U) m) := by
  simp only [rationalUnit_eq_adjunctionUnit]
  exact inverseImageExtensionIso_unit_section (algebraMap O F) f M U m

variable (F)

/-- The canonical comparison from the original rational stalk to the rationalized
inverse-image stalk. -/
def rationalStalkPullbackIso (f : X ⟶ Y) (M : Y.Sheaf (ModuleCat.{u} O)) (x : X) :
    TopCat.Presheaf.stalk ((rationalSheafFunctor F Y).obj M).obj (f x) ≅
      TopCat.Presheaf.stalk
        ((rationalSheafFunctor F X).obj
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M)).obj x :=
  inverseImageStalkIso f ((rationalSheafFunctor F Y).obj M) x ≪≫
    ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)) ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).mapIso
        ((inverseImageRationalIso (F := F) f).app M)

/-- The actual rational stalk comparison is computed by the inverse-image unit
and the rationalization comparison on germs. -/
theorem rationalStalkPullbackIso_germ (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} O)) (x : X) (U : Opens Y) (hx : f x ∈ U) :
    TopCat.Presheaf.germ ((rationalSheafFunctor F Y).obj M).obj U (f x) hx ≫
        (rationalStalkPullbackIso F f M x).hom =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} F) f).unit.app
        ((rationalSheafFunctor F Y).obj M)).hom.app (.op U)) ≫
          ((inverseImageRationalIso (F := F) f).hom.app M).hom.app
            (.op ((Opens.map f).obj U)) ≫
              TopCat.Presheaf.germ
                ((rationalSheafFunctor F X).obj
                  ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M)).obj
                  ((Opens.map f).obj U) x hx := by
  dsimp only [rationalStalkPullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rw [← Category.assoc, inverseImageStalkIso_germ, Category.assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- The actual rational comparison commutes with the integral-to-rational stalk map. -/
theorem rationalStalkPullbackIso_integral (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} O)) (x : X) :
    integralRationalStalkMap F Y M (f x) ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          (rationalStalkPullbackIso F f M x).hom =
      (inverseImageStalkIso f M x).hom ≫
        integralRationalStalkMap F X
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M) x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  simp only [← Category.assoc]
  rw [integralRationalStalkMap_germ, inverseImageStalkIso_germ]
  simp only [Category.assoc]
  rw [← Functor.map_comp, rationalStalkPullbackIso_germ]
  rw [← Category.assoc, integralRationalStalkMap_germ]
  apply ModuleCat.hom_ext
  ext m
  exact congrArg
    (fun z => TopCat.Presheaf.germ
      ((rationalSheafFunctor F X).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M)).obj
          ((Opens.map f).obj U) x hx z)
    (inverseImageRationalIso_unit_section f M U m)

/-- Naturality of the actual integral-to-rational stalk map. -/
theorem integralRationalStalkMap_naturality {M N : X.Sheaf (ModuleCat.{u} O)}
    (g : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map g.hom ≫
        integralRationalStalkMap F X N x =
      integralRationalStalkMap F X M x ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
            ((rationalSheafFunctor F X).map g).hom) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  simp only [← Category.assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc,
    integralRationalStalkMap_germ, integralRationalStalkMap_germ,
    Category.assoc, ← Functor.map_comp, TopCat.Presheaf.stalkFunctor_map_germ]
  have h := congrArg (fun k => k.hom.app (.op U)) (rationalUnit_naturality F X g)
  exact congrArg (fun k => k ≫
    (ModuleCat.restrictScalars (algebraMap O F)).map
      (TopCat.Presheaf.germ ((rationalSheafFunctor F X).obj N).obj U x hx)) h

/-- The actual rational stalk comparison intertwines every integral sheaf map. -/
theorem rationalStalkPullbackIso_naturality (f : X ⟶ Y)
    {M N : Y.Sheaf (ModuleCat.{u} O)} (g : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) (f x)).map
        ((rationalSheafFunctor F Y).map g).hom ≫
          (rationalStalkPullbackIso F f N x).hom =
      (rationalStalkPullbackIso F f M x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
          ((rationalSheafFunctor F X).map
            ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g)).hom := by
  let T := sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x
  have h := congrArg (fun k => T.map k)
    (inverseImageRationalIso_naturality (F := F) f g)
  simp only [Functor.map_comp] at h
  dsimp only [rationalStalkPullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rw [← Category.assoc, inverseImageStalkIso_naturality, Category.assoc]
  exact congrArg (fun k =>
    (inverseImageStalkIso f ((rationalSheafFunctor F Y).obj M) x).hom ≫ k) h

variable {d : ℕ} {π : O}

/-- The actual total rational sheaf comparison, including Pi-algebra scalar restriction. -/
def inverseImageRationalLatticeIso (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).obj (rationalLattice F Y d π M) ≅
      rationalLattice F X d π
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) :=
  (inverseImageRationalIso (F := F) f).app (latticeScalarSheaf d π Y M) ≪≫
    (rationalSheafFunctor F X).mapIso (inverseImageLatticeScalarIso f M)

/-- The actual F-linear comparison of total rational lattice stalks. -/
def rationalLatticeStalkPullbackIso (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (x : X) :
    rationalLatticeStalk F Y d π M (f x) ≅
      rationalLatticeStalk F X d π
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) x :=
  inverseImageStalkIso f (rationalLattice F Y d π M) x ≪≫
    ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} F)) ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).mapIso
        (inverseImageRationalLatticeIso F f M)

/-- Decomposition of the total stalk comparison into rationalization and
Pi-algebra coefficient restriction comparisons. -/
theorem rationalLatticeStalkPullbackIso_hom (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (x : X) :
    (rationalLatticeStalkPullbackIso F f M x).hom =
      (rationalStalkPullbackIso F f (latticeScalarSheaf d π Y M) x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
          ((rationalSheafFunctor F X).map (inverseImageLatticeScalarIso f M).hom).hom := by
  simp only [rationalLatticeStalkPullbackIso, inverseImageRationalLatticeIso,
    rationalStalkPullbackIso, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  rfl

/-- The total rational stalk comparison preserves the actual integral lattice map. -/
theorem rationalLatticeStalkPullbackIso_integral (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) (x : X) :
    integralRationalStalkMap F Y (latticeScalarSheaf d π Y M) (f x) ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          (rationalLatticeStalkPullbackIso F f M x).hom =
      (inverseImageStalkIso f (latticeScalarSheaf d π Y M) x).hom ≫
        (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
          (inverseImageLatticeScalarIso f M).hom.hom ≫
            integralRationalStalkMap F X
              (latticeScalarSheaf d π X
                ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M)) x := by
  rw [rationalLatticeStalkPullbackIso_hom, Functor.map_comp, ← Category.assoc,
    rationalStalkPullbackIso_integral,
    Category.assoc, ← integralRationalStalkMap_naturality]

namespace LatticePiSheaf

variable [NeZero d] (M : LatticePiSheaf d π Y)

/-- The rational stalk comparison intertwines the actual integral component maps. -/
theorem componentRationalStalkMap_pullback (f : X ⟶ Y) (i : ZMod d) (x : X) :
    M.componentRationalStalkMap F i (f x) ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          (rationalLatticeStalkPullbackIso F f M.sheaf x).hom =
      (inverseImageStalkIso f (M.component i) x).hom ≫
        (M.inverseImage f).componentRationalStalkMap F i x := by
  dsimp only [componentRationalStalkMap]
  rw [Category.assoc, rationalLatticeStalkPullbackIso_integral]
  rw [← Category.assoc, ← Category.assoc, inverseImageStalkIso_naturality]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

/-- The actual component O-lattice is transported by the F-linear rational stalk comparison. -/
theorem componentStalkLattice_pullback (f : X ⟶ Y) (i : ZMod d) (x : X) :
    (M.componentStalkLattice F i (f x)).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map
          (rationalLatticeStalkPullbackIso F f M.sheaf x).hom).hom) =
      (M.inverseImage f).componentStalkLattice F i x := by
  have h := congrArg (fun k => k.hom) (M.componentRationalStalkMap_pullback F f i x)
  ext y
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨(inverseImageStalkIso f (M.component i) x).hom m,
      (congrArg (fun k => k m) h).symm⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨m, rfl⟩ := (inverseImageStalkIso f (M.component i) x).toLinearEquiv.surjective m
    exact ⟨M.componentRationalStalkMap F i (f x) m, ⟨m, rfl⟩,
      congrArg (fun k => k m) h⟩

end LatticePiSheaf

end Langlands.DeligneFormalSpace
