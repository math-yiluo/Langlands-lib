import Langlands.Geometry.FormalGroup.DeligneIsoBaseChange
import Langlands.Geometry.FormalGroup.DeligneInverseImageCoherence

/-! # Coherent inverse image of Deligne's graded and framed lattices -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {W X Y Z : TopCat.{u}}

namespace LatticePiSheaf

/-- Actual total and homogeneous isomorphisms with their inclusion squares
give an isomorphism of graded lattices. -/
def isoOfComponents {M N : LatticePiSheaf d π X} (e : M.sheaf ≅ N.sheaf)
    (c : ∀ i, M.component i ≅ N.component i)
    (hc : ∀ i, (c i).hom ≫ N.inclusion i =
      M.inclusion i ≫ (latticeScalarFunctor d π X).map e.hom) : M ≅ N where
  hom := ⟨e.hom, fun i => (c i).hom, hc⟩
  inv := {
    total := e.inv
    component i := (c i).inv
    inclusion i := by
      apply (cancel_mono ((latticeScalarFunctor d π X).map e.hom)).mp
      rw [Category.assoc, ← hc i, Iso.inv_hom_id_assoc, Category.assoc,
        ← Functor.map_comp, Iso.inv_hom_id]
      exact (congrArg (fun k => N.inclusion i ≫ k)
        ((latticeScalarFunctor d π X).map_id N.sheaf)).trans
        (Category.comp_id (N.inclusion i)) |>.symm }
  hom_inv_id := Hom.ext_total e.hom_inv_id
  inv_hom_id := Hom.ext_total e.inv_hom_id

variable (M : LatticePiSheaf d π Y)

/-- The identity inverse-image comparisons preserve the actual homogeneous inclusions. -/
theorem inverseImageIdIso_inclusion (i : ZMod d) :
    (inverseImageIdIso O Y).hom.app (M.component i) ≫ M.inclusion i =
      (M.inverseImage (𝟙 Y)).inclusion i ≫
        (latticeScalarFunctor d π Y).map
          ((inverseImageIdIso (PiAlgebra d π) Y).hom.app M.sheaf) := by
  have hn := (inverseImageIdIso O Y).hom.naturality (M.inclusion i)
  dsimp only [Functor.id_map] at hn
  have hc :
      (inverseImageLatticeScalarIso (𝟙 Y) M.sheaf).hom ≫
          (latticeScalarFunctor d π Y).map
            ((inverseImageIdIso (PiAlgebra d π) Y).hom.app M.sheaf) =
        (inverseImageIdIso O Y).hom.app (latticeScalarSheaf d π Y M.sheaf) :=
    congrArg (fun e => e.hom.app M.sheaf)
      (inverseImageRestrictionIso_id (algebraMap O (PiAlgebra d π)) Y)
  change _ = (_ ≫ _) ≫ _
  rw [Category.assoc, hc]
  exact hn.symm

/-- Canonical identity inverse image as a genuine graded-lattice isomorphism. -/
def inverseImageIdIso : M.inverseImage (𝟙 Y) ≅ M :=
  isoOfComponents
    ((Langlands.DeligneFormalSpace.inverseImageIdIso (PiAlgebra d π) Y).app M.sheaf)
    (fun i => (Langlands.DeligneFormalSpace.inverseImageIdIso O Y).app (M.component i))
    M.inverseImageIdIso_inclusion

/-- Identity inverse-image comparison is natural for all homogeneous lattice maps. -/
def inverseImageIdNatIso :
    inverseImageFunctor (d := d) (π := π) (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.inverseImageIdIso) (fun g =>
    Hom.ext_total
      ((Langlands.DeligneFormalSpace.inverseImageIdIso (PiAlgebra d π) Y).hom.naturality
        g.total))

/-- Composite inverse-image comparisons preserve the actual homogeneous inclusions. -/
theorem inverseImageCompIso_inclusion (f : X ⟶ Y) (g : W ⟶ X) (i : ZMod d) :
    (inverseImageCompIso O f g).hom.app (M.component i) ≫
        (M.inverseImage (g ≫ f)).inclusion i =
      ((M.inverseImage f).inverseImage g).inclusion i ≫
        (latticeScalarFunctor d π W).map
          ((inverseImageCompIso (PiAlgebra d π) f g).hom.app M.sheaf) := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} O) g
  have hn := (inverseImageCompIso O f g).hom.naturality (M.inclusion i)
  dsimp only [Functor.comp_map] at hn
  have hc :
      (inverseImageCompIso O f g).hom.app (latticeScalarSheaf d π Y M.sheaf) ≫
          (inverseImageLatticeScalarIso (g ≫ f) M.sheaf).hom =
        P.map (inverseImageLatticeScalarIso f M.sheaf).hom ≫
          (inverseImageLatticeScalarIso g (M.inverseImage f).sheaf).hom ≫
          (latticeScalarFunctor d π W).map
            ((inverseImageCompIso (PiAlgebra d π) f g).hom.app M.sheaf) :=
    congrArg (fun e => e.hom.app M.sheaf)
      (inverseImageRestrictionIso_comp (algebraMap O (PiAlgebra d π)) f g)
  change _ ≫ (_ ≫ _) = (P.map (_ ≫ _) ≫ _) ≫ _
  rw [← Category.assoc, ← hn, Category.assoc, hc]
  simp only [P.map_comp, Category.assoc]
  rfl

/-- Canonical iterated inverse image as a genuine graded-lattice isomorphism. -/
def inverseImageCompIso (f : X ⟶ Y) (g : W ⟶ X) :
    (M.inverseImage f).inverseImage g ≅ M.inverseImage (g ≫ f) :=
  isoOfComponents
    ((Langlands.DeligneFormalSpace.inverseImageCompIso (PiAlgebra d π) f g).app M.sheaf)
    (fun i => (Langlands.DeligneFormalSpace.inverseImageCompIso O f g).app (M.component i))
    (M.inverseImageCompIso_inclusion f g)

/-- Composite inverse-image comparison is natural for all homogeneous lattice maps. -/
def inverseImageCompNatIso (f : X ⟶ Y) (g : W ⟶ X) :
    inverseImageFunctor (d := d) (π := π) f ⋙ inverseImageFunctor g ≅
      inverseImageFunctor (g ≫ f) :=
  NatIso.ofComponents (fun M => M.inverseImageCompIso f g) (fun h =>
    Hom.ext_total
      ((Langlands.DeligneFormalSpace.inverseImageCompIso (PiAlgebra d π) f g).hom.naturality
        h.total))

/-- The graded-lattice comparisons satisfy associativity. -/
theorem inverseImageCompIso_assoc (f : X ⟶ Y) (g : W ⟶ X) (h : Z ⟶ W) :
    (inverseImageFunctor h).mapIso (M.inverseImageCompIso f g) ≪≫
        M.inverseImageCompIso (g ≫ f) h =
      (M.inverseImage f).inverseImageCompIso g h ≪≫ M.inverseImageCompIso f (h ≫ g) := by
  apply Iso.ext
  apply Hom.ext_total
  exact congrArg (fun e => e.hom.app M.sheaf) (inverseImage_assoc (PiAlgebra d π) f g h)

/-- The original-base identity is a unit for graded-lattice inverse image. -/
theorem inverseImageCompIso_id_left (f : X ⟶ Y) :
    M.inverseImageCompIso (𝟙 Y) f =
      (inverseImageFunctor f).mapIso M.inverseImageIdIso := by
  apply Iso.ext
  apply Hom.ext_total
  exact congrArg (fun e => e.hom.app M.sheaf) (inverseImage_id_comp (PiAlgebra d π) f)

/-- The new-base identity is a unit for graded-lattice inverse image. -/
theorem inverseImageCompIso_id_right (f : X ⟶ Y) :
    M.inverseImageCompIso f (𝟙 X) = (M.inverseImage f).inverseImageIdIso := by
  apply Iso.ext
  apply Hom.ext_total
  exact congrArg (fun e => e.hom.app M.sheaf) (inverseImage_comp_id (PiAlgebra d π) f)

end LatticePiSheaf

variable {F : Type u} [Field F] [Algebra O F]

namespace FramedLatticePiSheaf

/-- A lattice isomorphism preserving the full frame also preserves it in the
inverse direction. -/
def isoOfLattice {M N : FramedLatticePiSheaf d π X F} (e : M.lattice ≅ N.lattice)
    (hc : M.frame.hom ≫ (rationalSheafFunctor F X).map (e.hom.component 0) =
      N.frame.hom) : M ≅ N where
  hom := ⟨e.hom, hc⟩
  inv := {
    lattice := e.inv
    frame := by
      have hi : e.hom.component 0 ≫ e.inv.component 0 = 𝟙 _ :=
        congrArg (fun g => g.component 0) e.hom_inv_id
      rw [← hc, Category.assoc, ← Functor.map_comp, hi]
      exact (congrArg (fun k => M.frame.hom ≫ k)
        ((rationalSheafFunctor F X).map_id (M.lattice.component 0))).trans
        (Category.comp_id M.frame.hom) }
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

variable (M : FramedLatticePiSheaf d π Y F)

/-- The identity comparison preserves the full rational frame. -/
theorem inverseImageIdIso_frame :
    (M.inverseImage (𝟙 Y)).frame.hom ≫
        (rationalSheafFunctor F Y).map (M.lattice.inverseImageIdIso.hom.component 0) =
      M.frame.hom := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} F) (𝟙 Y)
  let c := (inverseImageConstantIso (O := F) (𝟙 Y)).app
    (ModuleCat.of F (Fin d → F))
  let r := (inverseImageRationalIso (F := F) (𝟙 Y)).app (M.lattice.component 0)
  have hr :
      r.hom ≫ (rationalSheafFunctor F Y).map
          ((inverseImageIdIso O Y).hom.app (M.lattice.component 0)) =
        (inverseImageIdIso F Y).hom.app (M.lattice.rationalComponent F 0) :=
    congrArg (fun e => e.hom.app (M.lattice.component 0))
      (inverseImageRationalIso_id (F := F) Y)
  have hc : c.hom = (inverseImageIdIso F Y).hom.app
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} F)).obj
        (ModuleCat.of F (Fin d → F))) :=
    congrArg (fun e => e.hom.app (ModuleCat.of F (Fin d → F)))
      (inverseImageConstantIso_id F Y)
  have hn := (inverseImageIdIso F Y).hom.naturality M.frame.hom
  dsimp only [Functor.id_map] at hn
  change ((c.inv ≫ P.map M.frame.hom) ≫ r.hom) ≫
    (rationalSheafFunctor F Y).map
      ((inverseImageIdIso O Y).hom.app (M.lattice.component 0)) = _
  rw [Category.assoc, hr, Category.assoc, hn, ← hc, Iso.inv_hom_id_assoc]

/-- Identity inverse image is a genuine frame-preserving isomorphism. -/
def inverseImageIdIso : M.inverseImage (𝟙 Y) ≅ M :=
  isoOfLattice M.lattice.inverseImageIdIso M.inverseImageIdIso_frame

/-- The identity comparison is natural for all frame-preserving morphisms. -/
def inverseImageIdNatIso :
    inverseImageFunctor (d := d) (π := π) (F := F) (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.inverseImageIdIso) (fun g =>
    Hom.ext (LatticePiSheaf.inverseImageIdNatIso.hom.naturality g.lattice))

/-- The composition comparison preserves the full rational frame. -/
theorem inverseImageCompIso_frame (f : X ⟶ Y) (g : W ⟶ X) :
    ((M.inverseImage f).inverseImage g).frame.hom ≫
        (rationalSheafFunctor F W).map
          ((M.lattice.inverseImageCompIso f g).hom.component 0) =
      (M.inverseImage (g ≫ f)).frame.hom := by
  let Pf := TopCat.Sheaf.pullback (ModuleCat.{u} F) f
  let Pg := TopCat.Sheaf.pullback (ModuleCat.{u} F) g
  let Pgf := TopCat.Sheaf.pullback (ModuleCat.{u} F) (g ≫ f)
  let V := ModuleCat.of F (Fin d → F)
  let cf := (inverseImageConstantIso (O := F) f).app V
  let cg := (inverseImageConstantIso (O := F) g).app V
  let cgf := (inverseImageConstantIso (O := F) (g ≫ f)).app V
  let rf := (inverseImageRationalIso (F := F) f).app (M.lattice.component 0)
  let rg := (inverseImageRationalIso (F := F) g).app ((M.lattice.inverseImage f).component 0)
  let rgf := (inverseImageRationalIso (F := F) (g ≫ f)).app (M.lattice.component 0)
  let eQ := (Langlands.DeligneFormalSpace.inverseImageCompIso F f g).app
    (M.lattice.rationalComponent F 0)
  let eC := (Langlands.DeligneFormalSpace.inverseImageCompIso F f g).app
    ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} F)).obj V)
  have hr : eQ.hom ≫ rgf.hom =
      Pg.map rf.hom ≫ rg.hom ≫ (rationalSheafFunctor F W).map
        ((Langlands.DeligneFormalSpace.inverseImageCompIso O f g).hom.app
          (M.lattice.component 0)) :=
    congrArg (fun e => e.hom.app (M.lattice.component 0))
      (inverseImageRationalIso_comp (F := F) f g)
  have hc : cgf.inv ≫ eC.inv = cg.inv ≫ Pg.map cf.inv :=
    congrArg (fun e => e.inv.app V) (inverseImageConstantIso_comp F f g)
  have hn : Pg.map (Pf.map M.frame.hom) ≫ eQ.hom =
      eC.hom ≫ Pgf.map M.frame.hom :=
    (Langlands.DeligneFormalSpace.inverseImageCompIso F f g).hom.naturality
      M.frame.hom
  change ((cg.inv ≫ Pg.map ((cf.inv ≫ Pf.map M.frame.hom) ≫ rf.hom)) ≫ rg.hom) ≫
      (rationalSheafFunctor F W).map
        ((Langlands.DeligneFormalSpace.inverseImageCompIso O f g).hom.app
          (M.lattice.component 0)) =
    (cgf.inv ≫ Pgf.map M.frame.hom) ≫ rgf.hom
  calc
    _ = (cg.inv ≫ Pg.map cf.inv) ≫ Pg.map (Pf.map M.frame.hom) ≫
        (Pg.map rf.hom ≫ rg.hom ≫ (rationalSheafFunctor F W).map
          ((Langlands.DeligneFormalSpace.inverseImageCompIso O f g).hom.app
            (M.lattice.component 0))) := by
      simp only [Pg.map_comp, Category.assoc]
    _ = (cg.inv ≫ Pg.map cf.inv) ≫ Pg.map (Pf.map M.frame.hom) ≫
        (eQ.hom ≫ rgf.hom) := by rw [hr]
    _ = (cg.inv ≫ Pg.map cf.inv) ≫
        (eC.hom ≫ Pgf.map M.frame.hom) ≫ rgf.hom := by
      rw [← Category.assoc (Pg.map (Pf.map M.frame.hom)), hn]
    _ = (cgf.inv ≫ eC.inv) ≫
        (eC.hom ≫ Pgf.map M.frame.hom) ≫ rgf.hom := by rw [hc]
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Composite inverse image is a genuine frame-preserving isomorphism. -/
def inverseImageCompIso (f : X ⟶ Y) (g : W ⟶ X) :
    (M.inverseImage f).inverseImage g ≅ M.inverseImage (g ≫ f) :=
  isoOfLattice (M.lattice.inverseImageCompIso f g) (M.inverseImageCompIso_frame f g)

/-- The composition comparison is natural for all frame-preserving morphisms. -/
def inverseImageCompNatIso (f : X ⟶ Y) (g : W ⟶ X) :
    inverseImageFunctor (d := d) (π := π) (F := F) f ⋙ inverseImageFunctor g ≅
      inverseImageFunctor (g ≫ f) :=
  NatIso.ofComponents (fun M => M.inverseImageCompIso f g) (fun h =>
    Hom.ext ((LatticePiSheaf.inverseImageCompNatIso f g).hom.naturality h.lattice))

/-- The framed-lattice comparisons satisfy associativity. -/
theorem inverseImageCompIso_assoc (f : X ⟶ Y) (g : W ⟶ X) (h : Z ⟶ W) :
    (inverseImageFunctor h).mapIso (M.inverseImageCompIso f g) ≪≫
        M.inverseImageCompIso (g ≫ f) h =
      (M.inverseImage f).inverseImageCompIso g h ≪≫ M.inverseImageCompIso f (h ≫ g) := by
  apply Iso.ext
  apply Hom.ext
  exact M.lattice.inverseImageCompIso_assoc f g h
    |> congrArg Iso.hom

/-- The original-base identity is a unit for framed-lattice inverse image. -/
theorem inverseImageCompIso_id_left (f : X ⟶ Y) :
    M.inverseImageCompIso (𝟙 Y) f =
      (inverseImageFunctor f).mapIso M.inverseImageIdIso := by
  apply Iso.ext
  apply Hom.ext
  exact congrArg Iso.hom (M.lattice.inverseImageCompIso_id_left f)

/-- The new-base identity is a unit for framed-lattice inverse image. -/
theorem inverseImageCompIso_id_right (f : X ⟶ Y) :
    M.inverseImageCompIso f (𝟙 X) = (M.inverseImage f).inverseImageIdIso := by
  apply Iso.ext
  apply Hom.ext
  exact congrArg Iso.hom (M.lattice.inverseImageCompIso_id_right f)

end FramedLatticePiSheaf

end Langlands.DeligneFormalSpace
