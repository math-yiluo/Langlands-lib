import Langlands.Geometry.FormalGroup.DelignePreDatumBaseChange
import Langlands.Geometry.FormalGroup.DeligneIsomorphism

/-! # Base change of morphisms of Deligne's four sheaf data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {X Y : TopCat.{u}} {F : Type u} [Field F] [Algebra O F]

omit [NeZero d] in
/-- The coefficient comparison is natural for actual total lattice morphisms. -/
theorem inverseImageLatticeScalarIso_naturality (f : X ⟶ Y)
    {M N : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))} (g : M ⟶ N) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map
        ((latticeScalarFunctor d π Y).map g) ≫
      (inverseImageLatticeScalarIso f N).hom =
    (inverseImageLatticeScalarIso f M).hom ≫
      (latticeScalarFunctor d π X).map
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).map g) :=
  (inverseImageRestrictionIso (algebraMap O (PiAlgebra d π)) f).hom.naturality g

omit [NeZero d] in
/-- The inverse coefficient comparison is natural for total lattice morphisms. -/
theorem inverseImageLatticeScalarIso_inv_naturality (f : X ⟶ Y)
    {M N : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))} (g : M ⟶ N) :
    (latticeScalarFunctor d π X).map
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).map g) ≫
      (inverseImageLatticeScalarIso f N).inv =
    (inverseImageLatticeScalarIso f M).inv ≫
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map
        ((latticeScalarFunctor d π Y).map g) :=
  (inverseImageRestrictionIso (algebraMap O (PiAlgebra d π)) f).inv.naturality g

namespace LatticePiSheaf

/-- Actual inverse image of a coefficient-linear homogeneous lattice morphism. -/
def inverseImageMap (f : X ⟶ Y) {M N : LatticePiSheaf d π Y} (g : M ⟶ N) :
    M.inverseImage f ⟶ N.inverseImage f where
  total := (TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).map g.total
  component i := (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (g.component i)
  inclusion i := by
    change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
    rw [← Category.assoc, ← Functor.map_comp, g.inclusion, Functor.map_comp,
      Category.assoc, inverseImageLatticeScalarIso_naturality, ← Category.assoc]

/-- Inverse image is a functor on the actual graded flat lattices. -/
def inverseImageFunctor (f : X ⟶ Y) :
    LatticePiSheaf d π Y ⥤ LatticePiSheaf d π X where
  obj M := M.inverseImage f
  map g := inverseImageMap f g
  map_id M := Hom.ext_total
    ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).map_id M.sheaf)
  map_comp g h := Hom.ext_total
    ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).map_comp g.total h.total)

end LatticePiSheaf

namespace FramedLatticePiSheaf

/-- Actual inverse image preserves the complete rational frame. -/
def inverseImageMap (f : X ⟶ Y) {M N : FramedLatticePiSheaf d π Y F}
    (g : M ⟶ N) : M.inverseImage f ⟶ N.inverseImage f where
  lattice := LatticePiSheaf.inverseImageMap f g.lattice
  frame := by
    let P := TopCat.Sheaf.pullback (ModuleCat.{u} F) f
    let c := (inverseImageConstantIso (O := F) f).app (ModuleCat.of F (Fin d → F))
    let rM := (inverseImageRationalIso (F := F) f).app (M.lattice.component 0)
    let rN := (inverseImageRationalIso (F := F) f).app (N.lattice.component 0)
    change ((c.inv ≫ P.map M.frame.hom) ≫ rM.hom) ≫
        (rationalSheafFunctor F X).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (g.lattice.component 0)) =
      (c.inv ≫ P.map N.frame.hom) ≫ rN.hom
    calc
      _ = (c.inv ≫ P.map M.frame.hom) ≫
          (P.map ((rationalSheafFunctor F Y).map (g.lattice.component 0)) ≫ rN.hom) :=
        congrArg (fun k => (c.inv ≫ P.map M.frame.hom) ≫ k)
          (inverseImageRationalIso_naturality f (g.lattice.component 0)).symm
      _ = (c.inv ≫ P.map
          (M.frame.hom ≫ (rationalSheafFunctor F Y).map (g.lattice.component 0))) ≫
            rN.hom := by simp only [P.map_comp, Category.assoc]
      _ = _ := congrArg (fun k => (c.inv ≫ P.map k) ≫ rN.hom) g.frame

/-- Inverse image is functorial on framed graded flat lattices. -/
def inverseImageFunctor (f : X ⟶ Y) :
    FramedLatticePiSheaf d π Y F ⥤ FramedLatticePiSheaf d π X F where
  obj M := M.inverseImage f
  map g := inverseImageMap f g
  map_id M := Hom.ext ((LatticePiSheaf.inverseImageFunctor f).map_id M.lattice)
  map_comp g h := Hom.ext
    ((LatticePiSheaf.inverseImageFunctor f).map_comp g.lattice h.lattice)

end FramedLatticePiSheaf

variable {S S' : Scheme.{u}}

namespace GradedPiSheaf

variable {a : Γ(S, ⊤)}

/-- Structural pullback of an actual homogeneous Pi-compatible map. -/
def pullbackMap (f : S' ⟶ S)
    {M N : GradedPiSheaf d S.sheaf (schemeScalar S a)} (g : M ⟶ N) :
    M.pullback f ⟶ N.pullback f where
  val := {
    val := (Scheme.Modules.pullback f).map g.val.val
    comm := by
      change (Scheme.Modules.pullback f).map M.pi ≫
          (Scheme.Modules.pullback f).map g.val.val =
        (Scheme.Modules.pullback f).map g.val.val ≫
          (Scheme.Modules.pullback f).map N.pi
      rw [← Functor.map_comp, g.val.comm, Functor.map_comp] }
  homogeneous U i x hx := by
    obtain ⟨t, rfl⟩ := hx
    refine ⟨((Scheme.Modules.pullback f).map (g.componentMap i)).val.app U t, ?_⟩
    have h := congrArg (fun k => (Scheme.Modules.pullback f).map k)
      (g.componentMap_inclusion i)
    rw [Functor.map_comp, Functor.map_comp] at h
    exact congrArg (fun k => k.val.app U t) h

/-- Structural pullback is a functor on graded Pi sheaves. -/
def pullbackFunctor (f : S' ⟶ S) :
    GradedPiSheaf d S.sheaf (schemeScalar S a) ⥤
      GradedPiSheaf d S'.sheaf (schemeScalar S' (f.appTop a)) where
  obj M := M.pullback f
  map g := pullbackMap f g
  map_id M := Hom.ext (PiSheaf.Hom.ext ((Scheme.Modules.pullback f).map_id M.module))
  map_comp g h := Hom.ext (PiSheaf.Hom.ext
    ((Scheme.Modules.pullback f).map_comp g.val.val h.val.val))

end GradedPiSheaf

namespace SheafPreDatum

variable {φ : O →+* Γ(S, ⊤)}

/-- Pullback of an actual four-data morphism preserves its total u square. -/
theorem pullbackMap_u (f : S' ⟶ S) {D E : SheafPreDatum d π F φ} (g : D ⟶ E) :
    (latticeScalarFunctor d π (S' : TopCat)).map
        (LatticePiSheaf.inverseImageMap f.base g.eta.lattice).total ≫ E.pullbackU f =
      D.pullbackU f ≫ (structuralOSheafFunctor S' (pulledGlobalScalar f φ)).map
        (GradedPiSheaf.pullbackMap f g.tangent).val.val := by
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} O) f.base
  let G := structuralOSheafFunctor S' (pulledGlobalScalar f φ)
  let c := structuralPullbackComparison f φ
  let eD := inverseImageLatticeScalarIso f.base D.eta.lattice.sheaf
  let eE := inverseImageLatticeScalarIso f.base E.eta.lattice.sheaf
  have hs := inverseImageLatticeScalarIso_inv_naturality f.base g.eta.lattice.total
  have hc := c.naturality g.tangent.val.val
  dsimp only [Functor.comp_map] at hc
  change _ ≫ (eE.inv ≫ (P.map E.u ≫ c.app E.tangent.graded.module)) =
    (eD.inv ≫ (P.map D.u ≫ c.app D.tangent.graded.module)) ≫
      G.map ((Scheme.Modules.pullback f).map g.tangent.val.val)
  rw [← Category.assoc]
  calc
    _ = (eD.inv ≫ P.map
        ((latticeScalarFunctor d π (S : TopCat)).map g.eta.lattice.total)) ≫
          (P.map E.u ≫ c.app E.tangent.graded.module) :=
      congrArg (fun k => k ≫ (P.map E.u ≫ c.app E.tangent.graded.module)) hs
    _ = eD.inv ≫ P.map
        ((latticeScalarFunctor d π (S : TopCat)).map g.eta.lattice.total ≫ E.u) ≫
          c.app E.tangent.graded.module := by
      simp only [P.map_comp, Category.assoc]
    _ = eD.inv ≫ P.map (D.u ≫
        (structuralOSheafFunctor S φ).map g.tangent.val.val) ≫
          c.app E.tangent.graded.module :=
      congrArg (fun k => eD.inv ≫ P.map k ≫ c.app E.tangent.graded.module) g.u
    _ = eD.inv ≫ P.map D.u ≫
        (P.map ((structuralOSheafFunctor S φ).map g.tangent.val.val) ≫
          c.app E.tangent.graded.module) := by
      simp only [P.map_comp, Category.assoc]
    _ = eD.inv ≫ P.map D.u ≫
        (c.app D.tangent.graded.module ≫
          G.map ((Scheme.Modules.pullback f).map g.tangent.val.val)) :=
      congrArg (fun k => eD.inv ≫ P.map D.u ≫ k) hc
    _ = _ := by simp only [Category.assoc]

/-- Actual pullback of morphisms preserving eta, T, u and the rational frame. -/
def pullbackMap (f : S' ⟶ S) {D E : SheafPreDatum d π F φ} (g : D ⟶ E) :
    D.pullback f ⟶ E.pullback f where
  eta := FramedLatticePiSheaf.inverseImageMap f.base g.eta
  tangent := GradedPiSheaf.pullbackMap f g.tangent
  u := pullbackMap_u f g

/-- For a fixed scheme map the actual four-data pullback is a functor. -/
def pullbackFunctor (f : S' ⟶ S) :
    SheafPreDatum d π F φ ⥤ SheafPreDatum d π F (pulledGlobalScalar f φ) where
  obj D := D.pullback f
  map g := pullbackMap f g
  map_id D := Hom.ext
    ((FramedLatticePiSheaf.inverseImageFunctor f.base).map_id D.eta)
    ((GradedPiSheaf.pullbackFunctor f).map_id D.tangent.graded)
  map_comp g h := Hom.ext
    ((FramedLatticePiSheaf.inverseImageFunctor f.base).map_comp g.eta h.eta)
    ((GradedPiSheaf.pullbackFunctor f).map_comp g.tangent h.tangent)

/-- Pullback takes a genuine isomorphism to one preserving all four pulled data. -/
def pullbackIso (f : S' ⟶ S) {D E : SheafPreDatum d π F φ} (e : D ≅ E) :
    D.pullback f ≅ E.pullback f :=
  (pullbackFunctor f).mapIso e

namespace IsoClass

/-- Actual pullback is well defined on the preliminary isomorphism classes. -/
def pullback (f : S' ⟶ S) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) →
      IsoClass (d := d) (π := π) (F := F) (φ := pulledGlobalScalar f φ) :=
  Quotient.map (fun D => D.pullback f) (fun _ _ ⟨e⟩ => ⟨pullbackIso f e⟩)

@[simp]
theorem pullback_mk (f : S' ⟶ S) (D : SheafPreDatum d π F φ) :
    pullback f (mk D) = mk (D.pullback f) := rfl

end IsoClass

end SheafPreDatum

end Langlands.DeligneFormalSpace
