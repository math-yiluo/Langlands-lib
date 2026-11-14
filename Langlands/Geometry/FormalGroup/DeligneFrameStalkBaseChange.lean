import Langlands.Geometry.FormalGroup.DeligneRationalStalkBaseChange

/-! # Actual frame compatibility on pulled stalks -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O : Type u} [CommRing O] {X Y : TopCat.{u}}

/-- The actual inverse-image constant comparison preserves the global constant unit. -/
theorem inverseImageConstantIso_unit (f : X ⟶ Y) (V : ModuleCat.{u} O) :
    (toSheafify (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).obj V)).app (.op ⊤) ≫
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f).unit.app
          ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} O)).obj V)).hom.app
            (.op ⊤)) ≫
              ((inverseImageConstantIso (O := O) f).hom.app V).hom.app (.op ⊤) =
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj V)).app (.op ⊤) := by
  let A := (constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{u} O)
    (topOpenIsTerminal Y)).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f)
  let B := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} O)
    (topOpenIsTerminal X)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app A B V
  simp only [Adjunction.homEquiv_unit] at h
  exact h

variable {F : Type u} [Field F] [Algebra O F]
variable (F) {d : ℕ} {π : O}

/-- The total rational lattice stalk comparison on actual germs. -/
theorem rationalLatticeStalkPullbackIso_germ (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π)))
    (x : X) (U : Opens Y) (hx : f x ∈ U) :
    TopCat.Presheaf.germ (rationalLattice F Y d π M).obj U (f x) hx ≫
        (rationalLatticeStalkPullbackIso F f M x).hom =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} F) f).unit.app
        (rationalLattice F Y d π M)).hom.app (.op U)) ≫
          (inverseImageRationalLatticeIso F f M).hom.hom.app
            (.op ((Opens.map f).obj U)) ≫
              TopCat.Presheaf.germ
                (rationalLattice F X d π
                  ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M)).obj
                    ((Opens.map f).obj U) x hx := by
  dsimp only [rationalLatticeStalkPullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.comp_map]
  rw [← Category.assoc, inverseImageStalkIso_germ, Category.assoc,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

namespace LatticePiSheaf

variable [NeZero d] (M : LatticePiSheaf d π Y)

/-- The actual rationalized inclusion is preserved by the total rational comparison. -/
theorem rationalInclusion_pullback (f : X ⟶ Y) (i : ZMod d) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map (M.rationalInclusion F i) ≫
        (inverseImageRationalLatticeIso F f M.sheaf).hom =
      (inverseImageRationalIso (F := F) f).hom.app (M.component i) ≫
        (M.inverseImage f).rationalInclusion F i := by
  change (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
      ((rationalSheafFunctor F Y).map (M.inclusion i)) ≫
        ((inverseImageRationalIso (F := F) f).hom.app
          (latticeScalarSheaf d π Y M.sheaf) ≫
            (rationalSheafFunctor F X).map (inverseImageLatticeScalarIso f M.sheaf).hom) =
      (inverseImageRationalIso (F := F) f).hom.app (M.component i) ≫
        (rationalSheafFunctor F X).map
          ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (M.inclusion i) ≫
            (inverseImageLatticeScalarIso f M.sheaf).hom)
  rw [← Category.assoc, inverseImageRationalIso_naturality, Category.assoc,
    ← Functor.map_comp]

end LatticePiSheaf

namespace FramedLatticePiSheaf

variable [NeZero d] (M : FramedLatticePiSheaf d π Y F)

/-- The actual frame into the total rational sheaf is preserved by inverse image. -/
theorem frameToTotal_pullback (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map (M.frameToTotal F) ≫
        (inverseImageRationalLatticeIso F f M.lattice.sheaf).hom =
      (inverseImageConstantIso (O := F) f).hom.app (ModuleCat.of F (Fin d → F)) ≫
        (M.inverseImage f).frameToTotal F := by
  calc
    _ = (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map M.frame.hom ≫
        (inverseImageRationalIso (F := F) f).hom.app (M.lattice.component 0) ≫
          (M.lattice.inverseImage f).rationalInclusion F 0 := by
      change (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
        (M.frame.hom ≫ M.lattice.rationalInclusion F 0) ≫ _ = _
      rw [Functor.map_comp, Category.assoc,
        LatticePiSheaf.rationalInclusion_pullback F M.lattice f 0]
    _ = _ := by
      change _ =
        ((inverseImageConstantIso (O := F) f).app (ModuleCat.of F (Fin d → F))).hom ≫
          ((((inverseImageConstantIso (O := F) f).app
            (ModuleCat.of F (Fin d → F))).inv ≫
              (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map M.frame.hom) ≫
                ((inverseImageRationalIso (F := F) f).app (M.lattice.component 0)).hom) ≫
                  (M.lattice.inverseImage f).rationalInclusion F 0
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rfl

/-- Transport of the original rational frame germ by the actual total stalk comparison. -/
def frameStalkPullbackMap (f : X ⟶ Y) (x : X) :
    ModuleCat.of F (Fin d → F) ⟶
      rationalLatticeStalk F X d π (M.inverseImage f).lattice.sheaf x :=
  M.frameStalkMap F (f x) ≫
    (rationalLatticeStalkPullbackIso F f M.lattice.sheaf x).hom

/-- The actual stalk frame of the pulled lattice is the transported original frame. -/
theorem frameStalkPullbackMap_eq (f : X ⟶ Y) (x : X) :
    M.frameStalkPullbackMap F f x = (M.inverseImage f).frameStalkMap F x := by
  have h := congrArg (fun k => k.hom.app (.op ⊤))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} F) f).unit.naturality
      (M.frameToTotal F))
  change (M.frameToTotal F).hom.app (.op ⊤) ≫
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} F) f).unit.app
        (rationalLattice F Y d π M.lattice.sheaf)).hom.app (.op ⊤)) =
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} F) f).unit.app
      ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} F)).obj
        (ModuleCat.of F (Fin d → F)))).hom.app (.op ⊤)) ≫
      ((TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map (M.frameToTotal F)).hom.app
        (.op ((Opens.map f).obj ⊤)) at h
  have h₂ := congrArg (fun k => k.hom.app (.op ((Opens.map f).obj ⊤)))
    (M.frameToTotal_pullback F f)
  change ((TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
      (M.frameToTotal F)).hom.app (.op ((Opens.map f).obj ⊤)) ≫
        (inverseImageRationalLatticeIso F f M.lattice.sheaf).hom.hom.app
          (.op ((Opens.map f).obj ⊤)) =
    ((inverseImageConstantIso (O := F) f).hom.app
      (ModuleCat.of F (Fin d → F))).hom.app (.op ((Opens.map f).obj ⊤)) ≫
        ((M.inverseImage f).frameToTotal F).hom.app
          (.op ((Opens.map f).obj ⊤)) at h₂
  dsimp only [frameStalkPullbackMap, frameStalkMap, TopCat.Presheaf.Γgerm]
  simp only [Category.assoc]
  rw [rationalLatticeStalkPullbackIso_germ]
  rw [← Category.assoc ((M.frameToTotal F).hom.app (.op ⊤)), h]
  simp only [Category.assoc]
  rw [← Category.assoc
      (((TopCat.Sheaf.pullback (ModuleCat.{u} F) f).map
        (M.frameToTotal F)).hom.app (.op ((Opens.map f).obj ⊤)))]
  rw [h₂]
  have h₃ := inverseImageConstantIso_unit (O := F) f (ModuleCat.of F (Fin d → F))
  simp only [← Category.assoc] at h₃
  simp only [Opens.map_top, ← Category.assoc]
  rw [h₃]
  rfl

/-- The actual comparison preserves the images of O-valued frame vectors. -/
theorem integralFrameStalkMap_pullback (f : X ⟶ Y) (x : X) :
    (((ModuleCat.restrictScalars (algebraMap O F)).map
      (rationalLatticeStalkPullbackIso F f M.lattice.sheaf x).hom).hom).comp
        (M.integralFrameStalkMap F (f x)) =
      (M.inverseImage f).integralFrameStalkMap F x := by
  apply LinearMap.ext
  intro v
  exact congrArg (fun k => k (fun j => algebraMap O F (v j)))
    (M.frameStalkPullbackMap_eq F f x)

/-- The actual frame O-lattice is carried to the actual pulled frame O-lattice. -/
theorem frameStalkLattice_pullback (f : X ⟶ Y) (x : X) :
    (M.frameStalkLattice F (f x)).map
        (((ModuleCat.restrictScalars (algebraMap O F)).map
          (rationalLatticeStalkPullbackIso F f M.lattice.sheaf x).hom).hom) =
      (M.inverseImage f).frameStalkLattice F x := by
  have h := M.integralFrameStalkMap_pullback F f x
  ext y
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, (congrArg (fun k => k v) h).symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨M.integralFrameStalkMap F (f x) v, ⟨v, rfl⟩,
      congrArg (fun k => k v) h⟩

end FramedLatticePiSheaf

end Langlands.DeligneFormalSpace
