import Langlands.Geometry.FormalGroup.DeligneIntegerShift
import Langlands.Geometry.FormalGroup.DeligneLatticeBaseChange

/-! # Coherence and inverse equivalences for actual integer Deligne shifts -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

section Graded

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {a : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}

namespace GradedPiSheaf

variable (M : GradedPiSheaf d R a)

/-- The integer zero shift has identity maps on the actual total Pi sheaf. -/
def shiftIntZeroIso : M.shift ((0 : ℤ) : ZMod d) ≅ M where
  hom := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component i).toSubmodule.obj U
      simpa only [shift, Int.cast_zero, add_zero] using hx }
  inv := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component (i + ((0 : ℤ) : ZMod d))).toSubmodule.obj U
      simpa only [Int.cast_zero, add_zero] using hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

/-- Integer addition identifies successive tangent shifts by total identity maps. -/
def shiftIntAddIso (k l : ℤ) :
    (M.shift (k : ZMod d)).shift (l : ZMod d) ≅ M.shift ((k + l : ℤ) : ZMod d) where
  hom := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component (i + ((k + l : ℤ) : ZMod d))).toSubmodule.obj U
      simpa only [shift, Int.cast_add, add_assoc, add_comm, add_left_comm] using hx }
  inv := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component ((i + (l : ZMod d)) + (k : ZMod d))).toSubmodule.obj U
      simpa only [shift, Int.cast_add, add_assoc, add_comm, add_left_comm] using hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

end GradedPiSheaf

end Graded

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {X : TopCat.{u}} (F : Type u) [Field F] [Algebra O F]

namespace LatticePiSheaf

variable (M : LatticePiSheaf d π X)

/-- Rationalization preserves the actual homogeneous splitting, without a flatness premise. -/
def rationalInclusionSplitMono (i : ZMod d) : SplitMono (M.rationalInclusion F i) where
  retraction := (rationalSheafFunctor F X).map (M.projection i)
  id := by
    rw [rationalInclusion, ← Functor.map_comp, M.inclusion_projection]
    exact (rationalSheafFunctor F X).map_id _

/-- Every rational homogeneous inclusion is split monic by its actual projection. -/
instance rationalInclusion_isSplitMono (i : ZMod d) :
    IsSplitMono (M.rationalInclusion F i) :=
  IsSplitMono.mk' (M.rationalInclusionSplitMono F i)

omit [NeZero d] in
/-- Rationalized genuine component maps respect the actual total inclusion. -/
@[reassoc]
theorem Hom.rationalInclusion {M N : LatticePiSheaf d π X} (f : M ⟶ N)
    (i : ZMod d) :
    (rationalSheafFunctor F X).map (f.component i) ≫ N.rationalInclusion F i =
      M.rationalInclusion F i ≫
        (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map f.total) := by
  rw [LatticePiSheaf.rationalInclusion, LatticePiSheaf.rationalInclusion,
    ← Functor.map_comp, f.inclusion, Functor.map_comp]

/-- The integer zero shift has actual index-transport maps and total identity. -/
def shiftIntZeroIso : M.shift ((0 : ℤ) : ZMod d) ≅ M := by
  have hi (i : ZMod d) : i + ((0 : ℤ) : ZMod d) = i := by simp
  exact {
    hom := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i))
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i)).trans
          ((congrArg (fun t => M.inclusion (i + ((0 : ℤ) : ZMod d)) ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    inv := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i).symm)
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i).symm).trans
          ((congrArg (fun t => M.inclusion i ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    hom_inv_id := Hom.ext_total (Category.id_comp _)
    inv_hom_id := Hom.ext_total (Category.id_comp _) }

/-- Successive integer degree shifts compare by actual index transports and total identity. -/
def shiftIntAddIso (k l : ℤ) :
    (M.shift (k : ZMod d)).shift (l : ZMod d) ≅ M.shift ((k + l : ℤ) : ZMod d) := by
  have hi (i : ZMod d) : (i + (l : ZMod d)) + (k : ZMod d) =
      i + ((k + l : ℤ) : ZMod d) := by
    rw [Int.cast_add]
    abel
  exact {
    hom := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i))
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i)).trans
          ((congrArg (fun t => M.inclusion ((i + (l : ZMod d)) + (k : ZMod d)) ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    inv := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i).symm)
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i).symm).trans
          ((congrArg (fun t => M.inclusion (i + ((k + l : ℤ) : ZMod d)) ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    hom_inv_id := Hom.ext_total (Category.id_comp _)
    inv_hom_id := Hom.ext_total (Category.id_comp _) }

end LatticePiSheaf

namespace FramedLatticePiSheaf

omit [NeZero d] in
/-- The frame-preserving square can be checked in the actual total rational lattice. -/
theorem frame_iff_total {M N : FramedLatticePiSheaf d π X F}
    (f : M.lattice ⟶ N.lattice) :
    M.frame.hom ≫ (rationalSheafFunctor F X).map (f.component 0) = N.frame.hom ↔
      M.frameToTotal F ≫
          (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map f.total) =
        N.frameToTotal F := by
  rw [← cancel_mono (N.lattice.rationalInclusion F 0)]
  simp only [Category.assoc, LatticePiSheaf.Hom.rationalInclusion,
    frameToTotal]

/-- A genuine lattice isomorphism preserving the total frame lifts to the framed category. -/
def isoOfTotalFrame {M N : FramedLatticePiSheaf d π X F}
    (e : M.lattice ≅ N.lattice)
    (h : M.frameToTotal F ≫
      (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map e.hom.total) =
        N.frameToTotal F) : M ≅ N where
  hom := { lattice := e.hom, frame := (frame_iff_total F e.hom).mpr h }
  inv := {
    lattice := e.inv
    frame := by
      have he := (frame_iff_total F e.hom).mpr h
      rw [← he, Category.assoc, ← Functor.map_comp]
      have hc : e.hom.component 0 ≫ e.inv.component 0 = 𝟙 _ :=
        congrArg (fun f => f.component 0) e.hom_inv_id
      rw [hc]
      exact (congrArg (fun t => M.frame.hom ≫ t)
        ((rationalSheafFunctor F X).map_id _)).trans (Category.comp_id _) }
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

variable (M : FramedLatticePiSheaf d π X F) (hπ : algebraMap O F π ≠ 0)

omit [NeZero d] in
/-- The total frame followed by rationalization of the total identity is unchanged. -/
theorem frameToTotal_comp_totalId :
    M.frameToTotal F ≫ (rationalSheafFunctor F X).map
        ((latticeScalarFunctor d π X).map (𝟙 M.lattice.sheaf)) =
      M.frameToTotal F :=
  (congrArg (fun t => M.frameToTotal F ≫ (rationalSheafFunctor F X).map t)
    ((latticeScalarFunctor d π X).map_id _)).trans
    ((congrArg (fun t => M.frameToTotal F ≫ t)
      ((rationalSheafFunctor F X).map_id _)).trans (Category.comp_id _))

/-- The constructed zero shift preserves the full frame through the total identity. -/
def shiftIntZeroIso : M.shiftInt F hπ 0 ≅ M :=
  isoOfTotalFrame F M.lattice.shiftIntZeroIso (by
    change (M.shiftInt F hπ 0).frameToTotal F ≫
      (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map (𝟙 _)) = _
    rw [frameToTotal_comp_totalId, M.frameToTotal_shiftInt]
    simp only [zpow_zero]
    exact Category.comp_id _)

/-- Successive constructed integer frames compare with the summed frame. -/
def shiftIntAddIso (k l : ℤ) :
    (M.shiftInt F hπ k).shiftInt F hπ l ≅ M.shiftInt F hπ (k + l) :=
  isoOfTotalFrame F (M.lattice.shiftIntAddIso k l) (by
    change ((M.shiftInt F hπ k).shiftInt F hπ l).frameToTotal F ≫
      (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map (𝟙 _)) = _
    rw [frameToTotal_comp_totalId,
      frameToTotal_shiftInt, M.frameToTotal_shiftInt, M.frameToTotal_shiftInt,
      Category.assoc]
    congr 1
    rw [add_comm k l, zpow_add]
    rfl)

/-- Opposite integer shifts cancel through actual lattice maps with total identity. -/
def shiftIntCancelIso (k l : ℤ) (h : k + l = 0) :
    (M.shiftInt F hπ k).shiftInt F hπ l ≅ M :=
  isoOfTotalFrame F
    (M.lattice.shiftCancelIso (k : ZMod d) (l : ZMod d)
      (by rw [← Int.cast_add, h, Int.cast_zero])) (by
    change ((M.shiftInt F hπ k).shiftInt F hπ l).frameToTotal F ≫
      (rationalSheafFunctor F X).map ((latticeScalarFunctor d π X).map (𝟙 _)) = _
    rw [frameToTotal_comp_totalId, frameToTotal_shiftInt, M.frameToTotal_shiftInt,
      Category.assoc]
    change M.frameToTotal F ≫
      ((rationalPiAut F X d π M.lattice.sheaf hπ ^ k).asIso.hom ≫
        (rationalPiAut F X d π M.lattice.sheaf hπ ^ l).asIso.hom) = M.frameToTotal F
    have hp :
        (rationalPiAut F X d π M.lattice.sheaf hπ ^ k).asIso.hom ≫
          (rationalPiAut F X d π M.lattice.sheaf hπ ^ l).asIso.hom =
        (rationalPiAut F X d π M.lattice.sheaf hπ ^ (k + l)).asIso.hom := by
      rw [add_comm k l, zpow_add]
      rfl
    rw [hp, h, zpow_zero]
    exact Category.comp_id _)

/-- The integer zero comparison is natural in every genuine framed lattice map. -/
def shiftIntZeroNatIso :
    shiftIntFunctor (d := d) (π := π) (X := X) F hπ 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.shiftIntZeroIso F hπ) (fun _f =>
    Hom.ext (LatticePiSheaf.Hom.ext_total
      ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- The integer addition comparison is natural in every genuine framed lattice map. -/
def shiftIntAddNatIso (k l : ℤ) :
    shiftIntFunctor (d := d) (π := π) (X := X) F hπ k ⋙ shiftIntFunctor F hπ l ≅
      shiftIntFunctor F hπ (k + l) :=
  NatIso.ofComponents (fun M => M.shiftIntAddIso F hπ k l) (fun _f =>
    Hom.ext (LatticePiSheaf.Hom.ext_total
      ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Cancellation of integer shifts is a natural framed isomorphism. -/
def shiftIntCancelNatIso (k l : ℤ) (h : k + l = 0) :
    shiftIntFunctor (d := d) (π := π) (X := X) F hπ k ⋙ shiftIntFunctor F hπ l ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.shiftIntCancelIso F hπ k l h) (fun _f =>
    Hom.ext (LatticePiSheaf.Hom.ext_total
      ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Integer framed shift is an actual equivalence with inverse the opposite shift. -/
def shiftIntEquivalence (k : ℤ) :
    FramedLatticePiSheaf d π X F ≌ FramedLatticePiSheaf d π X F where
  functor := shiftIntFunctor F hπ k
  inverse := shiftIntFunctor F hπ (-k)
  unitIso := (shiftIntCancelNatIso F hπ k (-k) (add_neg_cancel k)).symm
  counitIso := shiftIntCancelNatIso F hπ (-k) k (neg_add_cancel k)
  functor_unitIso_comp _ := Hom.ext (LatticePiSheaf.Hom.ext_total (Category.id_comp _))

end FramedLatticePiSheaf

variable {F} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ) (hπ : algebraMap O F π ≠ 0)

/-- The integer zero shift identifies all four actual data by total identity maps. -/
def shiftIntZeroIso : D.shiftInt hπ 0 ≅ D where
  hom := {
    eta := (D.eta.shiftIntZeroIso F hπ).hom
    tangent := D.tangent.graded.shiftIntZeroIso.hom
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  inv := {
    eta := (D.eta.shiftIntZeroIso F hπ).inv
    tangent := D.tangent.graded.shiftIntZeroIso.inv
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  hom_inv_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))
  inv_hom_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))

/-- Successive integer shifts of all four data compare with their summed shift. -/
def shiftIntAddIso (k l : ℤ) : (D.shiftInt hπ k).shiftInt hπ l ≅ D.shiftInt hπ (k + l) where
  hom := {
    eta := (D.eta.shiftIntAddIso F hπ k l).hom
    tangent := (D.tangent.graded.shiftIntAddIso k l).hom
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  inv := {
    eta := (D.eta.shiftIntAddIso F hπ k l).inv
    tangent := (D.tangent.graded.shiftIntAddIso k l).inv
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  hom_inv_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))
  inv_hom_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))

/-- Opposite integer shifts cancel through actual frame- and u-preserving isomorphisms. -/
def shiftIntCancelIso (k l : ℤ) (h : k + l = 0) :
    (D.shiftInt hπ k).shiftInt hπ l ≅ D where
  hom := {
    eta := (D.eta.shiftIntCancelIso F hπ k l h).hom
    tangent := (D.tangent.graded.shiftCancelIso (k : ZMod d) (l : ZMod d)
      (by rw [← Int.cast_add, h, Int.cast_zero])).hom
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  inv := {
    eta := (D.eta.shiftIntCancelIso F hπ k l h).inv
    tangent := (D.tangent.graded.shiftCancelIso (k : ZMod d) (l : ZMod d)
      (by rw [← Int.cast_add, h, Int.cast_zero])).inv
    u := by
      change (latticeScalarFunctor d π (S : TopCat)).map (𝟙 _) ≫ D.u =
        D.u ≫ (structuralOSheafFunctor S φ).map (𝟙 _)
      simp }
  hom_inv_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))
  inv_hom_id := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))

/-- The integer zero comparison is natural for genuine maps of all four data. -/
def shiftIntZeroNatIso :
    shiftIntFunctor (d := d) (π := π) (F := F) (φ := φ) hπ 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun D => D.shiftIntZeroIso hπ) (fun _f =>
    Hom.ext (FramedLatticePiSheaf.Hom.ext (LatticePiSheaf.Hom.ext_total
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
        (GradedPiSheaf.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Integer addition is a natural comparison of four-data shift functors. -/
def shiftIntAddNatIso (k l : ℤ) :
    shiftIntFunctor (d := d) (π := π) (F := F) (φ := φ) hπ k ⋙ shiftIntFunctor hπ l ≅
      shiftIntFunctor hπ (k + l) :=
  NatIso.ofComponents (fun D => D.shiftIntAddIso hπ k l) (fun _f =>
    Hom.ext (FramedLatticePiSheaf.Hom.ext (LatticePiSheaf.Hom.ext_total
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
        (GradedPiSheaf.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Cancellation of opposite integer shifts is natural for all four data. -/
def shiftIntCancelNatIso (k l : ℤ) (h : k + l = 0) :
    shiftIntFunctor (d := d) (π := π) (F := F) (φ := φ) hπ k ⋙ shiftIntFunctor hπ l ≅ 𝟭 _ :=
  NatIso.ofComponents (fun D => D.shiftIntCancelIso hπ k l h) (fun _f =>
    Hom.ext (FramedLatticePiSheaf.Hom.ext (LatticePiSheaf.Hom.ext_total
      ((Category.comp_id _).trans (Category.id_comp _).symm)))
        (GradedPiSheaf.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- Integer shift is an equivalence of actual four-data categories, inverse to shift -k. -/
def shiftIntEquivalence (k : ℤ) : SheafPreDatum d π F φ ≌ SheafPreDatum d π F φ where
  functor := shiftIntFunctor hπ k
  inverse := shiftIntFunctor hπ (-k)
  unitIso := (shiftIntCancelNatIso hπ k (-k) (add_neg_cancel k)).symm
  counitIso := shiftIntCancelNatIso hπ (-k) k (neg_add_cancel k)
  functor_unitIso_comp _ := Hom.ext (FramedLatticePiSheaf.Hom.ext
    (LatticePiSheaf.Hom.ext_total (Category.id_comp _)))
      (GradedPiSheaf.Hom.ext (Category.id_comp _))

namespace IsoClass

variable (q : IsoClass (d := d) (π := π) (F := F) (φ := φ))

/-- The zero integer shift acts identically on genuine preliminary isomorphism classes. -/
@[simp]
theorem shiftInt_zero : shiftInt hπ 0 q = q := by
  refine Quotient.inductionOn q ?_
  intro D
  exact Quotient.sound ⟨D.shiftIntZeroIso hπ⟩

/-- Successive shifts of preliminary classes add their integer parameters. -/
theorem shiftInt_add (k l : ℤ) :
    shiftInt hπ l (shiftInt hπ k q) = shiftInt hπ (k + l) q := by
  refine Quotient.inductionOn q ?_
  intro D
  exact Quotient.sound ⟨D.shiftIntAddIso hπ k l⟩

/-- Every preliminary class shift is bijective, with inverse the opposite integer shift. -/
def shiftIntEquiv (k : ℤ) :
    IsoClass (d := d) (π := π) (F := F) (φ := φ) ≃
      IsoClass (d := d) (π := π) (F := F) (φ := φ) where
  toFun := shiftInt hπ k
  invFun := shiftInt hπ (-k)
  left_inv q := by rw [shiftInt_add, add_neg_cancel, shiftInt_zero]
  right_inv q := by rw [shiftInt_add, neg_add_cancel, shiftInt_zero]

/-- Raw integer shifts give an additive action on preliminary four-data classes. -/
@[instance_reducible]
def shiftIntAddAction :
    AddAction ℤ (IsoClass (d := d) (π := π) (F := F) (φ := φ)) where
  vadd k q := shiftInt hπ k q
  zero_vadd q := shiftInt_zero hπ q
  add_vadd k l q := by
    change shiftInt hπ (k + l) q = shiftInt hπ k (shiftInt hπ l q)
    rw [shiftInt_add, add_comm k l]

end IsoClass

end SheafPreDatum

end Langlands.DeligneFormalSpace
