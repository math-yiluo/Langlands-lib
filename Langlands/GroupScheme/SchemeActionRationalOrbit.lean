import Langlands.GroupScheme.SchemeActionRationalPoints
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Rational points in actual scheme-action orbits -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A rational point in the underlying image of a locally finite type morphism
over an algebraically closed field has an actual rational lift. -/
theorem exists_rationalPoint_lift_of_mem_range
    {k : Type u} [Field k] [IsAlgClosed k]
    {Z Y : Scheme.{u}} (f : Z ⟶ Y) [LocallyOfFiniteType f]
    (y : Spec (CommRingCat.of k) ⟶ Y)
    (hy : y (IsLocalRing.closedPoint k) ∈ Set.range f) :
    ∃ z : Spec (CommRingCat.of k) ⟶ Z, z ≫ f = y := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨w, _⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := y)
      z (IsLocalRing.closedPoint k) hz
  let P : Over (Spec (CommRingCat.of k)) := Over.mk (pullback.snd f y)
  have : Nonempty P.left := ⟨w⟩
  have : LocallyOfFiniteType P.hom := by
    dsimp [P]
    infer_instance
  obtain ⟨p⟩ := nonempty_rationalPoints P
  refine ⟨p.left ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact (congrArg (fun q => q ≫ y) (Over.w p)).trans (Category.id_comp y)

namespace SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}
variable (a : SchemeAction H X)

/-- The orbit of a section under the actual group of sections over the base. -/
def rationalOrbit (x : 𝟙_ (Over S) ⟶ X) : Set (𝟙_ (Over S) ⟶ X) :=
  Set.range (fun h : 𝟙_ (Over S) ⟶ H.X => a.act h x)

/-- An orbit containing an all-test fixed section is the singleton orbit. -/
theorem isFixed_of_fixed_mem_rationalOrbit
    {x y : 𝟙_ (Over S) ⟶ X} (hy : a.IsFixed y)
    (hxy : y ∈ a.rationalOrbit x) : a.IsFixed x := by
  obtain ⟨h, hh⟩ := hxy
  have he := congrArg (a.act h⁻¹) hh
  rw [← a.act_mul, inv_mul_cancel, a.act_one] at he
  have hf : a.act h⁻¹ y = y := by
    simpa only [Category.id_comp] using hy _ (𝟙 _) h⁻¹
  have h : x = y := he.trans hf
  rw [h]
  exact hy

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))}
  (a : SchemeAction H X) [LocallyOfFiniteType H.X.hom]

/-- A rational section is in the rational orbit exactly when its underlying
point is in the image of the actual orbit morphism. -/
theorem mem_rationalOrbit_iff
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    y ∈ a.rationalOrbit x ↔
      y.left (IsLocalRing.closedPoint k) ∈ Set.range (a.orbitMap x).left := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h.left (IsLocalRing.closedPoint k), ?_⟩
    have he := a.comp_orbitMap x h
    have hu : toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    rw [hu, Category.id_comp] at he
    have e := congrArg (fun q => q.left (IsLocalRing.closedPoint k)) he
    change (h.left ≫ (a.orbitMap x).left) (IsLocalRing.closedPoint k) =
      (a.act h x).left (IsLocalRing.closedPoint k) at e
    exact (Scheme.Hom.comp_apply h.left (a.orbitMap x).left
      (IsLocalRing.closedPoint k)).symm.trans e
  · intro hy
    have : LocallyOfFiniteType ((a.orbitMap x).left ≫ X.hom) := by
      rw [Over.w]
      infer_instance
    have : LocallyOfFiniteType (a.orbitMap x).left :=
      locallyOfFiniteType_of_comp (a.orbitMap x).left X.hom
    obtain ⟨h, hh⟩ :=
      exists_rationalPoint_lift_of_mem_range (a.orbitMap x).left y.left hy
    have hs : h ≫ H.X.hom = 𝟙 _ := by
      rw [← Over.w (a.orbitMap x), ← Category.assoc, hh]
      exact Over.w y
    let h' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X := Over.homMk h hs
    refine ⟨h', ?_⟩
    have he : h' ≫ a.orbitMap x = y := Over.OverMorphism.ext hh
    rw [a.comp_orbitMap] at he
    have hu : toUnit (𝟙_ (Over (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    simpa only [hu, Category.id_comp] using he

/-- If a fixed rational point lies in the actual orbit image, the original
rational point is fixed over every test scheme. -/
theorem isFixed_of_fixed_mem_orbitImage
    {x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X}
    (hy : a.IsFixed y)
    (hxy : y.left (IsLocalRing.closedPoint k) ∈ Set.range (a.orbitMap x).left) :
    a.IsFixed x :=
  a.isFixed_of_fixed_mem_rationalOrbit hy ((a.mem_rationalOrbit_iff x y).2 hxy)

/-- A closed orbit whose closure contains a fixed rational point is fixed. -/
theorem isFixed_of_closed_orbitImage
    {x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X}
    (hy : a.IsFixed y) (hc : IsClosed (Set.range (a.orbitMap x).left))
    (hxy : y.left (IsLocalRing.closedPoint k) ∈
      closure (Set.range (a.orbitMap x).left)) : a.IsFixed x := by
  rw [hc.closure_eq] at hxy
  exact a.isFixed_of_fixed_mem_orbitImage hy hxy

end SchemeAction

end Langlands.GroupScheme
