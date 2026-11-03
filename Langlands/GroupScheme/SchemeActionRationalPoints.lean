import Langlands.GroupScheme.SchemeAction
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Rational points and scheme-theoretic fixedness of scheme actions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S}
    (a : SchemeAction H X)

/-- The actual orbit morphism of a rational section over the base. -/
def orbitMap (x : Over.mk (𝟙 S) ⟶ X) : H.X ⟶ X :=
  a.act (𝟙 H.X) (toUnit H.X ≫ x)

/-- Evaluation of the orbit morphism is the given action on every test scheme. -/
theorem comp_orbitMap (x : Over.mk (𝟙 S) ⟶ X) {T : Over S} (h : T ⟶ H.X) :
    h ≫ a.orbitMap x = a.act h (toUnit T ≫ x) := by
  rw [orbitMap, naturality, Category.comp_id, comp_toUnit_assoc]

/-- All-test fixedness of a rational section is constancy of its orbit morphism. -/
theorem isFixed_iff_orbitMap_eq (x : Over.mk (𝟙 S) ⟶ X) :
    a.IsFixed x ↔ a.orbitMap x = toUnit H.X ≫ x := by
  constructor
  · intro hx
    exact hx H.X (toUnit H.X) (𝟙 H.X)
  · intro hx T b h
    have hb : b = toUnit T := toUnit_unique _ _
    rw [hb, ← a.comp_orbitMap x h, hx, comp_toUnit_assoc]

end SchemeAction

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A nonempty scheme locally of finite type over an algebraically closed field
has a rational section, without a reducedness assumption. -/
theorem nonempty_rationalPoints
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    [Nonempty X.left] :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set X.left).Nonempty) isOpen_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (by simp)⟩

/-- Morphisms from a reduced locally finite type scheme to a separated scheme
over an algebraically closed field are determined by rational points. -/
theorem hom_ext_rationalPoints
    {Z Y : Over (Spec (CommRingCat.of k))}
    [IsReduced Z.left] [LocallyOfFiniteType Z.hom] [IsSeparated Y.hom]
    {f g : Z ⟶ Y}
    (h : ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z, z ≫ f = z ≫ g) :
    f = g := by
  have : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq f.left g.left Y.hom
    (closedPoints Z.left) ?_ ?_ ?_
  · rw [dense_iff_closure_eq]
    exact closure_closedPoints
  · intro z hz
    let p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z :=
      Over.homMk (pointOfClosedPoint Z.hom z hz) (pointOfClosedPoint_comp Z.hom z hz)
    have hp := congrArg (fun q => q.left) (h p)
    change (Spec.map (residueFieldIsoBase Z.hom z hz).hom ≫
        Z.left.fromSpecResidueField z) ≫ f.left =
      (Spec.map (residueFieldIsoBase Z.hom z hz).hom ≫
        Z.left.fromSpecResidueField z) ≫ g.left at hp
    apply (cancel_epi (Spec.map (residueFieldIsoBase Z.hom z hz).hom)).mp
    simpa only [Category.assoc] using hp
  · exact (Over.w f).trans (Over.w g).symm

namespace SchemeAction

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction H X)
    [Smooth H.X.hom] [IsSeparated X.hom]

/-- For a smooth acting group, rational invariance implies fixedness on all
tests and refinements, even when the scheme acted on is nonreduced. -/
theorem isFixed_iff_rationalPoints
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X) :
    a.IsFixed x ↔
      ∀ h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, a.act h x = x := by
  have : IsReduced H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k H.X.left H.X.hom
  constructor
  · intro hx h
    simpa only [Category.id_comp] using hx _ (𝟙 _) h
  · intro hx
    apply (a.isFixed_iff_orbitMap_eq x).2
    apply hom_ext_rationalPoints
    intro h
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    rw [a.comp_orbitMap, hu, Category.id_comp, hx, comp_toUnit_assoc,
      hu, Category.id_comp]

end SchemeAction

end Langlands.GroupScheme
