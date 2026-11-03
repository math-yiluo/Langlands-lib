import Langlands.GroupScheme.SchemeActionOrbit
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.OrbitMapFlatProof
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Restriction of actions to reduced stable closed subschemes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open TopologicalSpace Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

section AnyBase

variable {S : Scheme.{u}} {G : GroupScheme S} {X : Over S}

/-- A closed subset is invariant if every translation by a base section preserves it. -/
def IsInvariantClosed (a : SchemeAction G X) (Z : Closeds X.left) : Prop :=
  ∀ (g : 𝟙_ (Over S) ⟶ G.X), ∀ z ∈ Z, (a.translation g).left z ∈ Z

end AnyBase

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction G X)

omit [IsAlgClosed k] in
/-- Evaluating a rational action section is evaluation of the corresponding translation. -/
theorem act_closedPoint_eq_translation
    (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X)
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    (a.act g y).left (IsLocalRing.closedPoint k) =
      (a.translation g).left (y.left (IsLocalRing.closedPoint k)) := by
  have h : y ≫ a.translation g = a.act g y := by
    rw [a.comp_translation, toUnit_unit, Category.id_comp]
  rw [← h, Over.comp_left, Scheme.Hom.comp_apply]

/-- A closed subset stable under rational translations carries a reduced closed
subscheme and an action equivariant on every test scheme. -/
theorem exists_reduced_invariantClosedSubscheme
    [Smooth G.X.hom] [LocallyOfFiniteType X.hom]
    (Z : Closeds X.left)
    (hZst : a.IsInvariantClosed Z) :
    ∃ (O : Over (Spec (CommRingCat.of k))) (j : O ⟶ X) (b : SchemeAction G O),
      IsReduced O.left ∧ IsClosedImmersion j.left ∧ Set.range j.left = Z ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (o : T ⟶ O),
        b.act g o ≫ j = a.act g (o ≫ j) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hred : IsReduced I.subscheme :=
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker Z).1
  let O : Over (Spec (CommRingCat.of k)) := Over.mk (I.subschemeι ≫ X.hom)
  let j : O ⟶ X := Over.homMk I.subschemeι rfl
  have : IsReduced O.left := hred
  have : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hjrange : Set.range j.left = Z := by
    change Set.range I.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have : LocallyOfFiniteType O.hom := by
    change LocallyOfFiniteType (I.subschemeι ≫ X.hom)
    infer_instance
  have : IsLocallyNoetherian O.left := LocallyOfFiniteType.isLocallyNoetherian O.hom
  have hjcancel : ∀ {T : Over (Spec (CommRingCat.of k))} (f₁ f₂ : T ⟶ O),
      f₁ ≫ j = f₂ ≫ j → f₁ = f₂ := by
    intro T f₁ f₂ h
    have : Mono j := Over.mono_of_mono_left j
    exact (cancel_mono j).mp h
  have : GeometricallyReduced G.X.hom :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth G.X.hom
  have : IsReduced (G.X ⊗ O).left :=
    inferInstanceAs (IsReduced (Limits.pullback G.X.hom O.hom))
  have : LocallyOfFiniteType (G.X ⊗ O).hom := by
    change LocallyOfFiniteType (Limits.pullback.fst G.X.hom O.hom ≫ G.X.hom)
    infer_instance
  have : JacobsonSpace (G.X ⊗ O).left := LocallyOfFiniteType.jacobsonSpace (G.X ⊗ O).hom
  let m : G.X ⊗ O ⟶ X := (G.X ◁ j) ≫ a.hom
  have hm : Set.range m.left ⊆ Set.range j.left := by
    rw [hjrange]
    have hclosed : IsClosed (m.left ⁻¹' (Z : Set X.left)) := Z.isClosed.preimage m.left.continuous
    have hcl : closedPoints (G.X ⊗ O).left ⊆ m.left ⁻¹' (Z : Set X.left) := by
      intro w hw
      let p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X ⊗ O :=
        Over.homMk (pointOfClosedPoint (G.X ⊗ O).hom w hw) (by simp)
      have hpw : p.left (IsLocalRing.closedPoint k) = w := pointOfClosedPoint_apply _ _ _ _
      have hp : p ≫ m = a.act (p ≫ fst _ _) ((p ≫ snd _ _) ≫ j) := by
        rw [SchemeAction.act]
        simp only [m, ← Category.assoc]
        congr 1
        apply CartesianMonoidalCategory.hom_ext <;> simp
      have h := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hp
      simp only [Over.comp_left, Scheme.Hom.comp_apply, hpw] at h
      change m.left w ∈ (Z : Set X.left)
      rw [h, a.act_closedPoint_eq_translation]
      apply hZst
      change (j.left ((p ≫ snd _ _).left (IsLocalRing.closedPoint k))) ∈
        (Z : Set X.left)
      rw [← hjrange]
      exact ⟨(p ≫ snd _ _).left (IsLocalRing.closedPoint k), by
        simp only [Over.comp_left, Scheme.Hom.comp_apply]⟩
    rintro _ ⟨w, rfl⟩
    have hall := closure_minimal hcl hclosed
    rw [closure_closedPoints] at hall
    exact hall (Set.mem_univ w)
  obtain ⟨l, hl⟩ := FiniteIndexTransfer.exists_lift_of_range_subset j.left m.left hm
  let hom : G.X ⊗ O ⟶ O := Over.homMk l (by
    change l ≫ j.left ≫ X.hom = _
    rw [← Category.assoc, hl]
    exact Over.w m)
  have hhom : hom ≫ j = m := Over.OverMorphism.ext hl
  have hkey : ∀ {T : Over (Spec (CommRingCat.of k))} (f : T ⟶ G.X) (o : T ⟶ O),
      (lift f o ≫ hom) ≫ j = a.act f (o ≫ j) := by
    intro T f o
    rw [Category.assoc, hhom, SchemeAction.act]
    simp only [m, ← Category.assoc, lift_whiskerLeft]
  have hone : ∀ {T : Over (Spec (CommRingCat.of k))} (o : T ⟶ O),
      lift (1 : T ⟶ G.X) o ≫ hom = o := by
    intro T o
    apply hjcancel
    rw [hkey, SchemeAction.act_one]
  have hmul : ∀ {T : Over (Spec (CommRingCat.of k))} (h h' : T ⟶ G.X) (o : T ⟶ O),
      lift (h * h') o ≫ hom = lift h (lift h' o ≫ hom) ≫ hom := by
    intro T h h' o
    apply hjcancel
    rw [hkey, hkey, hkey, SchemeAction.act_mul]
  let b : SchemeAction G O := schemeActionOfPointLaws hom hone hmul
  exact ⟨O, j, b, inferInstance, inferInstance, hjrange, fun _ g o => hkey g o⟩

omit [IsAlgClosed k] in
/-- Rational translations preserve the closure of an actual orbit-map image. -/
theorem translation_mem_closure_orbit
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X)
    {z : X.left} (hz : z ∈ closure (a.orbit x)) :
    (a.translation g).left z ∈ closure (a.orbit x) := by
  have hr : ∀ w ∈ a.orbit x, (a.translation g).left w ∈ a.orbit x := by
    rintro _ ⟨w, rfl⟩
    refine ⟨(FiniteIndexTransfer.leftMul G g).left w, ?_⟩
    have h := congrArg (fun f => f.left w) (OrbitMapFlat.leftMul_comp_orbit a g x)
    simpa only [orbitMap, translation, OrbitMapFlat.actBy,
      Over.comp_left, Scheme.Hom.comp_apply] using h
  exact map_mem_closure (a.translation g).left.continuous hz hr

/-- The closure of each rational orbit is the image of an equivariant reduced
closed subscheme. -/
theorem exists_reduced_orbitClosure
    [Smooth G.X.hom] [LocallyOfFiniteType X.hom]
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    ∃ (O : Over (Spec (CommRingCat.of k))) (j : O ⟶ X) (b : SchemeAction G O),
      IsReduced O.left ∧ IsClosedImmersion j.left ∧
      Set.range j.left = closure (a.orbit x) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (o : T ⟶ O),
        b.act g o ≫ j = a.act g (o ≫ j) := by
  exact a.exists_reduced_invariantClosedSubscheme ⟨closure (a.orbit x), isClosed_closure⟩
    (fun g _ hz => a.translation_mem_closure_orbit x g hz)

end Langlands.GroupScheme.SchemeAction
