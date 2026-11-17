import Langlands.GroupScheme.LocalGroupIsoRefinement
import Langlands.GroupScheme.LocalGroupIsoBaseChangeEquivalence
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Local group isomorphism families over scheme coproducts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

namespace LocalGroupHom

variable {S : Scheme.{u}} {G H : GroupScheme S} {J : Type u}
    (V : J → Over S) (e : ∀ i, LocalGroupHom G H (V i))

private theorem coproductValues_compatible {T : Over S}
    (a : T ⟶ sigmaOver V) (g : T ⟶ G.X) :
    Presieve.Arrows.Compatible (yoneda.obj H.X)
      (fun i => pullback.fst a (sigmaOverι V i))
      (fun i => (e i).toFun (pullback.snd a (sigmaOverι V i))
        (pullback.fst a (sigmaOverι V i) ≫ g)) := by
  intro i j W f h hfh
  change f ≫ (e i).toFun _ _ = h ≫ (e j).toFun _ _
  rw [← (e i).naturality, ← (e j).naturality]
  have hc : (f ≫ pullback.snd a (sigmaOverι V i)) ≫ sigmaOverι V i =
      (h ≫ pullback.snd a (sigmaOverι V j)) ≫ sigmaOverι V j := by
    calc
      _ = (f ≫ pullback.fst a (sigmaOverι V i)) ≫ a := by
        rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      _ = (h ≫ pullback.fst a (sigmaOverι V j)) ≫ a :=
        congrArg (fun k => k ≫ a) hfh
      _ = _ := by rw [Category.assoc, pullback.condition, ← Category.assoc]
  by_cases hij : i = j
  · subst j
    let : Mono (sigmaOverι V i) := Over.mono_of_mono_left _
    have hx := (cancel_mono (sigmaOverι V i)).mp hc
    rw [hx, ← Category.assoc, hfh, Category.assoc]
  · let : IsEmpty W.left := _root_.AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
      (g := fun i => (V i).left)
      (show CommSq (f ≫ pullback.snd a (sigmaOverι V i)).left
        (h ≫ pullback.snd a (sigmaOverι V j)).left
        (Sigma.ι (fun i => (V i).left) i) (Sigma.ι (fun i => (V i).left) j) from
          ⟨congrArg (fun k => k.left) hc⟩) hij
    exact Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)

private theorem existsUnique_coproductValue {T : Over S}
    (a : T ⟶ sigmaOver V) (g : T ⟶ G.X) :
    ∃! h : T ⟶ H.X, ∀ i,
      pullback.fst a (sigmaOverι V i) ≫ h =
        (e i).toFun (pullback.snd a (sigmaOverι V i))
          (pullback.fst a (sigmaOverι V i) ≫ g) := by
  have hs : Presieve.IsSheafFor (yoneda.obj H.X)
      (Presieve.ofArrows (fun i => pullback a (sigmaOverι V i))
        (fun i => pullback.fst a (sigmaOverι V i))) := by
    rw [Presieve.isSheafFor_iff_generate]
    apply (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.zariskiTopology.over S) (yoneda.obj H.X))
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (pullbackOpenCover V a).mem_grothendieckTopology
  exact (Presieve.isSheafFor_arrows_iff _ _).mp hs _
    (coproductValues_compatible V e a g)

/-- Glue the values of the component homomorphism families on a coproduct point. -/
def coproductValue {T : Over S} (a : T ⟶ sigmaOver V) (g : T ⟶ G.X) : T ⟶ H.X :=
  (existsUnique_coproductValue V e a g).choose

theorem coproductValue_fac {T : Over S} (a : T ⟶ sigmaOver V)
    (g : T ⟶ G.X) (i : J) :
    pullback.fst a (sigmaOverι V i) ≫ coproductValue V e a g =
      (e i).toFun (pullback.snd a (sigmaOverι V i))
        (pullback.fst a (sigmaOverι V i) ≫ g) :=
  (existsUnique_coproductValue V e a g).choose_spec.1 i

/-- Evaluation on a component commutes with every relative test refinement. -/
theorem comp_coproductValue {T W : Over S} (a : T ⟶ sigmaOver V)
    (g : T ⟶ G.X) (i : J) (t : W ⟶ T) (b : W ⟶ V i)
    (ht : t ≫ a = b ≫ sigmaOverι V i) :
    t ≫ coproductValue V e a g = (e i).toFun b (t ≫ g) := by
  have h := congrArg (fun k => pullback.lift t b ht ≫ k)
    (coproductValue_fac V e a g i)
  simpa only [← Category.assoc, pullback.lift_fst, ← (e i).naturality,
    pullback.lift_snd] using h

/-- Morphisms from a coproduct point's test are determined on all component pullbacks. -/
theorem coproduct_hom_ext {T Y : Over S} (a : T ⟶ sigmaOver V) {f h : T ⟶ Y}
    (hfh : ∀ i, pullback.fst a (sigmaOverι V i) ≫ f =
      pullback.fst a (sigmaOverι V i) ≫ h) : f = h := by
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (pullbackOpenCover V a) f.left h.left
  intro i
  exact congrArg (fun k => k.left) (hfh i)

/-- Gluing of component homomorphism values is natural on every test scheme. -/
theorem coproductValue_naturality {T W : Over S} (t : W ⟶ T)
    (a : T ⟶ sigmaOver V) (g : T ⟶ G.X) :
    coproductValue V e (t ≫ a) (t ≫ g) = t ≫ coproductValue V e a g := by
  apply coproduct_hom_ext V (t ≫ a)
  intro i
  rw [coproductValue_fac, ← Category.assoc]
  exact (comp_coproductValue V e a g i
    (pullback.fst (t ≫ a) (sigmaOverι V i) ≫ t)
    (pullback.snd (t ≫ a) (sigmaOverι V i))
    (by rw [Category.assoc, pullback.condition])).symm

/-- The glued component values preserve the group law. -/
def coproductPointsHom {T : Over S} (a : T ⟶ sigmaOver V) :
    (T ⟶ G.X) →* (T ⟶ H.X) where
  toFun := coproductValue V e a
  map_one' := by
    apply coproduct_hom_ext V a
    intro i
    rw [coproductValue_fac, MonObj.comp_one, map_one, MonObj.comp_one]
  map_mul' g h := by
    apply coproduct_hom_ext V a
    intro i
    rw [coproductValue_fac, MonObj.comp_mul, map_mul, MonObj.comp_mul,
      coproductValue_fac, coproductValue_fac]

/-- Natural local group homomorphisms glue over an arbitrary scheme coproduct. -/
def coproduct : LocalGroupHom G H (sigmaOver V) where
  toFun a := coproductPointsHom V e a
  naturality := coproductValue_naturality V e

end LocalGroupHom

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {J : Type u}
    (V : J → Over S) (e : ∀ i, LocalGroupIso G H (V i))

/-- Natural local group isomorphisms glue over an arbitrary scheme coproduct.
The construction uses only the component families and no isomorphism representer. -/
def coproduct : LocalGroupIso G H (sigmaOver V) where
  toFun a :=
    { toFun := LocalGroupHom.coproductValue V (fun i => (e i).toLocalGroupHom) a
      invFun := LocalGroupHom.coproductValue V (fun i => (e i).symm.toLocalGroupHom) a
      left_inv g := by
        apply LocalGroupHom.coproduct_hom_ext V a
        intro i
        rw [LocalGroupHom.coproductValue_fac]
        change (e i).symm.toFun _ (_ ≫
          LocalGroupHom.coproductValue V (fun i => (e i).toLocalGroupHom) a g) = _
        rw [LocalGroupHom.coproductValue_fac]
        exact (e i).toFun _ |>.symm_apply_apply _
      right_inv h := by
        apply LocalGroupHom.coproduct_hom_ext V a
        intro i
        rw [LocalGroupHom.coproductValue_fac]
        change (e i).toFun _ (_ ≫
          LocalGroupHom.coproductValue V (fun i => (e i).symm.toLocalGroupHom) a h) = _
        rw [LocalGroupHom.coproductValue_fac]
        exact (e i).toFun _ |>.apply_symm_apply _
      map_mul' := (LocalGroupHom.coproductPointsHom V
        (fun i => (e i).toLocalGroupHom) a).map_mul }
  naturality := LocalGroupHom.coproductValue_naturality V
    (fun i => (e i).toLocalGroupHom)

/-- Evaluation on a component of the glued family holds on all relative tests. -/
theorem coproduct_toFun_comp {T W : Over S} (a : T ⟶ sigmaOver V)
    (g : T ⟶ G.X) (i : J) (t : W ⟶ T) (b : W ⟶ V i)
    (ht : t ≫ a = b ≫ sigmaOverι V i) :
    t ≫ (coproduct V e).toFun a g = (e i).toFun b (t ≫ g) :=
  LocalGroupHom.comp_coproductValue V (fun i => (e i).toLocalGroupHom)
    a g i t b ht

@[simp]
theorem coproduct_toFun_ι {T : Over S} (i : J) (a : T ⟶ V i) (g : T ⟶ G.X) :
    (coproduct V e).toFun (a ≫ sigmaOverι V i) g = (e i).toFun a g := by
  simpa only [Category.id_comp] using
    coproduct_toFun_comp V e (a ≫ sigmaOverι V i) g i (𝟙 T) a (Category.id_comp _)

/-- Refining the coproduct family by an inclusion recovers the prescribed family. -/
@[simp]
theorem coproduct_refine_ι (i : J) :
    (coproduct V e).refine (sigmaOverι V i) = e i := by
  apply ext_toFun
  intro T a g
  exact coproduct_toFun_ι V e i a g

/-- The component restrictions uniquely determine a family on the coproduct. -/
theorem coproduct_unique (E : LocalGroupIso G H (sigmaOver V))
    (hE : ∀ i, E.refine (sigmaOverι V i) = e i) : E = coproduct V e := by
  apply ext_toFun
  intro T a g
  apply LocalGroupHom.coproduct_hom_ext V a
  intro i
  rw [← E.naturality]
  have hi := congrArg (fun F : LocalGroupIso G H (V i) =>
    F.toFun (pullback.snd a (sigmaOverι V i))
      (pullback.fst a (sigmaOverι V i) ≫ g)) (hE i)
  change E.toFun (pullback.snd a (sigmaOverι V i) ≫ sigmaOverι V i) _ = _ at hi
  rw [pullback.condition]
  exact hi.trans (coproduct_toFun_comp V e a g i
    (pullback.fst a (sigmaOverι V i)) (pullback.snd a (sigmaOverι V i))
    pullback.condition).symm

end LocalGroupIso

end Langlands.GroupScheme
