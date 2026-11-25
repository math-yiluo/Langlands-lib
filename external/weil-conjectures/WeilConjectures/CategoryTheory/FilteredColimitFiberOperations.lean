/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredColimitHomCategory
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Identity and composition on filtered arrow fibers -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem arrow_comp_congr {C : Type z} [Category.{z} C]
    {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff f f').mp hf
  obtain ⟨_, hZ, hg⟩ := (Arrow.mk_eq_mk_iff g g').mp hg
  subst hX
  subst hY
  subst hZ
  simpa using congrArg Arrow.mk (congrArg₂ (fun f g ↦ f ≫ g) hf hg)

private theorem eventually_equal₂
    {J : Type z} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type z)
    {j k : J} (x y : G.obj j) (x' y' : G.obj k)
    (hx : colimit.ι G j x = colimit.ι G k x')
    (hy : colimit.ι G j y = colimit.ι G k y') :
    ∃ (l : J) (u : j ⟶ l) (v : k ⟶ l),
      G.map u x = G.map v x' ∧ G.map u y = G.map v y' := by
  obtain ⟨l, u, v, hu⟩ := (Types.FilteredColimit.colimit_eq_iff G).mp hx
  have hy' : colimit.ι G l (G.map u y) = colimit.ι G l (G.map v y') := by
    simpa using hy
  obtain ⟨m, w, hw⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit G) _ _).mp hy'
  refine ⟨m, u ≫ w, v ≫ w, ?_, ?_⟩
  · simpa using congrArg (fun a ↦ G.map w a) hu
  · simpa using hw

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph,
and Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-fiber-operations).

Proof: Represent an object in the object colimit by a stage object and send its
identity to the arrow colimit. Represent two composable fiber elements by stage
arrows. Move the representatives to a common stage. Their middle endpoints agree
in the object colimit, so the filtered-colimit equality criterion makes them equal
at a further stage. Transport along this equality and compose at that stage.
Independence of all choices follows by moving two choices to a common stage and
using eventual equality for their arrows and endpoints; transition functors preserve
identities and composition. The resulting arrow has the required endpoints, so lies
in the required fiber. The formulas for stage identities and composites follow by
choosing the stage itself for the representatives. Empty stage categories give no
objects requiring identities; otherwise each object has a representative. -/
theorem filteredColimit_fiber_operations
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∃ (i : ∀ X : O, FilteredColimitHom F X X)
      (c : ∀ {X Y Z : O}, FilteredColimitHom F X Y →
        FilteredColimitHom F Y Z → FilteredColimitHom F X Z),
      (∀ (j : J) (X : F.obj j),
        i (colimit.ι (F ⋙ Cat.objects) j X) = filteredColimitHomι F j (𝟙 X)) ∧
      (∀ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
        c (filteredColimitHomι F j f) (filteredColimitHomι F j g) =
          filteredColimitHomι F j (f ≫ g)) := by
  classical
  let A := colimit (F ⋙ Cat.arrows)
  let O := colimit (F ⋙ Cat.objects)
  let ic : Cocone (F ⋙ Cat.objects) :=
    { pt := A
      ι :=
        { app := fun j ↦ TypeCat.ofHom (fun (X : F.obj j) ↦
            colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (𝟙 X)))
          naturality := by
            intro j k u
            ext X
            change F.obj j at X
            change colimit.ι (F ⋙ Cat.arrows) k
              (Arrow.mk (𝟙 ((F.map u).toFunctor.obj X))) =
                colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (𝟙 X))
            have hw := ConcreteCategory.congr_hom
              (colimit.w (F ⋙ Cat.arrows) u) (Arrow.mk (𝟙 X))
            change colimit.ι (F ⋙ Cat.arrows) k
              (Arrow.mk ((F.map u).toFunctor.map (𝟙 X))) =
                colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (𝟙 X)) at hw
            simpa only [Functor.map_id] using hw } }
  let I : O → A := colimit.desc (F ⋙ Cat.objects) ic
  have hI (j : J) (X : F.obj j) :
      I (colimit.ι (F ⋙ Cat.objects) j X) =
        colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (𝟙 X)) := by
    exact ConcreteCategory.congr_hom (colimit.ι_desc ic j) X
  have hIs (X : O) : filteredColimitArrowSource F (I X) = X := by
    obtain ⟨j, X, rfl⟩ := Types.jointly_surjective' X
    rw [hI]
    exact filteredColimitArrowSource_ι F j _
  have hIt (X : O) : filteredColimitArrowTarget F (I X) = X := by
    obtain ⟨j, X, rfl⟩ := Types.jointly_surjective' X
    rw [hI]
    exact filteredColimitArrowTarget_ι F j _
  let i : ∀ X : O, FilteredColimitHom F X X := fun X ↦ ⟨I X, hIs X, hIt X⟩
  have hi (j : J) (X : F.obj j) :
      i (colimit.ι (F ⋙ Cat.objects) j X) = filteredColimitHomι F j (𝟙 X) := by
    apply Subtype.ext
    exact hI j X
  -- A composable pair admits composable representatives at one stage.
  have hrep (a b : A)
      (hab : filteredColimitArrowTarget F a = filteredColimitArrowSource F b) :
      ∃ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
        colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk f) = a ∧
          colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk g) = b := by
    obtain ⟨j, x, y, hx, hy⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂
        (colimit.isColimit (F ⋙ Cat.arrows)) a b
    change colimit.ι (F ⋙ Cat.arrows) j x = a at hx
    change colimit.ι (F ⋙ Cat.arrows) j y = b at hy
    have hmid : colimit.ι (F ⋙ Cat.objects) j x.right =
        colimit.ι (F ⋙ Cat.objects) j y.left := by
      rw [← filteredColimitArrowTarget_ι F j x,
        ← filteredColimitArrowSource_ι F j y, hx, hy]
      exact hab
    obtain ⟨k, u, hu⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
        (colimit.isColimit (F ⋙ Cat.objects)) x.right y.left).mp hmid
    change (F.map u).toFunctor.obj x.right = (F.map u).toFunctor.obj y.left at hu
    refine ⟨k, (F.map u).toFunctor.obj x.left, (F.map u).toFunctor.obj x.right,
      (F.map u).toFunctor.obj y.right, (F.map u).toFunctor.map x.hom,
      eqToHom hu ≫ (F.map u).toFunctor.map y.hom, ?_, ?_⟩
    · exact (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) u) x).trans hx
    · rw [Arrow.arrow_mk_eqToHom_comp]
      exact (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) u) y).trans hy
  -- The composite does not depend on these representatives.
  have hcomp_eq (j k : J) (X Y Z : F.obj j) (X' Y' Z' : F.obj k)
      (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
      (hf : colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk f) =
        colimit.ι (F ⋙ Cat.arrows) k (Arrow.mk f'))
      (hg : colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk g) =
        colimit.ι (F ⋙ Cat.arrows) k (Arrow.mk g')) :
      colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (f ≫ g)) =
        colimit.ι (F ⋙ Cat.arrows) k (Arrow.mk (f' ≫ g')) := by
    obtain ⟨l, u, v, hu, hv⟩ := eventually_equal₂ (F ⋙ Cat.arrows)
      (Arrow.mk f) (Arrow.mk g) (Arrow.mk f') (Arrow.mk g') hf hg
    change Arrow.mk ((F.map u).toFunctor.map f) =
      Arrow.mk ((F.map v).toFunctor.map f') at hu
    change Arrow.mk ((F.map u).toFunctor.map g) =
      Arrow.mk ((F.map v).toFunctor.map g') at hv
    calc
      _ = colimit.ι (F ⋙ Cat.arrows) l
          (Arrow.mk ((F.map u).toFunctor.map (f ≫ g))) :=
        (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) u)
          (Arrow.mk (f ≫ g))).symm
      _ = colimit.ι (F ⋙ Cat.arrows) l
          (Arrow.mk ((F.map v).toFunctor.map (f' ≫ g'))) := by
        rw [Functor.map_comp, Functor.map_comp]
        exact congrArg (fun a ↦ colimit.ι (F ⋙ Cat.arrows) l a)
          (arrow_comp_congr _ _ _ _ hu hv)
      _ = _ := ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) v)
        (Arrow.mk (f' ≫ g'))
  let R (a b d : A) : Prop :=
    ∃ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
      colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk f) = a ∧
        colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk g) = b ∧
          colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (f ≫ g)) = d
  have hR (a b : A)
      (hab : filteredColimitArrowTarget F a = filteredColimitArrowSource F b) :
      ∃! d, R a b d := by
    obtain ⟨j, X, Y, Z, f, g, hf, hg⟩ := hrep a b hab
    refine ⟨colimit.ι (F ⋙ Cat.arrows) j (Arrow.mk (f ≫ g)),
      ⟨j, X, Y, Z, f, g, hf, hg, rfl⟩, ?_⟩
    rintro d ⟨k, X', Y', Z', f', g', hf', hg', hd⟩
    rw [← hd]
    exact hcomp_eq k j X' Y' Z' X Y Z f' g' f g
      (hf'.trans hf.symm) (hg'.trans hg.symm)
  let C (a b : A)
      (hab : filteredColimitArrowTarget F a = filteredColimitArrowSource F b) : A :=
    (hR a b hab).choose
  have hC (a b : A)
      (hab : filteredColimitArrowTarget F a = filteredColimitArrowSource F b) :
      R a b (C a b hab) := (hR a b hab).choose_spec.1
  have hCs (a b : A) (hab : filteredColimitArrowTarget F a =
      filteredColimitArrowSource F b) :
      filteredColimitArrowSource F (C a b hab) = filteredColimitArrowSource F a := by
    obtain ⟨j, X, Y, Z, f, g, hf, _, hd⟩ := hC a b hab
    rw [← hd, ← hf, filteredColimitArrowSource_ι, filteredColimitArrowSource_ι]
    rfl
  have hCt (a b : A) (hab : filteredColimitArrowTarget F a =
      filteredColimitArrowSource F b) :
      filteredColimitArrowTarget F (C a b hab) = filteredColimitArrowTarget F b := by
    obtain ⟨j, X, Y, Z, f, g, _, hg, hd⟩ := hC a b hab
    rw [← hd, ← hg, filteredColimitArrowTarget_ι, filteredColimitArrowTarget_ι]
    rfl
  let c : ∀ {X Y Z : O}, FilteredColimitHom F X Y →
      FilteredColimitHom F Y Z → FilteredColimitHom F X Z := fun {X Y Z} f g ↦
    ⟨C f.val g.val (f.property.2.trans g.property.1.symm),
      (hCs _ _ (f.property.2.trans g.property.1.symm)).trans f.property.1,
      (hCt _ _ (f.property.2.trans g.property.1.symm)).trans g.property.2⟩
  refine ⟨i, @c, hi, ?_⟩
  intro j X Y Z f g
  apply Subtype.ext
  exact ((hR _ _ ((filteredColimitHomι F j f).property.2.trans
    (filteredColimitHomι F j g).property.1.symm)).choose_spec.2 _
    ⟨j, X, Y, Z, f, g, rfl, rfl, rfl⟩).symm

end CategoryTheory
