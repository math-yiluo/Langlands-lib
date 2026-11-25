/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-!
# Functors from a pair category to a fixed category

The constant stage system `CategoryTheory.StageSystem.const I D` on a category `D` has the
identity functors as transition functors and identities as associators. Its pair category maps
to `D` by forgetting the stages (`CategoryTheory.StageSystem.constEval`).

A *coherent cocone* on a stage system `S` with vertex `D`, i.e. functors `Φ_i : C i ⥤ D` with
isomorphisms `T_{j/i} ⋙ Φ_j ≅ Φ_i` compatible with the associators, is the same as a morphism of
stage systems `S ⟶ const I D` (`CategoryTheory.StageSystem.Morphism.ofCocone`); it therefore
induces a functor `S.PairCategory ⥤ D` (`CategoryTheory.StageSystem.descFunctor`), the comparison
functor from the `2`-colimit to the vertex, sending `(i, x)` to `Φ_i x`.

The stage inclusions `j_i : C i ⥤ S.PairCategory` form a cocone of categories
(`CategoryTheory.StageSystem.cocone`) which is a filtered `2`-colimit in the sense of
`CategoryTheory.CategoryCocone.IsFilteredTwoColimit`
(`CategoryTheory.StageSystem.cocone_isFilteredTwoColimit`).
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

namespace StageSystem

variable (I : Type w) [Preorder I] (D : Type u') [Category.{v'} D]

/-- The constant stage system on a category `D`: the transition functors are the identity
functors and the associators are identities. -/
@[simps]
def const : StageSystem (fun _ : I ↦ D) where
  T _ := 𝟭 D
  assoc _ _ := Iso.refl _
  cocycle _ _ _ _ := by simp

variable {I D}

@[simp]
lemma const_tr {i j n p : I} {hi : i ≤ n} {hj : j ≤ n} (h : n ≤ p) {x y : D} (u : x ⟶ y) :
    (const I D).tr (hi := hi) (hj := hj) h u = u := by
  change 𝟙 x ≫ u ≫ 𝟙 y = u
  simp

variable [IsDirectedOrder I]

open PairCategory

/-- The functor from the pair category of the constant stage system on `D` to `D`, forgetting
the stages: a morphism represented by `u` at some stage goes to `u`. -/
noncomputable def constEval : (const I D).PairCategory ⥤ D where
  obj X := X.obj
  map {X Y} f := Quotient.lift (s := Rep.setoid X Y) (fun r ↦ r.u)
    (fun r s ⟨p, hr, hs, e⟩ ↦ by simpa using e) f
  map_id X := rfl
  map_comp {X Y Z} f g := by
    induction f using hom_induction with
    | h n hX hY u =>
    induction g using hom_induction with
    | h n' hY' hZ v =>
    rw [mkHom_comp_mkHom' u v (le_commonStage_left n n') (le_commonStage_right n n')]
    simp [mkHom]

@[simp]
lemma constEval_map_mkHom {X Y : (const I D).PairCategory} {n : I} (hX : X.stage ≤ n)
    (hY : Y.stage ≤ n) (u : X.obj ⟶ Y.obj) :
    constEval.map (mkHom n hX hY u) = u :=
  rfl

variable {C : I → Type u} [∀ i, Category.{v} (C i)] {S : StageSystem C}

/-- A cocone `Φ_i : C i ⥤ D`, `ι_{j/i} : T_{j/i} ⋙ Φ_j ≅ Φ_i`, compatible with the associators,
as a morphism of stage systems to the constant stage system on `D`. -/
@[simps]
def Morphism.ofCocone (Φ : ∀ i, C i ⥤ D) (ι : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ Φ j ≅ Φ i)
    (coh : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (x : C i),
      (Φ k).map ((S.assoc h h').hom.app x) ≫ (ι (h.trans h')).hom.app x =
        (ι h').hom.app ((S.T h).obj x) ≫ (ι h).hom.app x) :
    Morphism S (const I D) where
  Φ := Φ
  β h := (ι h).symm
  coh h h' x := by
    change (ι h).inv.app x ≫ (ι h').inv.app ((S.T h).obj x) ≫
      (Φ _).map ((S.assoc h h').hom.app x) = 𝟙 _ ≫ (ι (h.trans h')).inv.app x
    rw [← cancel_mono ((ι (h.trans h')).hom.app x), Category.assoc, Category.assoc, coh]
    simp

/-- The functor `S.PairCategory ⥤ D` induced by a cocone compatible with the associators,
`(i, x) ↦ Φ_i x`. -/
noncomputable def descFunctor (Φ : ∀ i, C i ⥤ D)
    (ι : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ Φ j ≅ Φ i)
    (coh : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (x : C i),
      (Φ k).map ((S.assoc h h').hom.app x) ≫ (ι (h.trans h')).hom.app x =
        (ι h').hom.app ((S.T h).obj x) ≫ (ι h).hom.app x) :
    S.PairCategory ⥤ D :=
  (Morphism.ofCocone Φ ι coh).functor ⋙ constEval

/-- The functor induced by a coherent cocone restricts on the stage `i` to `Φ_i`. -/
noncomputable def ιCompDescFunctorIso (Φ : ∀ i, C i ⥤ D)
    (ι : ∀ {i j : I} (h : i ≤ j), S.T h ⋙ Φ j ≅ Φ i)
    (coh : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (x : C i),
      (Φ k).map ((S.assoc h h').hom.app x) ≫ (ι (h.trans h')).hom.app x =
        (ι h').hom.app ((S.T h).obj x) ≫ (ι h).hom.app x) (i : I) :
    S.ι i ⋙ descFunctor Φ ι coh ≅ Φ i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    simp only [Functor.comp_map, Iso.refl_hom, Category.comp_id, Category.id_comp, descFunctor]
    rw [Morphism.functor_map_ι]
    rfl)

variable (S) in
/-- The cocone of categories of the stage inclusions `j_i : C i ⥤ S.PairCategory`, with the
identifications `j_j ∘ T_{j/i} ≅ j_i`. -/
noncomputable def cocone : CategoryCocone C S.PairCategory where
  T := S.T
  Φ := S.ι
  iso := S.transIso

variable (S) in
/-- **The pair category is the filtered `2`-colimit** of the stages, in the sense of
`CategoryTheory.CategoryCocone.IsFilteredTwoColimit`: every object and every morphism is
represented at a finite stage, and two representatives agree after a further transition if they
define the same morphism. -/
theorem cocone_isFilteredTwoColimit : S.cocone.IsFilteredTwoColimit where
  essSurjObj X := by
    obtain ⟨i, x, h⟩ := (S.exists_stage_representation).1 X
    exact ⟨i, x, ⟨eqToIso h⟩⟩
  homSurj i j x y f := (S.exists_stage_representation).2.1 x y f
  homInj k x y g g' h := ((S.exists_stage_representation).2.2 g g').1 h

end StageSystem

end CategoryTheory
