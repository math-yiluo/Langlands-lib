/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomTensorSectionNaturality

/-!
# Pure-tensor evaluation of currying naturality

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-curry-natural-pure)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency true in
private theorem projection_map (L L' M M' : CochainComplex Mod ℤ)
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q) :
    ((((homComplexFunctor (R := R)).map f.op).app M) ≫
      ((homComplexFunctor (R := R)).obj (op L')).map g).f n ≫
        homTensorProjection R L' M' n p q hpq =
      homTensorProjection R L M n p q hpq ≫
        SheafOfModules.homObjMap (R := R) (f.f p) (g.f q) := by
  exact (Classical.choose_spec
    (homComplex_projections_exists (R := R))).2.2 L L' M M' f g n p q hpq

private theorem hom_map_apply {A A' B B' : Mod} (f : A' ⟶ A) (g : B ⟶ B')
    (U : Cᵒᵖ) (s : (SheafOfModules.homObj (R := R) A B).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A'.val.obj (op W.unop.left)) :
    ((((SheafOfModules.homObjMap f g).val.app U).hom s).app W).hom x =
      (g.val.app (op W.unop.left)).hom
        ((s.app W).hom ((f.val.app (op W.unop.left)).hom x)) := by
  rfl

private theorem projection_map_apply (L L' M M' : CochainComplex Mod ℤ)
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q)
    (U : Cᵒᵖ) (s : (homComplex (R := R) L M).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (L'.X p).val.obj (op W.unop.left)) :
    let δ := (((homComplexFunctor (R := R)).map f.op).app M) ≫
      ((homComplexFunctor (R := R)).obj (op L')).map g
    ((((homTensorProjection R L' M' n p q hpq).val.app U).hom
      (((δ.f n).val.app U).hom s)).app W).hom x =
    ((g.f q).val.app (op W.unop.left)).hom
      (((((homTensorProjection R L M n p q hpq).val.app U).hom s).app W).hom
        (((f.f p).val.app (op W.unop.left)).hom x)) := by
  have he := congrArg
    (fun t : (homComplex (R := R) L M).X n ⟶
        SheafOfModules.homObj (R := R) (L'.X p) (M'.X q) ↦
      (((t.val.app U).hom s).app W).hom x)
    (projection_map R L L' M M' f g n p q hpq)
  exact he.trans (hom_map_apply R (f.f p) (g.f q) U
    (((homTensorProjection R L M n p q hpq).val.app U).hom s) W x)

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem total_tensor_pure (K K' L L' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (i j : ℤ) (V : Cᵒᵖ)
    (x : (K'.X i).val.obj V) (y : (L'.X j).val.obj V) :
    letI := SheafOfModules.monoidalCategory R
    (((HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).f
      (i + j)).val.app V).hom
      (((CochainComplex.ιMapBifunctor K' L' (curriedTensor Mod) i j (i + j) rfl).val.app
        V).hom (((homTensorSectionMap R (K'.X i) (L'.X j)).app V).hom
          (x ⊗ₜ[R.obj.obj V] y))) =
    ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod) i j (i + j) rfl).val.app
      V).hom (((homTensorSectionMap R (K.X i) (L.X j)).app V).hom
        ((((f.f i).val.app V).hom x) ⊗ₜ[R.obj.obj V] (((g.f j).val.app V).hom y))) := by
  let := SheafOfModules.monoidalCategory R
  have ht := HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)
    i j (i + j) rfl
  have hs := homTensorSectionMap_natural R (f.f i) (g.f j)
  have he := congrArg (fun t : (K'.X i ⊗ L'.X j) ⟶
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)).X (i + j) ↦
    (t.val.app V).hom
    (((homTensorSectionMap R (K'.X i) (L'.X j)).app V).hom
      (x ⊗ₜ[R.obj.obj V] y))) ht
  have he' := congrArg (fun t ↦ (t.app V).hom (x ⊗ₜ[R.obj.obj V] y)) hs
  change ((f.f i ⊗ₘ g.f j).val.app V).hom
    (((homTensorSectionMap R (K'.X i) (L'.X j)).app V).hom
      (x ⊗ₜ[R.obj.obj V] y)) = _ at he'
  change _ = ((homTensorSectionMap R (K.X i) (L.X j)).app V).hom
    ((((f.f i).val ⊗ₘ (g.f j).val).app V).hom (x ⊗ₜ[R.obj.obj V] y)) at he'
  erw [PresheafOfModules.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul] at he'
  change _ = ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
    i j (i + j) rfl).val.app V).hom
      (((f.f i ⊗ₘ g.f j).val.app V).hom
        (((homTensorSectionMap R (K'.X i) (L'.X j)).app V).hom
          (x ⊗ₜ[R.obj.obj V] y))) at he
  exact he.trans (congrArg _ he')

-- Localized Hom terms require extra elaboration of the two nested projection formulas.
set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
/-- Naturality of the pure-tensor equation for two degreewise currying maps.
Source: Stacks Project, Cohomology on Sites, Tag 0A90, functoriality,
referring to More on Algebra, Lemma 15.73.1.
(blueprint: lem-sc-hom-tensor-curry-natural-pure)

Proof: Apply the currying condition for the primed complexes to the image of s
under the iterated Hom map. The componentwise action specified by
homComplex_exists first evaluates the outer map at f^i(x), then the inner map
at g^j(y), and postcomposes the result with h^(i+j+n). Thus the left side is
h^(i+j+n)(phi_i(f^i(x))_j(g^j(y))). For the right side use the same Hom-complex
projection formula. Precomposition by the total tensor map restricts to the
termwise tensor map on the (i,j) summand by ι_mapBifunctorMap. Naturality of
the sheafification unit, its tensorator and the tensor comparison sends the
image of x tensor y to the image of f^i(x) tensor g^j(y). Apply the unprimed
currying condition to obtain the same value. This is an equality on one pure
tensor; no coproduct, sheafification or internal-Hom extensionality is used. -/
theorem homTensorCurry_natural_pure
    (K K' L L' M M' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a : (homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
        (homComplex (R := R)
          (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n)
      (a' : (homComplex (R := R) K' (homComplex (R := R) L' M')).X n ⟶
        (homComplex (R := R)
          (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M').X n),
    HomTensorCurryCondition R K L M n a →
    HomTensorCurryCondition R K' L' M' n a' →
    ∀ (U : Cᵒᵖ)
      (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
      (W : (Over U.unop)ᵒᵖ) (i j : ℤ)
      (x : (K'.X i).val.obj (op W.unop.left))
      (y : (L'.X j).val.obj (op W.unop.left)),
      let α := (((homComplexFunctor (R := R)).map f.op).app
          (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op K')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h)
      let β := (((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
        ((homComplexFunctor (R := R)).obj
          (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h
      let z := ((CochainComplex.ιMapBifunctor K' L' (curriedTensor Mod)
          i j (i + j) rfl).val.app (op W.unop.left)).hom
        (((homTensorSectionMap R (K'.X i) (L'.X j)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))
      (((((α.f n ≫ a') ≫ homTensorProjection R
          (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M'
            n (i + j) (i + j + n) rfl).val.app U).hom s).app W).hom z =
        (((((a ≫ β.f n) ≫ homTensorProjection R
          (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M'
            n (i + j) (i + j + n) rfl).val.app U).hom s).app W).hom z := by
  let := SheafOfModules.monoidalCategory R
  intro a a' ha ha' U s W i j x y
  let γ := (((homComplexFunctor (R := R)).map g.op).app M) ≫
    ((homComplexFunctor (R := R)).obj (op L')).map h
  let α := (((homComplexFunctor (R := R)).map f.op).app
    (homComplex (R := R) L M)) ≫
      ((homComplexFunctor (R := R)).obj (op K')).map γ
  have hc := ha' i j U ((α.f n).val.app U |>.hom s) W x y
  have ho := projection_map_apply R K K' (homComplex (R := R) L M)
    (homComplex (R := R) L' M') f γ n i (i + n) rfl U s W x
  let w := (((((homTensorProjection R K (homComplex (R := R) L M)
      n i (i + n) rfl).val.app U).hom s).app W).hom
        (((f.f i).val.app (op W.unop.left)).hom x))
  have hi := projection_map_apply R L L' M M' g h (i + n) j (i + j + n)
    (by omega) (op W.unop.left) w (op (Over.mk (𝟙 W.unop.left))) y
  have hx := congrArg
    (fun t : (homComplex (R := R) L' M').X (i + n) |>.val.obj (op W.unop.left) ↦
      (((((homTensorProjection R L' M' (i + n) j (i + j + n)
        (by omega)).val.app (op W.unop.left)).hom t).app
          (op (Over.mk (𝟙 W.unop.left)))).hom y)) ho
  have hl := hc.trans (hx.trans hi)
  let z := ((CochainComplex.ιMapBifunctor K' L' (curriedTensor Mod)
      i j (i + j) rfl).val.app (op W.unop.left)).hom
    (((homTensorSectionMap R (K'.X i) (L'.X j)).app (op W.unop.left)).hom
      (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))
  have hb := projection_map_apply R
    (CochainComplex.mapBifunctor K L (curriedTensor Mod))
    (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M M'
    (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)) h
    n (i + j) (i + j + n) rfl U ((a.val.app U).hom s) W z
  dsimp only [z] at hb
  have ht := total_tensor_pure R K K' L L' f g i j (op W.unop.left) x y
  have hbt := congrArg
    (fun t : (CochainComplex.mapBifunctor K L (curriedTensor Mod)).X (i + j)
        |>.val.obj (op W.unop.left) ↦
      ((h.f (i + j + n)).val.app (op W.unop.left)).hom
        (((((homTensorProjection R
          (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M
          n (i + j) (i + j + n) rfl).val.app U).hom
            ((a.val.app U).hom s)).app W).hom t)) ht
  have hu := ha i j U s W
    (((f.f i).val.app (op W.unop.left)).hom x)
    (((g.f j).val.app (op W.unop.left)).hom y)
  have hv := congrArg ((h.f (i + j + n)).val.app (op W.unop.left)).hom hu
  exact hl.trans (hb.trans (hbt.trans hv)).symm

end CategoryTheory
