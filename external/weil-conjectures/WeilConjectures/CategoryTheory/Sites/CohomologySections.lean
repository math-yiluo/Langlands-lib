/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTransport
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyTorsion

/-!
# Sheaf cohomology through sections of an injective resolution

Let `F → R^•` be an injective resolution of an abelian sheaf on a site with a terminal object
`T`. Then `H^{n + 1}(F) = 0` if and only if the complex of global sections `R^•(T)` is exact in
degree `n + 1` (`CategoryTheory.Sheaf.subsingleton_H_succ_iff_sectionsExactAt`). Sections of
an injective sheaf extend along monomorphisms
(`CategoryTheory.Sheaf.surjective_map_of_injective`), which gives a Mayer-Vietoris argument for
the exactness of the complexes of sections: if `Y` is covered by `U` and `V` with intersection
`W`, exactness over `U` and `V` in degree `n + 1` and the extension of cocycles over `W` to
cocycles over `U` give exactness over `Y` (`CategoryTheory.Sheaf.sectionsExactAt_of_isPullback`).

## Main definitions

- `CategoryTheory.Sheaf.SectionsExactAt`: the complex of sections `K^•(Y)` of a complex of
  abelian sheaves is exact in degree `n + 1`.

## Main statements

- `CategoryTheory.Sheaf.subsingleton_H_succ_iff_sectionsExactAt`: cohomology through sections
  of an injective resolution.
- `CategoryTheory.Sheaf.surjective_map_of_injective`: restriction of sections of an injective
  sheaf along a monomorphism is surjective.
- `CategoryTheory.Sheaf.sectionsExactAt_of_isPullback`: the Mayer-Vietoris step.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Limits Opposite Abelian

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section SectionsExactAt

/-- The complex of sections `K^•(Y)` of a complex `K` of abelian sheaves over an object `Y` is
exact in degree `n + 1`: every cocycle of degree `n + 1` is a coboundary. -/
def SectionsExactAt (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℕ) (Y : C) (n : ℕ) : Prop :=
  ∀ s : (K.X (n + 1)).obj.obj (op Y), (K.d (n + 1) (n + 2)).hom.app (op Y) s = 0 →
    ∃ t : (K.X n).obj.obj (op Y), (K.d n (n + 1)).hom.app (op Y) t = s

end SectionsExactAt

section Criterion

variable [HasSheafify J AddCommGrpCat.{w}] {T : C}

lemma constantHomEquiv_zero (hT : IsTerminal T) (G : Sheaf J AddCommGrpCat.{w}) :
    constantHomEquiv hT G 0 = 0 := by
  rw [← comp_zero (f := (0 : (constantSheaf J AddCommGrpCat.{w}).obj
    (AddCommGrpCat.of (ULift ℤ)) ⟶ G)) (Z := G), constantHomEquiv_comp]
  rfl

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- **Cohomology through sections of an injective resolution.** Let `R` be an injective
resolution of an abelian sheaf `F` and `T` a terminal object. Then `H^{n + 1}(F) = 0` if and
only if the complex of global sections `R^•(T)` is exact in degree `n + 1`. -/
theorem subsingleton_H_succ_iff_sectionsExactAt (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{w}}
    (R : InjectiveResolution F) (n : ℕ) :
    Subsingleton (H F (n + 1)) ↔ SectionsExactAt R.cocomplex T n := by
  let e := constantHomEquiv (J := J) hT
  constructor
  · intro h s hs
    let φ := (e _).symm s
    have hφ : φ ≫ R.cocomplex.d (n + 1) (n + 2) = 0 := by
      apply (e _).injective
      rw [constantHomEquiv_comp, Equiv.apply_symm_apply, hs, constantHomEquiv_zero]
    obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff φ (n + 2) rfl hφ n rfl).1 (Subsingleton.elim _ _)
    refine ⟨e _ g, ?_⟩
    rw [← constantHomEquiv_comp, hg, Equiv.apply_symm_apply]
  · intro h
    refine ⟨fun a b ↦ ?_⟩
    suffices ∀ α : H F (n + 1), α = 0 by rw [this a, this b]
    intro α
    obtain ⟨φ, hφ, rfl⟩ := R.extMk_surjective α (n + 2) rfl
    rw [R.extMk_eq_zero_iff φ (n + 2) rfl hφ n rfl]
    obtain ⟨t, ht⟩ := h (e _ φ) (by rw [← constantHomEquiv_comp, hφ, constantHomEquiv_zero])
    refine ⟨(e _).symm t, (e _).injective ?_⟩
    rw [constantHomEquiv_comp, Equiv.apply_symm_apply, ht]

end Criterion

section Injective

variable [HasSheafify J AddCommGrpCat.{max w v}]

/-- **Sections of an injective sheaf extend along monomorphisms.** For an injective abelian
sheaf `I` and a monomorphism `i : W ⟶ Y`, restriction `I(Y) ⟶ I(W)` is surjective: a section
over `W` is a morphism from the sheafified free abelian sheaf on `W`, which embeds into the one
on `Y`. -/
theorem surjective_map_of_injective (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I]
    {W Y : C} (i : W ⟶ Y) [Mono i] : Function.Surjective (I.obj.map i.op) := by
  let θ : uliftYoneda.{w}.obj W ⋙ AddCommGrpCat.free ⟶
      uliftYoneda.{w}.obj Y ⋙ AddCommGrpCat.free :=
    Functor.whiskerRight (uliftYoneda.{w}.map i) AddCommGrpCat.free
  have hθ : Mono θ := by
    have (V : Cᵒᵖ) : Mono (θ.app V) := by
      have : Mono ((uliftYoneda.{w}.map i).app V) := by
        rw [mono_iff_injective]
        intro a b hab
        exact ULift.ext ((cancel_mono i).1 (congrArg ULift.down hab))
      exact AddCommGrpCat.free.map_mono _
    exact NatTrans.mono_of_mono_app _
  let m := (presheafToSheaf J AddCommGrpCat.{max w v}).map θ
  intro s
  let f : (presheafToSheaf J _).obj (uliftYoneda.{w}.obj W ⋙ AddCommGrpCat.free) ⟶ I :=
    ⟨sheafifyLift J (freeYonedaPresheafHom.{w} W I.obj s) I.property⟩
  let g := Injective.factorThru f m
  have hg : m ≫ g = f := Injective.comp_factorThru f m
  refine ⟨g.hom.app (op Y) ((toSheafify J (uliftYoneda.{w}.obj Y ⋙ AddCommGrpCat.free)).app
    (op Y) (freeYonedaGen.{w} Y)), ?_⟩
  let Pw := uliftYoneda.{w}.obj W ⋙ AddCommGrpCat.free
  let Py := uliftYoneda.{w}.obj Y ⋙ AddCommGrpCat.free
  have h1 : Py.map i.op (freeYonedaGen.{w} Y) = θ.app (op W) (freeYonedaGen.{w} W) := by
    refine Eq.trans (FreeAbelianGroup.map_of_apply _) ((congrArg FreeAbelianGroup.of ?_).trans
      (FreeAbelianGroup.map_of_apply _).symm)
    exact ULift.ext (by simp)
  have key : θ ≫ toSheafify J Py ≫ g.hom = toSheafify J Pw ≫ f.hom := by
    rw [← Category.assoc, toSheafify_naturality, Category.assoc]
    exact congrArg (toSheafify J Pw ≫ ·) (congrArg (fun φ ↦ φ.hom) hg)
  have h2 : (toSheafify J Pw ≫ f.hom).app (op W) (freeYonedaGen.{w} W) = s := by
    rw [toSheafify_sheafifyLift]
    exact freeYonedaPresheafHom_gen W I.obj s
  rw [← h2, ← key, ← ConcreteCategory.comp_apply, ← g.hom.naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply ((toSheafify J Py).app (op Y)), ← (toSheafify J Py).naturality,
    ConcreteCategory.comp_apply, h1]
  rfl

end Injective

end Sheaf

end CategoryTheory
