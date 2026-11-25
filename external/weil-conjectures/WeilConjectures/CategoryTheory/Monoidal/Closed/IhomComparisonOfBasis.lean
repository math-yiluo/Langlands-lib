/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs along adjunctions with a scalar basis

Let `L : C ⥤ D` be a strong monoidal additive functor between preadditive monoidal closed
categories, with an additive right adjoint `G : D ⥤ C` reflecting isomorphisms. Suppose given a
finite family `σ : ι → (𝟭 D ⟶ 𝟭 D)` of "scalars", compatible with the tensor product
(`(σ i).app (P ⊗ Z) = P ◁ (σ i).app Z`), such that the maps `K ⟶ G (L K)` given by the unit
followed by the scalars form a basis, i.e. `biproduct.desc (fun i ↦ η_K ≫ G (σ i))` is an
isomorphism `⨁_ι K ≅ G (L K)`. Then the comparison maps `L [A, B] ⟶ [L A, L B]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) are isomorphisms
(`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_biproductDesc`).

Informally, `G L ≅ (-)^{⊕ι}`, so that `G L [A, B] ≅ [A, B]^{⊕ι} ≅ [A, G L B] ≅ G [L A, L B]`.
The proof is a Yoneda argument.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory MonoidalClosed Limits

/-- If `biproduct.desc θ : ⨁_ι K ⟶ M` is an isomorphism, then every morphism `X ⟶ M` can be
written uniquely as `∑ i, f i ≫ θ i` with `f i : X ⟶ K`. -/
lemma Limits.bijective_sum_comp_of_isIso_biproductDesc {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteBiproducts C] {ι : Type} [Fintype ι] {K M : C} (θ : ι → (K ⟶ M))
    [IsIso (biproduct.desc θ)] (X : C) :
    Function.Bijective (fun f : ι → (X ⟶ K) ↦ ∑ i, f i ≫ θ i) := by
  have hlift : Function.Bijective (fun f : ι → (X ⟶ K) ↦ biproduct.lift f) := by
    refine ⟨fun f g h ↦ funext fun i ↦ ?_, fun g ↦ ⟨fun i ↦ g ≫ biproduct.π _ i, ?_⟩⟩
    · simpa using congrArg (· ≫ biproduct.π _ i) h
    · exact biproduct.hom_ext _ _ fun i ↦ by simp
  have hcomp : Function.Bijective (fun g : X ⟶ ⨁ fun _ : ι ↦ K ↦ g ≫ biproduct.desc θ) :=
    (isIso_iff_yoneda_map_bijective _).1 inferInstance X
  convert hcomp.comp hlift using 1
  funext f
  exact (biproduct.lift_desc (f := fun _ : ι ↦ K)).symm

namespace MonoidalClosed

variable {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D]

/-- A natural endomorphism `σ` of the identity which is compatible with the tensor product,
`σ (P ⊗ Z) = P ◁ σ Z`, commutes with uncurrying. -/
lemma uncurry_comp_app_of_app_tensor (σ : 𝟭 D ⟶ 𝟭 D)
    (hσ : ∀ P Z : D, σ.app (P ⊗ Z) = P ◁ σ.app Z) {P Q X : D} (k : X ⟶ (ihom P).obj Q) :
    uncurry (k ≫ σ.app ((ihom P).obj Q)) = uncurry k ≫ σ.app Q := by
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc, ← hσ, Category.assoc]
  exact congrArg (P ◁ k ≫ ·) (σ.naturality ((ihom.ev P).app Q)).symm

end MonoidalClosed

namespace Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D]

/-- One summand of the Yoneda computation behind
`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_biproductDesc`: transposing
`f ≫ η ≫ G (σ ≫ w)` (with `w` the comparison map of `L`) along `L ⊣ G` and the tensor-hom
adjunctions gives `uncurry f ≫ η ≫ G σ`. -/
lemma homEquiv_δ_uncurry_homEquiv_symm (L : C ⥤ D) [L.Monoidal] {G : D ⥤ C} (adj : L ⊣ G)
    (σ : 𝟭 D ⟶ 𝟭 D) (hσ : ∀ P Z : D, σ.app (P ⊗ Z) = P ◁ σ.app Z) {A B X : C}
    (f : X ⟶ (ihom A).obj B) :
    adj.homEquiv _ _ (OplaxMonoidal.δ L A X ≫ uncurry ((adj.homEquiv _ _).symm
      ((f ≫ adj.unit.app _ ≫ G.map (σ.app (L.obj _))) ≫
        G.map ((ihomComparison L A).app B)))) =
      uncurry f ≫ adj.unit.app B ≫ G.map (σ.app (L.obj B)) := by
  have hnat := σ.naturality ((ihomComparison L A).app B)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj] at hnat
  rw [Category.assoc, Category.assoc, ← G.map_comp, ← hnat, ← adj.homEquiv_unit,
    ← adj.homEquiv_naturality_left, Equiv.symm_apply_apply, uncurry_natural_left,
    uncurry_comp_app_of_app_tensor σ hσ, uncurry_eq, Category.assoc, ihomComparison_ev_assoc,
    μ_natural_right_assoc, Monoidal.δ_μ_assoc, ← L.map_comp_assoc, ← uncurry_eq,
    adj.homEquiv_naturality_left, adj.homEquiv_unit]

/-- Let `L : C ⥤ D` be a strong monoidal additive functor between preadditive monoidal closed
categories with a right adjoint `G` reflecting isomorphisms, and let `σ : ι → (𝟭 D ⟶ 𝟭 D)` be a
finite family of scalars compatible with the tensor product such that the maps
`η_K ≫ G (σ i) : K ⟶ G (L K)` form a basis, i.e. `⨁_ι K ⟶ G (L K)` is an isomorphism. Then the
comparison maps `L [A, B] ⟶ [L A, L B]` are isomorphisms. -/
theorem isIso_ihomComparison_of_isIso_biproductDesc [Preadditive C] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts C] (L : C ⥤ D) [L.Monoidal] [L.Additive]
    {G : D ⥤ C} [G.ReflectsIsomorphisms] (adj : L ⊣ G) {ι : Type} [Finite ι]
    (σ : ι → (𝟭 D ⟶ 𝟭 D)) (hσ : ∀ (i : ι) (P Z : D), (σ i).app (P ⊗ Z) = P ◁ (σ i).app Z)
    (hθ : ∀ K : C,
      IsIso (biproduct.desc fun i : ι ↦ adj.unit.app K ≫ G.map ((σ i).app (L.obj K))))
    (A : C) : IsIso (ihomComparison L A) := by
  have := Fintype.ofFinite ι
  rw [NatTrans.isIso_iff_isIso_app]
  intro B
  rw [← isIso_iff_of_reflects_iso _ G, isIso_iff_yoneda_map_bijective]
  intro X
  let e : (X ⟶ G.obj ((ihom (L.obj A)).obj (L.obj B))) →+ (A ⊗ X ⟶ G.obj (L.obj B)) :=
    (adj.homAddEquiv _ _).toAddMonoidHom.comp ((Preadditive.leftComp _
      (OplaxMonoidal.δ L A X)).comp ((curryAddEquiv _ _ _).symm.toAddMonoidHom.comp
        (adj.homAddEquiv _ _).symm.toAddMonoidHom))
  have he : Function.Injective e := fun a b hab ↦ (adj.homEquiv _ _).symm.injective
    (uncurry_injective ((cancel_epi (OplaxMonoidal.δ L A X)).1
      ((adj.homEquiv _ _).injective hab)))
  have := hθ ((ihom A).obj B)
  have := hθ B
  have hα : Function.Bijective (fun f : ι → (X ⟶ (ihom A).obj B) ↦
      (∑ i, f i ≫ adj.unit.app _ ≫ G.map ((σ i).app (L.obj ((ihom A).obj B))) :
        X ⟶ G.obj (L.obj ((ihom A).obj B)))) :=
    bijective_sum_comp_of_isIso_biproductDesc _ X
  have hβ : Function.Bijective (fun f : ι → (A ⊗ X ⟶ B) ↦
      (∑ i, f i ≫ adj.unit.app B ≫ G.map ((σ i).app (L.obj B)) :
        A ⊗ X ⟶ G.obj (L.obj B))) :=
    bijective_sum_comp_of_isIso_biproductDesc _ (A ⊗ X)
  have hu : Function.Bijective (fun (f : ι → (X ⟶ (ihom A).obj B)) (i : ι) ↦ uncurry (f i)) :=
    ⟨fun f g hfg ↦ funext fun i ↦ uncurry_injective (congrFun hfg i),
      fun g ↦ ⟨fun i ↦ curry (g i), funext fun i ↦ uncurry_curry (g i)⟩⟩
  have hcomp : Function.Bijective ((e ∘ fun g ↦ g ≫ G.map ((ihomComparison L A).app B)) ∘
      fun f : ι → (X ⟶ (ihom A).obj B) ↦ (∑ i, f i ≫ adj.unit.app ((ihom A).obj B) ≫
        G.map ((σ i).app (L.obj ((ihom A).obj B))) : X ⟶ G.obj (L.obj ((ihom A).obj B)))) := by
    convert hβ.comp hu using 1
    funext f
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Preadditive.sum_comp,
      _root_.map_sum]
    exact Finset.sum_congr rfl fun i _ ↦
      homEquiv_δ_uncurry_homEquiv_symm L adj (σ i) (hσ i) (f i)
  rw [Function.Bijective.of_comp_iff _ hα] at hcomp
  refine ⟨hcomp.1.of_comp, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hcomp.2 (e y)
  exact ⟨x, he hx⟩

end Functor.LaxMonoidal

end CategoryTheory
