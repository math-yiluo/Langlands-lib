/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Exactness of the explicitly defined derived square boundary

Source: Mathlib, ShortComplex.ShortExact.homology_exact₁/₂/₃; Stacks, Cohomology, 01EB.
(blueprint: lem-sc-injectively-exact-square-boundary-exact).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory.InjectivelyExactSquare

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

private def pairFst (A B : C ⥤ AddCommGrpCat.{w}) : pairFunctor A B ⟶ A where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  naturality := by intros; rfl

private def pairSnd (A B : C ⥤ AddCommGrpCat.{w}) : pairFunctor A B ⟶ B where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  naturality := by intros; rfl

private def pairInl (A B : C ⥤ AddCommGrpCat.{w}) : A ⟶ pairFunctor A B where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.inl _ _)
  naturality := by intros; ext x; simp [pairFunctor]

private def pairInr (A B : C ⥤ AddCommGrpCat.{w}) : B ⟶ pairFunctor A B where
  app _ := AddCommGrpCat.ofHom (AddMonoidHom.inr _ _)
  naturality := by intros; ext x; simp [pairFunctor]

private noncomputable def hmap {A B : C ⥤ AddCommGrpCat.{w}} [A.Additive] [B.Additive]
    (α : A ⟶ B) (F : C) (n : ℕ) :=
  HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex) n

private lemma hmap_comp {A B D : C ⥤ AddCommGrpCat.{w}}
    [A.Additive] [B.Additive] [D.Additive] (α : A ⟶ B) (β : B ⟶ D) (F : C) (n : ℕ) :
    hmap (α ≫ β) F n = hmap α F n ≫ hmap β F n := by
  simp [hmap, NatTrans.mapHomologicalComplex_comp, HomologicalComplex.homologyMap_comp]

private lemma hmap_id (A : C ⥤ AddCommGrpCat.{w}) [A.Additive] (F : C) (n : ℕ) :
    hmap (𝟙 A) F n = 𝟙 _ := by simp [hmap]

private lemma hmap_add {A B : C ⥤ AddCommGrpCat.{w}} [A.Additive] [B.Additive]
    (α β : A ⟶ B) (F : C) (n : ℕ) :
    hmap (α + β) F n = hmap α F n + hmap β F n := by
  have h : (NatTrans.mapHomologicalComplex (α + β) (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (injectiveResolution F).cocomplex +
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app
        (injectiveResolution F).cocomplex := by ext; rfl
  simp only [hmap, h, HomologicalComplex.homologyMap_add]

private lemma hmap_zero (A B : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive]
    (F : C) (n : ℕ) : hmap (0 : A ⟶ B) F n = 0 := by
  have h : (NatTrans.mapHomologicalComplex (0 : A ⟶ B) (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex = 0 := by ext; rfl
  simp [hmap, h]

private noncomputable def splitIso {P A B : AddCommGrpCat.{w}}
    (p : P ⟶ A) (q : P ⟶ B) (i : A ⟶ P) (j : B ⟶ P)
    (h : p ≫ i + q ≫ j = 𝟙 P) (h₁ : i ≫ p = 𝟙 A) (h₂ : j ≫ p = 0)
    (h₃ : i ≫ q = 0) (h₄ : j ≫ q = 𝟙 B) : P ≅ AddCommGrpCat.of (A × B) where
  hom := AddCommGrpCat.ofHom (p.hom.prod q.hom)
  inv := AddCommGrpCat.ofHom
    (i.hom.comp (AddMonoidHom.fst _ _) + j.hom.comp (AddMonoidHom.snd _ _))
  hom_inv_id := by
    ext x
    exact congrArg (fun f ↦ f x) h
  inv_hom_id := by
    ext x : 2
    apply Prod.ext
    · change p (i x.1 + j x.2) = x.1
      simp [map_add, ← ConcreteCategory.comp_apply, h₁, h₂]
    · change q (i x.1 + j x.2) = x.2
      simp [map_add, ← ConcreteCategory.comp_apply, h₃, h₄]

private noncomputable def pairHomologyIso (A B : C ⥤ AddCommGrpCat.{w})
    [A.Additive] [B.Additive] (F : C) (n : ℕ) :
    (((pairFunctor A B).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution F).cocomplex).homology n ≅
    AddCommGrpCat.of
      ((((A.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution F).cocomplex).homology n) ×
        (((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution F).cocomplex).homology n)) :=
  splitIso (hmap (pairFst A B) F n) (hmap (pairSnd A B) F n)
    (hmap (pairInl A B) F n) (hmap (pairInr A B) F n)
    (by
      have h : pairFst A B ≫ pairInl A B + pairSnd A B ≫ pairInr A B = 𝟙 _ := by
        ext I x
        change (x.1, 0) + (0, x.2) = x
        exact Prod.ext (add_zero _) (zero_add _)
      simpa only [hmap_add, hmap_comp, hmap_id] using
        congrArg (fun α ↦ hmap α F n) h)
    (by
      have h : pairInl A B ≫ pairFst A B = 𝟙 _ := by ext; rfl
      simpa only [hmap_comp, hmap_id] using congrArg (fun α ↦ hmap α F n) h)
    (by
      have h : pairInr A B ≫ pairFst A B = 0 := by ext; rfl
      simpa only [hmap_comp, hmap_zero] using congrArg (fun α ↦ hmap α F n) h)
    (by
      have h : pairInl A B ≫ pairSnd A B = 0 := by ext; rfl
      simpa only [hmap_comp, hmap_zero] using congrArg (fun α ↦ hmap α F n) h)
    (by
      have h : pairInr A B ≫ pairSnd A B = 𝟙 _ := by ext; rfl
      simpa only [hmap_comp, hmap_id] using congrArg (fun α ↦ hmap α F n) h)

private lemma hmap_sub {A B : C ⥤ AddCommGrpCat.{w}} [A.Additive] [B.Additive]
    (α β : A ⟶ B) (F : C) (n : ℕ) :
    hmap (α - β) F n = hmap α F n - hmap β F n := by
  have h : (NatTrans.mapHomologicalComplex (α - β) (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex =
      (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (injectiveResolution F).cocomplex -
      (NatTrans.mapHomologicalComplex β (ComplexShape.up ℕ)).app
        (injectiveResolution F).cocomplex := by ext; rfl
  simp only [hmap, h, HomologicalComplex.homologyMap_sub]

private noncomputable def productIso {A B A' B' : AddCommGrpCat.{w}}
    (e : A ≅ A') (f : B ≅ B') :
    AddCommGrpCat.of (A × B) ≅ AddCommGrpCat.of (A' × B') :=
  (AddEquiv.prodCongr (Iso.addCommGroupIsoToAddEquiv e)
    (Iso.addCommGroupIsoToAddEquiv f)).toAddCommGrpIso

private noncomputable def middleIso (S : InjectivelyExactSquare.{u, v, w} C)
    (F : C) (n : ℕ) : (S.resolutionSequence F).X₂.homology n ≅
    AddCommGrpCat.of ((S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F) :=
  pairHomologyIso S.X₂ S.X₃ F n ≪≫ productIso
    ((injectiveResolution F).isoRightDerivedObj S.X₂ n).symm
    ((injectiveResolution F).isoRightDerivedObj S.X₃ n).symm

private lemma hmap_comparison {A B : C ⥤ AddCommGrpCat.{w}}
    [A.Additive] [B.Additive] (α : A ⟶ B) (F : C) (n : ℕ) :
    hmap α F n ≫ ((injectiveResolution F).isoRightDerivedObj B n).inv =
    ((injectiveResolution F).isoRightDerivedObj A n).inv ≫
      (NatTrans.rightDerived α n).app F := by
  rw [InjectiveResolution.rightDerived_app_eq α (injectiveResolution F)]
  simp [hmap, HomologicalComplex.homologyFunctor_map]

private noncomputable def derivedDiagonal (S : InjectivelyExactSquare.{u, v, w} C)
    (F : C) (n : ℕ) : (S.X₁.rightDerived n).obj F ⟶
    AddCommGrpCat.of ((S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F) :=
  AddCommGrpCat.ofHom (((NatTrans.rightDerived S.f₁₂ n).app F).hom.prod
    ((NatTrans.rightDerived S.f₁₃ n).app F).hom)

private noncomputable def derivedDifference (S : InjectivelyExactSquare.{u, v, w} C)
    (F : C) (n : ℕ) :
    AddCommGrpCat.of ((S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F) ⟶
      (S.X₄.rightDerived n).obj F :=
  AddCommGrpCat.ofHom
    ((((NatTrans.rightDerived S.f₂₄ n).app F).hom.comp (AddMonoidHom.fst _ _)) -
      (((NatTrans.rightDerived S.f₃₄ n).app F).hom.comp (AddMonoidHom.snd _ _)))

private lemma diagonal_comparison (S : InjectivelyExactSquare.{u, v, w} C)
    (F : C) (n : ℕ) :
    hmap S.diagonal F n ≫ (middleIso S F n).hom =
      ((injectiveResolution F).isoRightDerivedObj S.X₁ n).inv ≫
        derivedDiagonal S F n := by
  have h₁ : S.diagonal ≫ pairFst S.X₂ S.X₃ = S.f₁₂ := by ext; rfl
  have h₂ : S.diagonal ≫ pairSnd S.X₂ S.X₃ = S.f₁₃ := by ext; rfl
  have hh₁ := congrArg (fun α ↦ hmap α F n) h₁
  have hh₂ := congrArg (fun α ↦ hmap α F n) h₂
  simp only [hmap_comp] at hh₁ hh₂
  ext x : 2
  apply Prod.ext
  · change ((hmap S.diagonal F n ≫ hmap (pairFst S.X₂ S.X₃) F n ≫
        ((injectiveResolution F).isoRightDerivedObj S.X₂ n).inv) x) = _
    rw [← Category.assoc, hh₁, hmap_comparison]
    rfl
  · change ((hmap S.diagonal F n ≫ hmap (pairSnd S.X₂ S.X₃) F n ≫
        ((injectiveResolution F).isoRightDerivedObj S.X₃ n).inv) x) = _
    rw [← Category.assoc, hh₂, hmap_comparison]
    rfl

private lemma difference_comparison (S : InjectivelyExactSquare.{u, v, w} C)
    (F : C) (n : ℕ) :
    (middleIso S F n).hom ≫ derivedDifference S F n =
      hmap S.difference F n ≫
        ((injectiveResolution F).isoRightDerivedObj S.X₄ n).inv := by
  have h : S.difference = pairFst S.X₂ S.X₃ ≫ S.f₂₄ -
      pairSnd S.X₂ S.X₃ ≫ S.f₃₄ := by ext; rfl
  rw [h, hmap_sub, hmap_comp, hmap_comp, Preadditive.sub_comp]
  rw [Category.assoc, Category.assoc, hmap_comparison, hmap_comparison]
  ext x
  rfl

private lemma transport_exact (K : ShortComplex AddCommGrpCat.{w}) (hK : K.Exact)
    {A B D : AddCommGrpCat.{w}} (e₁ : K.X₁ ≅ A) (e₂ : K.X₂ ≅ B) (e₃ : K.X₃ ≅ D)
    (f : A ⟶ B) (g : B ⟶ D)
    (hf : e₁.hom ≫ f = K.f ≫ e₂.hom)
    (hg : e₂.hom ≫ g = K.g ≫ e₃.hom) : Function.Exact f g := by
  have hz : f ≫ g = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, hf, Category.assoc, hg,
      ← Category.assoc, K.zero, Limits.zero_comp, Limits.comp_zero]
  let L := ShortComplex.mk f g hz
  exact (ShortComplex.ab_exact_iff_function_exact L).mp
    (ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ hf hg) hK)

private lemma injectiveTransport {A A' B B' : AddCommGrpCat.{w}}
    (f : A ⟶ B) (g : A' ⟶ B') (e : A ≅ A') (e' : B ≅ B')
    (h : f ≫ e'.hom = e.hom ≫ g) (hi : Function.Injective f) :
    Function.Injective g := by
  have he := (ConcreteCategory.bijective_of_isIso e.inv).1
  have he' := (ConcreteCategory.bijective_of_isIso e'.hom).1
  intro x y hxy
  apply he
  apply hi
  apply he'
  have hx := congrArg (fun f ↦ f (e.inv x)) h
  have hy := congrArg (fun f ↦ f (e.inv y)) h
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hx hy
  exact hx.trans (hxy.trans hy.symm)

/-- The explicit transported complex connecting map gives the three exactness positions
and the initial injection for the derived sequence of the square.

Source: Mathlib, Algebra/Homology/HomologySequence.lean,
`ShortComplex.ShortExact.homology_exact₁/₂/₃`, and CategoryTheory/Abelian/RightDerived.lean,
`InjectiveResolution.isoRightDerivedObj`, following Stacks Cohomology Lemma 01EB.
(blueprint: lem-sc-injectively-exact-square-boundary-exact).

Proof: The `resolutionSequence` is already proved short exact. Apply Mathlib's
homology_exact₂ at n, homology_exact₃ at n,n+1, and homology_exact₁ at n,n+1. The four
injective-resolution comparison isomorphisms identify the outer homologies with the
right derived functor values. For the middle product complex, cycles are pairs of cycles
and boundaries are pairs of boundaries. The two projections therefore induce an
isomorphism from its degree-n homology to the product of the two degree-n homologies,
with inverse induced by the two inclusions and addition. These constructions are inverse
because the two coordinate projections of their composites are identities. Through this
comparison the map from the first complex is the pair of the derived f₁₂ and f₁₃, and the
map to the last complex is the difference of the derived f₂₄ and f₃₄, by additivity of
homology and `NatTrans.rightDerived_app_eq`. The connecting map after transport is exactly
`boundary` by its definition. Transport of the three exact pairs along these isomorphisms
gives the displayed Function.Exact assertions (using ShortComplex.ab_exact_iff_function_exact).
Finally, in degree zero, the natural-number-indexed complexes have no incoming boundaries.
Homology is the kernel of the outgoing differential. The termwise injective diagonal
therefore restricts to an injective map on these kernels. Transport and the product
comparison give the first assertion. No left-exactness assumption on the functors is used. -/
theorem boundary_exact (S : InjectivelyExactSquare.{u, v, w} C) :
    (∀ (F : C),
        Function.Injective (fun x : (S.X₁.rightDerived 0).obj F ↦
          ((NatTrans.rightDerived S.f₁₂ 0).app F x,
            (NatTrans.rightDerived S.f₁₃ 0).app F x))) ∧
    (∀ (F : C) (n : ℕ),
        Function.Exact
          (fun x : (S.X₁.rightDerived n).obj F ↦
            ((NatTrans.rightDerived S.f₁₂ n).app F x,
              (NatTrans.rightDerived S.f₁₃ n).app F x))
          (fun x : (S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F ↦
            (NatTrans.rightDerived S.f₂₄ n).app F x.1 -
              (NatTrans.rightDerived S.f₃₄ n).app F x.2) ∧
        Function.Exact
          (fun x : (S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F ↦
            (NatTrans.rightDerived S.f₂₄ n).app F x.1 -
              (NatTrans.rightDerived S.f₃₄ n).app F x.2)
          (S.boundary F n) ∧
        Function.Exact (S.boundary F n)
          (fun x : (S.X₁.rightDerived (n + 1)).obj F ↦
            ((NatTrans.rightDerived S.f₁₂ (n + 1)).app F x,
              (NatTrans.rightDerived S.f₁₃ (n + 1)).app F x))) := by
  constructor
  · intro F
    have hS := S.resolutionSequence_shortExact F
    have : Mono (S.resolutionSequence F).f := hS.mono_f
    have : Mono ((S.resolutionSequence F).f.f 0) := inferInstance
    have hm : Mono (hmap S.diagonal F 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
        (S.resolutionSequence F).f 0 (by intro i; simp [ComplexShape.up_Rel])
    have hi := (AddCommGrpCat.mono_iff_injective (hmap S.diagonal F 0)).mp hm
    exact injectiveTransport (hmap S.diagonal F 0) (derivedDiagonal S F 0)
      ((injectiveResolution F).isoRightDerivedObj S.X₁ 0).symm (middleIso S F 0)
      (diagonal_comparison S F 0) hi
  · intro F n
    have hS := S.resolutionSequence_shortExact F
    let e₁ := ((injectiveResolution F).isoRightDerivedObj S.X₁ n).symm
    let e₂ := middleIso S F n
    let e₃ := ((injectiveResolution F).isoRightDerivedObj S.X₄ n).symm
    let e₄ := ((injectiveResolution F).isoRightDerivedObj S.X₁ (n + 1)).symm
    let e₅ := middleIso S F (n + 1)
    have hb : e₃.hom ≫ S.boundary F n = hS.δ n (n + 1) rfl ≫ e₄.hom := by
      simp [e₃, e₄, boundary]
    refine ⟨?_, ?_, ?_⟩
    · exact transport_exact _ (hS.homology_exact₂ n) e₁ e₂ e₃
        (derivedDiagonal S F n) (derivedDifference S F n)
        (diagonal_comparison S F n).symm (difference_comparison S F n)
    · exact transport_exact _ (hS.homology_exact₃ n (n + 1) rfl) e₂ e₃ e₄
        (derivedDifference S F n) (S.boundary F n)
        (difference_comparison S F n) hb
    · exact transport_exact _ (hS.homology_exact₁ n (n + 1) rfl) e₃ e₄ e₅
        (S.boundary F n) (derivedDiagonal S F (n + 1)) hb
        (diagonal_comparison S F (n + 1)).symm

end CategoryTheory.InjectivelyExactSquare
