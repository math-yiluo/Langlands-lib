/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Derived sequence for three functors exact on injectives

Source: Stacks Project, Tags 0A50 and 0117.
(blueprint: lem-weil-pbc-right-derived-injective-sequence)
-/

@[expose] public section

universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

section
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  (A B E : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] [E.Additive]
  (a : A ⟶ B) (c : B ⟶ E)
  (hexact : ∀ (I : C), Injective I → Function.Exact (a.app I) (c.app I))

omit [HasInjectiveResolutions C] in
include hexact in
private theorem resolution_zero {M : C} (P : InjectiveResolution M) :
    (NatTrans.mapHomologicalComplex a _).app P.cocomplex ≫
      (NatTrans.mapHomologicalComplex c _).app P.cocomplex = 0 := by
  ext k x
  exact (hexact (P.cocomplex.X k) (P.injective k)).apply_apply_eq_zero x

private noncomputable def resolutionSequence {M : C} (P : InjectiveResolution M) :
    ShortComplex (CochainComplex AddCommGrpCat.{w} ℕ) :=
  ShortComplex.mk _ _ (resolution_zero A B E a c hexact P)

omit [HasInjectiveResolutions C] in
private theorem resolutionSequence_shortExact
    (hinj : ∀ (I : C), Injective I → Function.Injective (a.app I))
    (hsurj : ∀ (I : C), Injective I → Function.Surjective (c.app I))
    {M : C} (P : InjectiveResolution M) :
    (resolutionSequence A B E a c hexact P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ab_exact_iff_function_exact _).2
    exact hexact (P.cocomplex.X k) (P.injective k)
  · apply (AddCommGrpCat.mono_iff_injective _).2
    exact hinj (P.cocomplex.X k) (P.injective k)
  · apply (AddCommGrpCat.epi_iff_surjective _).2
    exact hsurj (P.cocomplex.X k) (P.injective k)

private noncomputable def resolutionSequenceMap {M N : C}
    (P : InjectiveResolution M) (Q : InjectiveResolution N)
    (f : P.cocomplex ⟶ Q.cocomplex) :
    resolutionSequence A B E a c hexact P ⟶ resolutionSequence A B E a c hexact Q where
  τ₁ := (A.mapHomologicalComplex _).map f
  τ₂ := (B.mapHomologicalComplex _).map f
  τ₃ := (E.mapHomologicalComplex _).map f
  comm₁₂ := NatTrans.mapHomologicalComplex_naturality a f
  comm₂₃ := NatTrans.mapHomologicalComplex_naturality c f

end

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 0A50, passage to derived functors; Homology Tag 0117.
(blueprint: lem-weil-pbc-right-derived-injective-sequence)

Proof: Evaluate the three functors and the two transformations on a chosen injective
resolution of each object. Exactness gives the zero composite, and the injectivity and
surjectivity hypotheses give a short exact sequence of complexes degree by degree.
Use its homology connecting map, conjugated by the canonical resolution comparisons.
A lift of a coefficient morphism gives a morphism of short exact sequences of complexes;
naturality of the homology connecting map and of the comparison isomorphisms gives a
natural transformation. The three homology exactness assertions transport along those
isomorphisms to the asserted three exact pairs. This works in degree zero as well as in
positive degrees, including the zero and split sequences. -/
theorem rightDerived_injective_sequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (A B E : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive] [E.Additive]
    (a : A ⟶ B) (c : B ⟶ E)
    (hinj : ∀ (I : C), Injective I → Function.Injective (a.app I))
    (hexact : ∀ (I : C), Injective I → Function.Exact (a.app I) (c.app I))
    (hsurj : ∀ (I : C), Injective I → Function.Surjective (c.app I)) :
    ∃ δ : ∀ n : ℕ, E.rightDerived n ⟶ A.rightDerived (n + 1),
      ∀ (M : C) (n : ℕ),
        Function.Exact ((a.rightDerived n).app M) ((c.rightDerived n).app M) ∧
        Function.Exact ((c.rightDerived n).app M) ((δ n).app M) ∧
        Function.Exact ((δ n).app M) ((a.rightDerived (n + 1)).app M) := by
  let S (M : C) := resolutionSequence A B E a c hexact (injectiveResolution M)
  have hS (M : C) : (S M).ShortExact :=
    resolutionSequence_shortExact A B E a c hexact hinj hsurj (injectiveResolution M)
  let e (F : C ⥤ AddCommGrpCat.{w}) [F.Additive] (M : C) (n : ℕ) :=
    (injectiveResolution M).isoRightDerivedObj F n
  let boundary (M : C) (n : ℕ) :=
    (e E M n).hom ≫ (hS M).δ n (n + 1) (by simp) ≫ (e A M (n + 1)).inv
  have natural (n : ℕ) {M N : C} (f : M ⟶ N) :
      (E.rightDerived n).map f ≫ boundary N n =
        boundary M n ≫ (A.rightDerived (n + 1)).map f := by
    let lift := InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M)
    let φ := resolutionSequenceMap A B E a c hexact
      (injectiveResolution M) (injectiveResolution N) lift
    have hd := HomologicalComplex.HomologySequence.δ_naturality φ (hS M) (hS N)
      n (n + 1) (by simp)
    dsimp [φ, resolutionSequenceMap] at hd
    dsimp [boundary, e]
    change _ = _ at hd
    rw [← Category.assoc,
      InjectiveResolution.isoRightDerivedObj_hom_naturality f _ _ lift
        (InjectiveResolution.desc_commutes_zero f _ _) E n]
    simp only [Category.assoc]
    rw [InjectiveResolution.isoRightDerivedObj_inv_naturality f _ _ lift
      (InjectiveResolution.desc_commutes_zero f _ _) A (n + 1)]
    change _ ≫ HomologicalComplex.homologyMap _ _ ≫ _ ≫ _ =
      _ ≫ _ ≫ HomologicalComplex.homologyMap _ _ ≫ _
    rw [← Category.assoc (HomologicalComplex.homologyMap _ _) _ _, ← hd]
    simp only [Category.assoc]
  let δ (n : ℕ) : E.rightDerived n ⟶ A.rightDerived (n + 1) :=
    { app := fun M => boundary M n
      naturality := fun _ _ f => natural n f }
  refine ⟨δ, ?_⟩
  intro M n
  have transport {X Y Z X' Y' Z' : AddCommGrpCat.{w}}
      (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
      (i : X' ≅ X) (j : Y' ≅ Y) (k : Z' ≅ Z)
      (hf : f' ≫ j.hom = i.hom ≫ f) (hg : g' ≫ k.hom = j.hom ≫ g)
      (h : Function.Exact f g) : Function.Exact f' g' := by
    apply (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
      f'.hom g'.hom f.hom g.hom i.hom.hom j.hom.hom k.hom.hom ?_ ?_
      (ConcreteCategory.bijective_of_isIso i.hom).2
      (ConcreteCategory.bijective_of_isIso j.hom)
      (ConcreteCategory.bijective_of_isIso k.hom).1).2 h
    · exact congrArg AddCommGrpCat.Hom.hom hf.symm
    · exact congrArg AddCommGrpCat.Hom.hom hg.symm
  have map_comm (F G : C ⥤ AddCommGrpCat.{w}) [F.Additive] [G.Additive]
      (α : F ⟶ G) (k : ℕ) :
      (α.rightDerived k).app M ≫ (e G M k).hom =
        (e F M k).hom ≫ HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α _).app (injectiveResolution M).cocomplex) k := by
    rw [(injectiveResolution M).rightDerived_app_eq α k]
    simp [e, Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · exact transport _ _ _ _ (e A M n) (e B M n) (e E M n)
      (map_comm A B a n) (map_comm B E c n)
      ((ShortComplex.ab_exact_iff_function_exact _).1 ((hS M).homology_exact₂ n))
  · apply transport _ _ _ _ (e B M n) (e E M n) (e A M (n + 1))
      (map_comm B E c n) ?_
      ((ShortComplex.ab_exact_iff_function_exact _).1
        ((hS M).homology_exact₃ n (n + 1) (by simp)))
    dsimp [δ, boundary]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · apply transport _ _ _ _ (e E M n) (e A M (n + 1)) (e B M (n + 1))
      ?_ (map_comm A B a (n + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        ((hS M).homology_exact₁ n (n + 1) (by simp)))
    dsimp [δ, boundary]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory
