/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.CategoryTheory.Generator.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Detection by the affine étale free complexes

Source: Bhatt--Scholze, Proposition 6.4.8, first paragraph.
(blueprint: lem-pur-affine-etale-free-detection)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The free rank-one sheaf at an affine étale object, placed in degree zero.
Source: Bhatt--Scholze, Proposition 6.4.8, coherent generators.
(blueprint: lem-pur-affine-etale-free-detection) -/
noncomputable def affineEtaleFreeComplex
    (C : Type (u + 1)) [CommRing C] (T : Scheme.{u}) (U : T.AffineEtale) :
    DerivedCategoryModule C T :=
  (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Sheaf.freeYoneda T.smallEtaleTopology ((Scheme.AffineEtale.Spec T).obj U)
      (ModuleCat.of C C))

set_option backward.isDefEq.respectTransparency false in
private theorem free_separating (C : Type (u + 1)) [CommRing C] (T : Scheme.{u}) :
    ObjectProperty.IsSeparating (.ofObj (fun U : T.AffineEtale ↦
      Sheaf.freeYoneda T.smallEtaleTopology ((Scheme.AffineEtale.Spec T).obj U)
        (ModuleCat.of C C))) := by
  intro M N f g hh
  apply (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)).map_injective
  apply (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense
    T.smallEtaleTopology (Scheme.AffineEtale.Spec T) M.obj N.obj N.property).injective
  ext ⟨U⟩ x
  let e (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} C)) :=
    Sheaf.freeYonedaHomEquiv (J := T.smallEtaleTopology)
      (X := (Scheme.AffineEtale.Spec T).obj U) (M := ModuleCat.of C C) (F := M)
  let a : ModuleCat.of C C ⟶ M.obj.obj (op ((Scheme.AffineEtale.Spec T).obj U)) :=
    ModuleCat.ofHom
      { toFun := fun r ↦ r • x
        map_add' := fun r s ↦ add_smul r s x
        map_smul' := fun r s ↦ mul_smul r s x }
  have hn (a : Sheaf.freeYoneda T.smallEtaleTopology
      ((Scheme.AffineEtale.Spec T).obj U) (ModuleCat.of C C) ⟶ M)
      (k : M ⟶ N) : e N (a ≫ k) = e M a ≫ k.hom.app _ := by
    dsimp [e, Sheaf.freeYonedaHomEquiv]
    erw [Adjunction.homEquiv_naturality_right, Presheaf.freeYonedaHomEquiv_comp]
    rfl
  have h := congrArg (e N) (hh _ (ObjectProperty.ofObj_apply _ U) ((e M).symm a))
  rw [hn, hn, Equiv.apply_symm_apply] at h
  have h' := congrArg (fun k ↦ k (1 : C)) h
  simpa [a] using h'

private theorem exact_of_classes
    {D : Type u} [Category.{v} D] [Abelian D] {ι : Type w} (G : ι → D)
    (hsep : ObjectProperty.IsSeparating (.ofObj G))
    (I : CochainComplex D ℤ)
    (hh : ∀ i n, Subsingleton
      (CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor D 0).obj (G i)) I n)) :
    ∀ n, I.ExactAt n := by
  intro n
  let S := I.sc' (n - 1) n (n + 1)
  have hepi : Epi S.toCycles := by
    constructor
    intro Z f g hfg
    apply hsep f g
    rintro _ ⟨i⟩ a
    have := hh i n
    obtain ⟨b, hb⟩ :=
      (CochainComplex.subsingleton_cohomologyClass_singleFunctor_iff (G i) I n).mp
        inferInstance (a ≫ S.iCycles) (by
          change (a ≫ S.iCycles) ≫ S.g = 0
          simp only [Category.assoc, ShortComplex.iCycles_g, comp_zero])
    have hb' : b ≫ S.toCycles = a := by
      rw [← cancel_mono S.iCycles, Category.assoc, ShortComplex.toCycles_i]
      exact hb
    rw [← hb', Category.assoc, Category.assoc, hfg]
  apply (I.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
  exact (ShortComplex.exact_iff_epi_toCycles S).2 hepi

private theorem zero_of_tests
    {D : Type u} [Category.{v} D] [Abelian D] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D] {ι : Type w} (G : ι → D)
    (hsep : ObjectProperty.IsSeparating (.ofObj G))
    (K : _root_.DerivedCategory D)
    (hh : ∀ i (n : ℤ), Subsingleton
      ((_root_.DerivedCategory.singleFunctor D 0).obj (G i) ⟶ K⟦n⟧)) : IsZero K := by
  classical
  let Q := _root_.DerivedCategory.Q (C := D)
  obtain ⟨I, _, r, _, _⟩ :=
    Abelian.HasKInjectiveResolutions.exists_isKInjective (Q.objPreimage K)
  let e : K ≅ Q.obj I := (Q.objObjPreimageIso K).symm ≪≫ asIso (Q.map r)
  have hclasses (i : ι) (n : ℤ) : Subsingleton
      (CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor D 0).obj (G i)) I n) := by
    let S := (CochainComplex.singleFunctor D 0).obj (G i)
    let q := HomotopyCategory.quotient D (.up ℤ)
    let es := (_root_.DerivedCategory.quotientCompQhIso D).app S ≪≫
      ((_root_.DerivedCategory.singleFunctorIsoCompQ D 0).app (G i)).symm
    let et := (_root_.DerivedCategory.quotientCompQhIso D).app (I⟦n⟧) ≪≫
      (Q.commShiftIso n).app I ≪≫ ((shiftFunctor _ n).mapIso e).symm
    have := hh i n
    have : Subsingleton
        (_root_.DerivedCategory.Qh.obj (q.obj S) ⟶
          _root_.DerivedCategory.Qh.obj (q.obj (I⟦n⟧))) :=
      (Iso.homCongr es et).injective.subsingleton
    have : Subsingleton (q.obj S ⟶ q.obj (I⟦n⟧)) :=
      (CochainComplex.IsKInjective.Qh_map_bijective (q.obj S) (I⟦n⟧)).1.subsingleton
    exact CochainComplex.HomComplex.CohomologyClass.homAddEquiv.injective.subsingleton
  have he := exact_of_classes G hsep I hclasses
  suffices hz : IsZero (Q.obj I) from hz.of_iso e
  apply _root_.DerivedCategory.isZero_of_forall_isZero_homology
  intro n
  exact (he n).isZero_homology.of_iso
    ((_root_.DerivedCategory.homologyFunctorFactors D n).app I)

set_option backward.isDefEq.respectTransparency false in
private theorem iso_of_tests
    {D : Type u} [Category.{v} D] [Abelian D] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D] {ι : Type w} (G : ι → D)
    (hsep : ObjectProperty.IsSeparating (.ofObj G))
    {A B : _root_.DerivedCategory D} (h : A ⟶ B)
    (hh : ∀ i (n : ℤ), Function.Bijective (fun
      (a : ((_root_.DerivedCategory.singleFunctor D 0).obj (G i))⟦n⟧ ⟶ A) ↦ a ≫ h)) :
    IsIso h := by
  let E := fun i ↦ (_root_.DerivedCategory.singleFunctor D 0).obj (G i)
  have hh' (i : ι) (n : ℤ) : Function.Bijective
      (fun (a : E i ⟶ A⟦n⟧) ↦ a ≫ h⟦n⟧') := by
    let adj := (shiftEquiv' (_root_.DerivedCategory D) (-n) n (neg_add_cancel n)).toAdjunction
    let eA := adj.homEquiv (E i) A
    let eB := adj.homEquiv (E i) B
    have hn (a : (E i)⟦-n⟧ ⟶ A) : eB (a ≫ h) = eA a ≫ h⟦n⟧' := by
      exact adj.homEquiv_naturality_right a h
    constructor
    · intro a b hab
      apply eA.symm.injective
      apply (hh i (-n)).1
      apply eB.injective
      rw [hn, hn, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hab
    · intro b
      obtain ⟨a, ha⟩ := (hh i (-n)).2 (eB.symm b)
      refine ⟨eA a, ?_⟩
      change a ≫ h = eB.symm b at ha
      change eA a ≫ h⟦n⟧' = b
      exact (hn a).symm.trans (congrArg eB ha |>.trans (eB.apply_symm_apply b))
  obtain ⟨K, g, d, hT⟩ := Pretriangulated.distinguished_cocone_triangle h
  let T := Pretriangulated.Triangle.mk h g d
  have hz : IsZero K := by
    apply zero_of_tests G hsep K
    intro i n
    apply subsingleton_of_forall_eq (0 : E i ⟶ K⟦n⟧)
    intro a
    let Tn := T⟦n⟧
    have hTn : Tn ∈ distTriang (_root_.DerivedCategory D) :=
      Pretriangulated.Triangle.shift_distinguished T hT n
    have hinj : Function.Injective
        (fun (b : E i ⟶ (A⟦n⟧)⟦(1 : ℤ)⟧) ↦ b ≫ (h⟦n⟧')⟦(1 : ℤ)⟧') := by
      intro b c hbc
      apply (cancel_mono ((shiftFunctorAdd (_root_.DerivedCategory D) n 1).inv.app A)).1
      apply (hh' i (n + 1)).1
      have he := congrArg
        (fun t ↦ t ≫ (shiftFunctorAdd (_root_.DerivedCategory D) n 1).inv.app B) hbc
      have hn : (h⟦n⟧')⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd (_root_.DerivedCategory D) n 1).inv.app B =
          (shiftFunctorAdd (_root_.DerivedCategory D) n 1).inv.app A ≫ h⟦n + 1⟧' :=
        (shiftFunctorAdd (_root_.DerivedCategory D) n 1).inv.naturality h
      simpa only [Category.assoc, hn] using he
    have hm : Tn.mor₁ = n.negOnePow • h⟦n⟧' := rfl
    have hinj' : Function.Injective
        (fun (b : E i ⟶ (A⟦n⟧)⟦(1 : ℤ)⟧) ↦ b ≫ Tn.mor₁⟦(1 : ℤ)⟧') := by
      intro b c hbc
      apply hinj
      apply MulAction.injective n.negOnePow
      simpa only [hm, Functor.map_units_smul, Linear.comp_units_smul] using hbc
    have ha : a ≫ Tn.mor₃ = 0 := by
      apply hinj'
      dsimp only
      rw [Category.assoc, Pretriangulated.comp_distTriang_mor_zero₃₁ Tn hTn,
        comp_zero, zero_comp]
    obtain ⟨b, hb⟩ := Tn.coyoneda_exact₃ hTn a ha
    obtain ⟨c, hc⟩ := (hh' i n).2 (n.negOnePow⁻¹ • b)
    change c ≫ h⟦n⟧' = n.negOnePow⁻¹ • b at hc
    have hc' : c ≫ Tn.mor₁ = b := by
      change c ≫ (n.negOnePow • h⟦n⟧') = b
      rw [Linear.comp_units_smul, hc, smul_inv_smul]
    rw [hb, ← hc', Category.assoc,
      Pretriangulated.comp_distTriang_mor_zero₁₂ Tn hTn, comp_zero]
  exact (T.isZero₃_iff_isIso₁ hT).1 hz

/-- The shifts of the affine free complexes detect isomorphisms.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 6.4.8,
first paragraph, expanded by the K-injective argument in the parent node.

Proof in words: free Yoneda and cover density of the affine étale basis show that
these free sheaves separate ordinary sheaf morphisms. For any separating family
in an abelian category with K-injective resolutions, its degree-zero single
complexes detect zero derived objects: resolve an object by a K-injective I.
Vanishing of all shifted Hom groups gives vanishing of the corresponding Hom
complex cohomology classes. The single-complex formula says every map from a
generator to cycles lifts through the preceding differential. Separation then
makes the map to cycles epi, so I is exact and the derived object is zero.
For a morphism h satisfying the hypothesis, take a distinguished cone triangle.
The two adjacent postcomposition bijections and the exact Hom sequence show that
all shifted tests of the cone vanish. In this calculation the shifted triangle
maps carry the invertible scalar (-1)^n; cancel it explicitly. The cone is zero
by the preceding argument, so h is invertible. This works for arbitrary
unbounded objects and includes the empty scheme and zero coefficient ring.
(blueprint: lem-pur-affine-etale-free-detection) -/
theorem isIso_of_affineEtaleFreeComplex
    (C : Type (u + 1)) [CommRing C] (T : Scheme.{u})
    {A B : DerivedCategoryModule C T} (h : A ⟶ B)
    (hh : ∀ (U : T.AffineEtale) (n : ℤ),
      Function.Bijective
        (fun (φ : (affineEtaleFreeComplex C T U)⟦n⟧ ⟶ A) ↦ φ ≫ h)) :
    IsIso h := by
  apply iso_of_tests
    (fun U : T.AffineEtale ↦ Sheaf.freeYoneda T.smallEtaleTopology
      ((Scheme.AffineEtale.Spec T).obj U) (ModuleCat.of C C))
    (free_separating C T) h
  exact hh

end AlgebraicGeometry.Etale
