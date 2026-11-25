/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Tactic.Abel

/-! # The ordinary derived free Weil resolution

Source: blueprint main-20261015, `cor-coef-verdier-weil-equivariance.proof.md`, final
exceptional-adjunction assertion, and the explicit ordinary-derived expansion in
`lem-sf-free-derived-weil-resolution` (blueprint: lem-sf-free-derived-weil-resolution).

The integer powers, free pair, and adjunction are the existing `IsoAlgebra.Free`
constructions. The isomorphisms `θ` below are their iterated structure maps. In particular,
`θ n ≪≫ (θ (n - 1)).symm` is exactly the coherent map `P^(n-1)(φ)` in the node.
The localization comparison is built from the standard exact-functor factorizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]

/-- Structural assertions for the free and forgetful functors. Source: blueprint
ordinary-derived expansion, steps 1--4
(blueprint: lem-sf-free-derived-weil-resolution).

Proof: step 1 applies the heart paragraph of
`lem-sf-fixed-pair-derived-forget-comparison` to the autoequivalence F. Kernels and
cokernels are created on underlying objects. The free object is the existing sum
of all integer translates, with successor structure, and its degree-zero summand
gives the adjunction. Exact sums make this left adjoint exact. Its value on a
separator is a separator, and filtered colimits are exact after forgetting, so the
heart is Grothendieck. Step 2 constructs coproducts with the component structure
isomorphisms; the equivalence preserves sums (`lem-galois-equivalence-preserves-limits`),
and the intertwining equation is tested on every summand, including the empty family. -/
theorem freeWeil_heart_properties :
    IsGrothendieckAbelian.{w} (IsoAlgebra F) ∧
      PreservesFiniteLimits (forget F) ∧ PreservesFiniteColimits (forget F) ∧
      (forget F).ReflectsIsomorphisms ∧
      (∀ J : Type w, PreservesColimitsOfShape (Discrete J) (forget F)) ∧
      PreservesFiniteLimits (Free.functor F) ∧ PreservesFiniteColimits (Free.functor F) ∧
      Nonempty (Free.functor F ⊣ forget F) ∧
      (∀ M : C, ((Free.functor F).obj M).carrier = ∐ (Free.obj F M)) ∧
      (∀ (M : C) (n : ℤ),
        F.map (Sigma.ι (Free.obj F M) n) ≫ ((Free.functor F).obj M).str.hom =
          (Free.objSucc F M n).hom ≫ Sigma.ι (Free.obj F M) (n + 1)) := by
  have : HasCoproducts.{0} C := hasCoproducts_shrink.{0, w}
  have : AB4OfSize.{0} C := AB4OfSize_shrink.{0, w} C
  have : HasExactColimitsOfShape (Discrete ℤ) C := inferInstance
  have : PreservesFiniteLimits (Free.functor F) :=
    (Free.functor F).preservesFiniteLimits_of_preservesHomology
  exact ⟨isGrothendieckAbelian F, inferInstance, inferInstance, inferInstance,
    fun J ↦ inferInstance, inferInstance, inferInstance, ⟨Free.adjunction F⟩,
    fun M ↦ rfl, fun M n ↦ Free.map_ι_comp_str F M n⟩

/-- Expose the exactness assertion of the heart theorem to the derived-functor API.
Source: ordinary-derived expansion, steps 1 and 3
(blueprint: lem-sf-free-derived-weil-resolution). -/
instance freeWeil_preservesFiniteLimits : PreservesFiniteLimits (Free.functor F) :=
  (freeWeil_heart_properties F).2.2.2.2.2.1

variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

/-- The specified localization of the existing free adjunction, with its original
termwise unit and counit. Source: ordinary-derived expansion, step 3, and
`def-weil-exact-derived-adjunction`
(blueprint: lem-sf-free-derived-weil-resolution). -/
def freeWeilDerivedAdjunction :
    (Free.functor F).mapDerivedCategory ⊣ (forget F).mapDerivedCategory :=
  (Free.adjunction F).mapExactDerivedCategory

/-- Standard comparison between the composite derived free-forgetful functor on a
representative and the localization of its termwise composite. Source: ordinary
derived expansion, steps 3 and 9; the two exact-functor factorizations
(blueprint: lem-sf-free-derived-weil-resolution). -/
def freeWeilLocalizationComponent (K : CochainComplex (IsoAlgebra F) ℤ) :
    ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory).obj
        (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Free.functor F).mapDerivedCategory.mapIso
      ((forget F).mapDerivedCategoryFactors.app K) ≪≫
    (Free.functor F).mapDerivedCategoryFactors.app
      (((forget F).mapHomologicalComplex (.up ℤ)).obj K)

/-- Exact induction and forgetting on the ordinary unbounded derived categories.
The adjunction used in the resolution is the specified localization
`(Free.adjunction F).mapExactDerivedCategory`.
Source: ordinary-derived expansion, steps 3--4
(blueprint: lem-sf-free-derived-weil-resolution).

Proof: step 3 uses `situation-conventions` and
`def-weil-exact-derived-adjunction`. Apply the heart unit and counit termwise and
localize; their triangle identities persist, giving the indicated exact adjunction.
The first paragraph of `lem-sf-fixed-pair-derived-forget-comparison` gives derived
conservativity. Step 4 uses `lem-kun-grothendieck-derived-coproducts` in both hearts:
termwise coproducts compute unbounded derived coproducts, and the underlying termwise
coproduct cocone is preserved, so localization proves preservation of every small sum. -/
theorem freeWeil_derived_properties :
    (Free.functor F).mapDerivedCategory.IsTriangulated ∧
      (forget F).mapDerivedCategory.IsTriangulated ∧
      Nonempty ((Free.functor F).mapDerivedCategory ⊣ (forget F).mapDerivedCategory) ∧
      (forget F).mapDerivedCategory.ReflectsIsomorphisms ∧
      ∀ J : Type w,
        PreservesColimitsOfShape (Discrete J) (forget F).mapDerivedCategory := by
  have : IsGrothendieckAbelian.{w} (IsoAlgebra F) := isGrothendieckAbelian F
  have : Abelian.HasKInjectiveResolutions C :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  have : Abelian.HasKInjectiveResolutions (IsoAlgebra F) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{w}
  refine ⟨inferInstance, inferInstance, ⟨freeWeilDerivedAdjunction F⟩, ?_,
    fun J ↦ (forget F).mapDerivedCategory_preservesCoproducts J⟩
  constructor
  intro X Y f hf
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso ((forget F).map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff ((forget F).mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ (forget F)

section

omit [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

omit [Abelian C] [IsGrothendieckAbelian.{w} C] [F.Additive] in
private theorem freeWeil_hom_isIso (M : IsoAlgebra F) (n : ℤ) :
    IsIso (Free.hom M (𝟙 M.carrier) n) := by
  have hp (k : ℕ) : IsIso (Free.posHom M (𝟙 M.carrier) k) := by
    induction k with
    | zero => change IsIso (𝟙 M.carrier); infer_instance
    | succ k hk =>
      change IsIso (F.map (Free.posHom M (𝟙 M.carrier) k) ≫ M.str.hom)
      infer_instance
  have hn (k : ℕ) : IsIso (Free.negHom M (𝟙 M.carrier) k) := by
    induction k with
    | zero =>
      have h : IsIso (F.map (Free.negHom M (𝟙 M.carrier) 0)) := by
        rw [Free.negHom, F.map_preimage]
        exact (F.asEquivalence.counitIso.app M.carrier ≪≫
          Iso.refl M.carrier ≪≫ M.str.symm).isIso_hom
      exact isIso_of_reflects_iso _ F
    | succ k hk =>
      have h : IsIso (F.map (Free.negHom M (𝟙 M.carrier) (k + 1))) := by
        rw [Free.negHom, F.map_preimage]
        infer_instance
      exact isIso_of_reflects_iso _ F
  cases n with
  | ofNat k => exact hp k
  | negSucc k => exact hn k

private def freeWeilTheta (M : IsoAlgebra F) (n : ℤ) :
    Free.obj F M.carrier n ≅ M.carrier := by
  have := freeWeil_hom_isIso F M n
  exact asIso (Free.hom M (𝟙 M.carrier) n)

omit [Abelian C] [IsGrothendieckAbelian.{w} C] [F.Additive] in
private lemma freeWeilTheta_rec (M : IsoAlgebra F) (n : ℤ) :
    F.map (freeWeilTheta F M n).hom ≫ M.str.hom =
      (Free.objSucc F M.carrier n).hom ≫ (freeWeilTheta F M (n + 1)).hom :=
  Free.map_hom_comp_str M (𝟙 M.carrier) n

omit [F.Additive] in
private lemma freeWeil_counit (M : IsoAlgebra F) (n : ℤ) :
    Sigma.ι (Free.obj F M.carrier) n ≫
      (forget F).map ((Free.adjunction F).counit.app M) = (freeWeilTheta F M n).hom := by
  change Sigma.ι _ n ≫ Sigma.desc _ = _
  exact Sigma.ι_comp_desc _ _

private def freeWeilShiftApp (M : IsoAlgebra F) :
    (Free.functor F).obj M.carrier ⟶ (Free.functor F).obj M.carrier :=
  Free.desc ((Free.functor F).obj M.carrier)
    ((freeWeilTheta F M (-1)).inv ≫ Sigma.ι (Free.obj F M.carrier) (-1))

private lemma freeWeilShift_summand (M : IsoAlgebra F) (n : ℤ) :
    Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map (freeWeilShiftApp F M) =
      (freeWeilTheta F M n).hom ≫ (freeWeilTheta F M (n - 1)).inv ≫
        Sigma.ι (Free.obj F M.carrier) (n - 1) := by
  have step (k : ℤ) :
      (Sigma.ι (Free.obj F M.carrier) k ≫ (forget F).map (freeWeilShiftApp F M) =
        (freeWeilTheta F M k).hom ≫ (freeWeilTheta F M (k - 1)).inv ≫
          Sigma.ι (Free.obj F M.carrier) (k - 1)) ↔
      (Sigma.ι (Free.obj F M.carrier) (k + 1) ≫
          (forget F).map (freeWeilShiftApp F M) =
        (freeWeilTheta F M (k + 1)).hom ≫ (freeWeilTheta F M k).inv ≫
          Sigma.ι (Free.obj F M.carrier) k) := by
    have ht := freeWeilTheta_rec F M k
    have hs := Free.map_ι_comp_comp_str (freeWeilShiftApp F M) k
    change F.map (Sigma.ι (Free.obj F M.carrier) k ≫
        (forget F).map (freeWeilShiftApp F M)) ≫ (Free.str F M.carrier).hom =
      (Free.objSucc F M.carrier k).hom ≫ Sigma.ι (Free.obj F M.carrier) (k + 1) ≫
        (forget F).map (freeWeilShiftApp F M) at hs
    have he : F.map ((freeWeilTheta F M k).hom ≫
        (freeWeilTheta F M (k - 1)).inv ≫ Sigma.ι (Free.obj F M.carrier) (k - 1)) ≫
        (Free.str F M.carrier).hom =
      (Free.objSucc F M.carrier k).hom ≫ (freeWeilTheta F M (k + 1)).hom ≫
        (freeWeilTheta F M k).inv ≫ Sigma.ι (Free.obj F M.carrier) k := by
      have hti (j : ℤ) : F.map (freeWeilTheta F M j).inv ≫
          (Free.objSucc F M.carrier j).hom =
          M.str.hom ≫ (freeWeilTheta F M (j + 1)).inv := by
        apply (cancel_epi (F.map (freeWeilTheta F M j).hom)).1
        simp only [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
        rw [← Category.assoc, freeWeilTheta_rec]
        simp
      simp only [F.map_comp, Category.assoc, Free.map_ι_comp_str]
      rw [← Category.assoc (F.map (freeWeilTheta F M (k - 1)).inv), hti]
      simp only [Category.assoc]
      rw [← Category.assoc (F.map (freeWeilTheta F M k).hom), ht]
      simp only [Category.assoc]
      rw [show k - 1 + 1 = k by omega]
    constructor
    · intro hk
      rw [hk, he] at hs
      exact (cancel_epi (Free.objSucc F M.carrier k).hom).1 hs.symm
    · intro hk
      apply F.map_injective
      apply (cancel_mono (Free.str F M.carrier).hom).1
      rw [hs, hk, he]
  induction n using Int.induction_on with
  | zero =>
    change Sigma.ι _ 0 ≫ (Free.desc _ _).hom.f = _
    change _ = 𝟙 M.carrier ≫ _
    rw [show (0 : ℤ) - 1 = -1 by omega]
    simpa only [Category.id_comp] using
      (Free.ι_desc_hom_f ((Free.functor F).obj M.carrier)
        ((freeWeilTheta F M (-1)).inv ≫ Sigma.ι (Free.obj F M.carrier) (-1)))
  | succ k hk =>
    rw [show (k : ℤ) + 1 - 1 = k by omega]
    exact (step k).1 hk
  | pred k hk =>
    apply (step (-(k : ℤ) - 1)).2
    rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by omega]
    exact hk

omit [F.Additive] in
private lemma freeWeil_map_summand {M N : IsoAlgebra F} (f : M ⟶ N) (n : ℤ) :
    Sigma.ι (Free.obj F M.carrier) n ≫
      (forget F).map ((Free.functor F).map ((forget F).map f)) =
      Free.objMap F ((forget F).map f) n ≫ Sigma.ι (Free.obj F N.carrier) n :=
  Sigma.ι_map _ _

omit [F.Additive] in
private lemma freeWeilTheta_naturality {M N : IsoAlgebra F} (f : M ⟶ N) (n : ℤ) :
    Free.objMap F ((forget F).map f) n ≫ (freeWeilTheta F N n).hom =
      (freeWeilTheta F M n).hom ≫ (forget F).map f := by
  have h := congrArg (fun g ↦ Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map g)
    ((Free.adjunction F).counit.naturality f)
  simp only [Functor.comp_map, Functor.id_map, Functor.map_comp, ← Category.assoc,
    freeWeil_map_summand] at h
  simpa only [Category.assoc, freeWeil_counit] using h

omit [F.Additive] in
private lemma freeWeilTheta_inv_naturality {M N : IsoAlgebra F} (f : M ⟶ N) (n : ℤ) :
    (freeWeilTheta F M n).inv ≫ Free.objMap F ((forget F).map f) n =
      (forget F).map f ≫ (freeWeilTheta F N n).inv := by
  apply (cancel_epi (freeWeilTheta F M n).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← freeWeilTheta_naturality]
  simp

private def freeWeilShift : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F where
  app := freeWeilShiftApp F
  naturality M N f := by
    apply Free.hom_ext
    change Sigma.ι (Free.obj F M.carrier) 0 ≫
        (Free.map f.hom.f).hom.f ≫ (freeWeilShiftApp F N).hom.f =
      Sigma.ι (Free.obj F M.carrier) 0 ≫
        (freeWeilShiftApp F M).hom.f ≫ (Free.map f.hom.f).hom.f
    rw [← Category.assoc, Free.map_hom_f, Sigma.ι_map, Free.objMap_zero]
    dsimp only [freeWeilShiftApp]
    rw [Category.assoc, Free.ι_desc_hom_f, Free.ι_desc_hom_f_assoc]
    rw [Category.assoc, Sigma.ι_map]
    simpa only [Category.assoc, forget_map] using
      congrArg (fun t ↦ t ≫ Sigma.ι (Free.obj F N.carrier) (-1))
        (freeWeilTheta_inv_naturality F f (-1)).symm

private def freeWeilDifference : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F :=
  𝟙 _ - freeWeilShift F

private lemma freeWeilDifference_summand (M : IsoAlgebra F) (n : ℤ) :
    Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map ((freeWeilDifference F).app M) =
      Sigma.ι (Free.obj F M.carrier) n -
        (freeWeilTheta F M n).hom ≫ (freeWeilTheta F M (n - 1)).inv ≫
          Sigma.ι (Free.obj F M.carrier) (n - 1) := by
  change Sigma.ι _ n ≫ (forget F).map (𝟙 _ - freeWeilShiftApp F M) = _
  rw [Functor.map_sub, Functor.map_id, Preadditive.comp_sub]
  change Sigma.ι _ n ≫ 𝟙 (∐ Free.obj F M.carrier) - _ = _
  rw [Category.comp_id, freeWeilShift_summand]

private lemma freeWeilDifference_counit (M : IsoAlgebra F) :
    (freeWeilDifference F).app M ≫ (Free.adjunction F).counit.app M = 0 := by
  apply (forget F).map_injective
  change (forget F).map ((freeWeilDifference F).app M) ≫
    (forget F).map ((Free.adjunction F).counit.app M) = 0
  apply Sigma.hom_ext
  intro n
  change Sigma.ι (Free.obj F M.carrier) n ≫
    ((forget F).map ((freeWeilDifference F).app M) ≫
      (forget F).map ((Free.adjunction F).counit.app M)) = _
  rw [← Category.assoc, freeWeilDifference_summand, Preadditive.sub_comp]
  simp only [Category.assoc, freeWeil_counit, Iso.inv_hom_id,
    Category.comp_id, sub_self, Limits.comp_zero]

private def freeWeilSection (M : IsoAlgebra F) (n : ℤ) :
    M.carrier ⟶ ∐ Free.obj F M.carrier :=
  (freeWeilTheta F M n).inv ≫ Sigma.ι (Free.obj F M.carrier) n

private def freeWeilPrimitive (M : IsoAlgebra F) :
    ℤ → (M.carrier ⟶ ∐ Free.obj F M.carrier)
  | .ofNat k => ∑ j ∈ Finset.range k, freeWeilSection F M ((j : ℤ) + 1)
  | .negSucc k => -∑ j ∈ Finset.range (k + 1), freeWeilSection F M (-(j : ℤ))

omit [F.Additive] in
private lemma freeWeilPrimitive_zero (M : IsoAlgebra F) :
    freeWeilPrimitive F M 0 = 0 := by simp [freeWeilPrimitive]

omit [F.Additive] in
private lemma freeWeilPrimitive_step (M : IsoAlgebra F) (n : ℤ) :
    freeWeilPrimitive F M n - freeWeilPrimitive F M (n - 1) =
      freeWeilSection F M n := by
  rcases n with k | k
  · cases k with
    | zero =>
      change (0 : M.carrier ⟶ ∐ Free.obj F M.carrier) -
        (-∑ j ∈ Finset.range 1, freeWeilSection F M (-(j : ℤ))) = _
      simp
    | succ k =>
      change freeWeilPrimitive F M ((k : ℤ) + 1) -
        freeWeilPrimitive F M ((k : ℤ) + 1 - 1) = _
      rw [show (k : ℤ) + 1 - 1 = k by omega]
      change (∑ j ∈ Finset.range (k + 1), freeWeilSection F M ((j : ℤ) + 1)) -
        (∑ j ∈ Finset.range k, freeWeilSection F M ((j : ℤ) + 1)) = _
      rw [Finset.sum_range_succ]
      abel
  · have hn : (Int.negSucc k - 1) = Int.negSucc (k + 1) := by omega
    rw [hn]
    simp only [freeWeilPrimitive, Finset.sum_range_succ]
    rw [show (Int.negSucc k) = -((k + 1 : ℕ) : ℤ) by omega]
    abel

private lemma freeWeilSection_difference (M : IsoAlgebra F) (n : ℤ) :
    freeWeilSection F M n ≫ (forget F).map ((freeWeilDifference F).app M) =
      freeWeilSection F M n - freeWeilSection F M (n - 1) := by
  dsimp only [freeWeilSection]
  rw [Category.assoc, freeWeilDifference_summand, Preadditive.comp_sub]
  simp only [Iso.inv_hom_id_assoc]

private lemma freeWeilPrimitive_difference (M : IsoAlgebra F) (n : ℤ) :
    freeWeilPrimitive F M n ≫ (forget F).map ((freeWeilDifference F).app M) =
      freeWeilSection F M n - freeWeilSection F M 0 := by
  have step (k : ℤ) :
      (freeWeilPrimitive F M (k - 1) ≫ (forget F).map ((freeWeilDifference F).app M) =
        freeWeilSection F M (k - 1) - freeWeilSection F M 0) ↔
      (freeWeilPrimitive F M k ≫ (forget F).map ((freeWeilDifference F).app M) =
        freeWeilSection F M k - freeWeilSection F M 0) := by
    have he' := congrArg (fun f ↦ f ≫ (forget F).map ((freeWeilDifference F).app M))
      (freeWeilPrimitive_step F M k)
    rw [Preadditive.sub_comp, freeWeilSection_difference] at he'
    constructor
    · intro h
      rw [h] at he'
      apply (sub_eq_iff_eq_add).1 at he'
      rw [he']
      abel
    · intro h
      rw [h] at he'
      apply (sub_eq_iff_eq_add).1 at he'
      apply (add_left_cancel (a := freeWeilSection F M k - freeWeilSection F M (k - 1)))
      rw [← he']
      abel
  induction n using Int.induction_on with
  | zero => simp [freeWeilPrimitive_zero]
  | succ k hk =>
    apply (step (k + 1)).1
    simpa only [add_sub_cancel_right] using hk
  | pred k hk =>
    exact (step (-(k : ℤ))).2 hk

private def freeWeilRetraction (M : IsoAlgebra F) :
    (∐ Free.obj F M.carrier) ⟶ ∐ Free.obj F M.carrier :=
  Sigma.desc (fun n ↦ (freeWeilTheta F M n).hom ≫ freeWeilPrimitive F M n)

private lemma freeWeil_underlying_split (M : IsoAlgebra F) :
    (ShortComplex.mk ((freeWeilDifference F).app M)
      ((Free.adjunction F).counit.app M) (freeWeilDifference_counit F M)).map
        (forget F) |>.ShortExact := by
  apply ShortComplex.Splitting.shortExact
  refine ⟨freeWeilRetraction F M, Sigma.ι (Free.obj F M.carrier) 0, ?_, ?_, ?_⟩
  · change (forget F).map ((freeWeilDifference F).app M) ≫
      freeWeilRetraction F M = 𝟙 (∐ Free.obj F M.carrier)
    apply Sigma.hom_ext
    intro n
    change Sigma.ι (Free.obj F M.carrier) n ≫
      (forget F).map ((freeWeilDifference F).app M) ≫ freeWeilRetraction F M =
        Sigma.ι (Free.obj F M.carrier) n ≫ 𝟙 _
    erw [← Category.assoc, freeWeilDifference_summand, Preadditive.sub_comp]
    simp only [Category.assoc, freeWeilRetraction, Sigma.ι_comp_desc,
      Iso.inv_hom_id_assoc]
    rw [← Preadditive.comp_sub, freeWeilPrimitive_step]
    simp [freeWeilSection]
  · exact freeWeil_counit F M 0
  · change (freeWeilRetraction F M ≫ (forget F).map ((freeWeilDifference F).app M) :
        (∐ Free.obj F M.carrier) ⟶ ∐ Free.obj F M.carrier) +
      ((forget F).map ((Free.adjunction F).counit.app M) ≫
        Sigma.ι (Free.obj F M.carrier) 0 :
          (∐ Free.obj F M.carrier) ⟶ ∐ Free.obj F M.carrier) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_add, ← Category.assoc, freeWeilRetraction, Sigma.ι_comp_desc,
      freeWeil_counit]
    rw [Category.assoc, freeWeilPrimitive_difference]
    simp only [Preadditive.comp_sub, freeWeilSection, Iso.hom_inv_id_assoc,
      Category.comp_id]
    have hθ0 : freeWeilTheta F M 0 = Iso.refl _ := Iso.ext (by rfl)
    rw [hθ0]
    change Sigma.ι _ n - (freeWeilTheta F M n).hom ≫
        𝟙 M.carrier ≫ Sigma.ι (Free.obj F M.carrier) 0 +
      (freeWeilTheta F M n).hom ≫ Sigma.ι (Free.obj F M.carrier) 0 = _
    simp

private lemma freeWeil_shortExact (M : IsoAlgebra F) :
    (ShortComplex.mk ((freeWeilDifference F).app M)
      ((Free.adjunction F).counit.app M) (freeWeilDifference_counit F M)).ShortExact := by
  let U : Unit → IsoAlgebra F ⥤ C := fun _ ↦ forget F
  have hU : JointlyReflectIsomorphisms U := by
    constructor
    intro X Y f hf
    have : IsIso ((forget F).map f) := hf ()
    exact isIso_of_reflects_iso f (forget F)
  exact (hU.shortExact_iff _).2 (fun _ ↦ freeWeil_underlying_split F M)

private lemma freeWeil_complex_zero (K : CochainComplex (IsoAlgebra F) ℤ) :
    ((freeWeilDifference F).mapHomologicalComplex (.up ℤ)).app K ≫
      ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K = 0 := by
  ext n
  exact freeWeilDifference_counit F (K.X n)

private lemma freeWeil_complex_shortExact (K : CochainComplex (IsoAlgebra F) ℤ) :
    (ShortComplex.mk (((freeWeilDifference F).mapHomologicalComplex (.up ℤ)).app K)
      (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K)
      (freeWeil_complex_zero F K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact freeWeil_shortExact F (K.X n)

end

private def freeWeilComparison :
    DerivedCategory.Q ⋙
        ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory) ≅
      (forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (freeWeilLocalizationComponent F) (fun f ↦ by
    dsimp [freeWeilLocalizationComponent]
    erw [Category.assoc, ← (Free.functor F).mapDerivedCategory.map_comp_assoc,
      (forget F).mapDerivedCategoryFactors_hom_naturality,
      (Free.functor F).mapDerivedCategory.map_comp,
      Category.assoc, (Free.functor F).mapDerivedCategoryFactors_hom_naturality]
    rfl)

private lemma freeWeil_derived_counit (K : CochainComplex (IsoAlgebra F) ℤ) :
    (freeWeilDerivedAdjunction F).counit.app (DerivedCategory.Q.obj K) =
      (freeWeilLocalizationComponent F K).hom ≫
        DerivedCategory.Q.map
          (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K) := by
  let : CatCommSq ((Free.functor F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (Free.functor F).mapDerivedCategory :=
    ⟨(Free.functor F).mapDerivedCategoryFactors.symm⟩
  let : CatCommSq ((forget F).mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q (forget F).mapDerivedCategory :=
    ⟨(forget F).mapDerivedCategoryFactors.symm⟩
  have h := Adjunction.Localization.η_app
    ((Free.adjunction F).mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q (HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ))
    (Free.functor F).mapDerivedCategory (forget F).mapDerivedCategory K
  have hU : (CatCommSq.iso ((forget F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (forget F).mapDerivedCategory).inv.app K =
      (forget F).mapDerivedCategoryFactors.hom.app K := rfl
  have hI : (CatCommSq.iso ((Free.functor F).mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q (Free.functor F).mapDerivedCategory).inv.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) =
      (Free.functor F).mapDerivedCategoryFactors.hom.app
        (((forget F).mapHomologicalComplex (.up ℤ)).obj K) := rfl
  rw [hU, hI] at h
  have hc : ((Free.adjunction F).mapHomologicalComplex (.up ℤ)).counit.app K =
      ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K := by
    ext n
    exact (Free.adjunction F).mapHomologicalComplex_counit_app_f (.up ℤ) K n
  rw [hc] at h
  simpa only [freeWeilDerivedAdjunction, Adjunction.mapExactDerivedCategory,
    Adjunction.localization, Adjunction.mkOfUnitCounit, freeWeilLocalizationComponent,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h

private def freeWeilConnecting : DerivedCategory.Q ⟶
    ((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
      shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ) where
  app K := DerivedCategory.triangleOfSESδ (freeWeil_complex_shortExact F K)
  naturality K L f := by
    let S (K : CochainComplex (IsoAlgebra F) ℤ) :=
      ShortComplex.mk (((freeWeilDifference F).mapHomologicalComplex (.up ℤ)).app K)
        (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K)
        (freeWeil_complex_zero F K)
    let t : S K ⟶ S L :=
      { τ₁ := ((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).map f
        τ₂ := ((forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)).map f
        τ₃ := f
        comm₁₂ := ((freeWeilDifference F).mapHomologicalComplex (.up ℤ)).naturality f
        comm₂₃ := ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).naturality f }
    exact (DerivedCategory.triangleOfSESδ_naturality
      (freeWeil_complex_shortExact F K) (freeWeil_complex_shortExact F L) t).symm

/-- The natural cyclic short exact sequence and its ordinary derived triangle, with
the actual counit and the explicit difference on all integer summands.
Source: ordinary-derived expansion, steps 5--9
(blueprint: lem-sf-free-derived-weil-resolution).

Proof: step 5 iterates the chain structure in both directions. Its maps are
`Free.hom K (𝟙 _) n`; they are invertible, and their zero member is the identity.
The two recursion identities identify the augmentation with the free counit and
show naturality. Step 6 defines s on summand n by the coherent map P^(n-1)(φ)
into summand n-1. Its intertwining equation follows on applying P to each summand.
Thus d = 1-s is a natural morphism of fixed pairs and the counit kills d.
For step 7, identify each translate with the underlying object by its iterate.
Then d e_n = e_n-e_(n-1) and ε e_n = 1. Define h e_n by the finite sum of e_j
for 1 ≤ j ≤ n if n>0, zero if n=0, and the negative finite sum for n<j≤0 if n<0.
Telescoping gives dh=1-e_0 ε and hd=1, hence d is the kernel of the split epimorphism
ε in every underlying degree. Step 8 uses
`lem-weil-pbc-jointly-reflect-short-exact` for the singleton exact conservative
forgetful functor to reflect short exactness to the fixed-pair heart.
Step 9 applies `lem-weil-pbc-complex-ses-triangle`. The short exact sequence is
natural on complexes, so its connecting map is natural. All its functors invert
quasi-isomorphisms. Localization descends its natural transformations, including
the counit, giving a distinguished triangle natural for every derived morphism. -/
theorem exists_freeDerivedWeilResolution :
    ∃ (θ : ∀ (M : IsoAlgebra F) (n : ℤ), Free.obj F M.carrier n ≅ M.carrier)
      (d : forget F ⋙ Free.functor F ⟶ forget F ⋙ Free.functor F),
      (∀ (M : IsoAlgebra F) (n : ℤ), (θ M n).hom = Free.hom M (𝟙 M.carrier) n) ∧
      (∀ (M : IsoAlgebra F) (n : ℤ),
        Sigma.ι (Free.obj F M.carrier) n ≫ (forget F).map (d.app M) =
          Sigma.ι (Free.obj F M.carrier) n -
            (θ M n ≪≫ (θ M (n - 1)).symm).hom ≫
              Sigma.ι (Free.obj F M.carrier) (n - 1)) ∧
      (∀ (M : IsoAlgebra F) (n : ℤ),
        Sigma.ι (Free.obj F M.carrier) n ≫
          (forget F).map ((Free.adjunction F).counit.app M) = (θ M n).hom) ∧
      ∃ (hzero : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
        (d.mapHomologicalComplex (.up ℤ)).app K ≫
          ((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K = 0)
        (hshort : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
          (ShortComplex.mk ((d.mapHomologicalComplex (.up ℤ)).app K)
            (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K)
            (hzero K)).ShortExact),
        ∃ (dD : (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory ⟶
            (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory)
          (δ : 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶
            ((forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory) ⋙
              shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ)),
          (∀ K : CochainComplex (IsoAlgebra F) ℤ,
            dD.app (DerivedCategory.Q.obj K) ≫ (freeWeilLocalizationComponent F K).hom =
              (freeWeilLocalizationComponent F K).hom ≫
                DerivedCategory.Q.map ((d.mapHomologicalComplex (.up ℤ)).app K)) ∧
          (∀ K : CochainComplex (IsoAlgebra F) ℤ,
            (freeWeilDerivedAdjunction F).counit.app (DerivedCategory.Q.obj K) =
              (freeWeilLocalizationComponent F K).hom ≫
                (DerivedCategory.Q (C := IsoAlgebra F)).map
                  (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app K)) ∧
          (∀ K : CochainComplex (IsoAlgebra F) ℤ,
            δ.app (DerivedCategory.Q.obj K) ≫
                (shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ)).map
                  (freeWeilLocalizationComponent F K).hom =
              DerivedCategory.triangleOfSESδ (hshort K)) ∧
          ∀ K : DerivedCategory (IsoAlgebra F),
            Triangle.mk (dD.app K)
              ((freeWeilDerivedAdjunction F).counit.app K) (δ.app K) ∈
                  distTriang (DerivedCategory (IsoAlgebra F)) := by
  let A := (forget F).mapDerivedCategory ⋙ (Free.functor F).mapDerivedCategory
  let B := (forget F ⋙ Free.functor F).mapHomologicalComplex (.up ℤ)
  let Q := DerivedCategory.Q (C := IsoAlgebra F)
  let W := HomologicalComplex.quasiIso (IsoAlgebra F) (.up ℤ)
  let e : Q ⋙ A ≅ B ⋙ Q := freeWeilComparison F
  let H := Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory (IsoAlgebra F))
  let dC := (freeWeilDifference F).mapHomologicalComplex (.up ℤ)
  let τ : Q ⋙ A ⟶ Q ⋙ A := e.hom ≫ Functor.whiskerRight dC Q ≫ e.inv
  let dD : A ⟶ A := H.preimage τ
  have hdD (K : CochainComplex (IsoAlgebra F) ℤ) :
      dD.app (Q.obj K) ≫ (e.app K).hom =
        (e.app K).hom ≫ Q.map (dC.app K) := by
    have h := congr_app (H.map_preimage τ) K
    change dD.app (Q.obj K) = (e.app K).hom ≫ Q.map (dC.app K) ≫ (e.app K).inv at h
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id]
    congr 1
    exact Category.comp_id _
  let s := shiftFunctor (DerivedCategory (IsoAlgebra F)) (1 : ℤ)
  let τδ : Q ⋙ 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶ Q ⋙ (A ⋙ s) :=
    freeWeilConnecting F ≫ Functor.whiskerRight e.inv s
  let δ : 𝟭 (DerivedCategory (IsoAlgebra F)) ⟶ A ⋙ s := H.preimage τδ
  have hδ (K : CochainComplex (IsoAlgebra F) ℤ) :
      δ.app (Q.obj K) ≫ s.map (e.app K).hom =
        DerivedCategory.triangleOfSESδ (freeWeil_complex_shortExact F K) := by
    have h := congr_app (H.map_preimage τδ) K
    change δ.app (Q.obj K) =
      DerivedCategory.triangleOfSESδ (freeWeil_complex_shortExact F K) ≫
        s.map (e.app K).inv at h
    rw [h, Category.assoc, ← s.map_comp, Iso.inv_hom_id, s.map_id, Category.comp_id]
  refine ⟨freeWeilTheta F, freeWeilDifference F, fun M n ↦ rfl, ?_,
    freeWeil_counit F, freeWeil_complex_zero F, freeWeil_complex_shortExact F,
    dD, δ, hdD, freeWeil_derived_counit F, hδ, ?_⟩
  · intro M n
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
      freeWeilDifference_summand F M n
  · intro K
    let T (K : DerivedCategory (IsoAlgebra F)) :=
      Triangle.mk (dD.app K) ((freeWeilDerivedAdjunction F).counit.app K) (δ.app K)
    have hT (L : CochainComplex (IsoAlgebra F) ℤ) : T (Q.obj L) ∈ distTriang _ := by
      apply isomorphic_distinguished _
        (DerivedCategory.triangleOfSES_distinguished (freeWeil_complex_shortExact F L))
      refine Triangle.isoMk _ _ (e.app L) (e.app L) (Iso.refl _) ?_ ?_ ?_
      · change dD.app (Q.obj L) ≫ (e.app L).hom =
          (e.app L).hom ≫ Q.map (dC.app L)
        exact hdD L
      · change (freeWeilDerivedAdjunction F).counit.app (Q.obj L) ≫ 𝟙 _ =
          (e.app L).hom ≫ Q.map
            (((Free.adjunction F).counit.mapHomologicalComplex (.up ℤ)).app L)
        rw [Category.comp_id]
        exact freeWeil_derived_counit F L
      · change δ.app (Q.obj L) ≫ s.map (e.app L).hom =
          𝟙 _ ≫ DerivedCategory.triangleOfSESδ (freeWeil_complex_shortExact F L)
        rw [Category.id_comp]
        exact hδ L
    let L := Q.objPreimage K
    let a := Q.objObjPreimageIso K
    apply isomorphic_distinguished _ (hT L)
    refine Triangle.isoMk _ _ (A.mapIso a.symm) (A.mapIso a.symm) a.symm ?_ ?_ ?_
    · exact (dD.naturality a.inv).symm
    · exact ((freeWeilDerivedAdjunction F).counit.naturality a.inv).symm
    · exact (δ.naturality a.inv).symm

/-- Underlying membership implies membership in the localizing hull of free images.
Source: ordinary-derived expansion, step 10
(blueprint: lem-sf-free-derived-weil-resolution).

Proof: apply `exists_freeDerivedWeilResolution`. If U K lies in L, then I U K lies
in I(L), hence in its localizing closure. Both initial vertices of the distinguished
cyclic triangle are I U K. Closure under distinguished cones and isomorphisms puts
K in that closure (`def-weil-triangulated-subcategory`). No invariance of L under
the autoequivalence, boundedness, or extra hypothesis on K is needed. -/
theorem freeWeil_mem_localizingClosure
    (L : ObjectProperty (DerivedCategory C)) [L.IsLocalizing]
    (K : DerivedCategory (IsoAlgebra F))
    (hK : L ((forget F).mapDerivedCategory.obj K)) :
    ObjectProperty.localizingClosure (fun N : DerivedCategory (IsoAlgebra F) ↦
      ∃ M : DerivedCategory C, L M ∧
        Nonempty ((Free.functor F).mapDerivedCategory.obj M ≅ N)) K := by
  obtain ⟨θ, d, _, _, _, hzero, hshort, dD, δ, _, _, _, hdist⟩ :=
    exists_freeDerivedWeilResolution F
  let P : ObjectProperty (DerivedCategory (IsoAlgebra F)) := fun N ↦
    ∃ M : DerivedCategory C, L M ∧
      Nonempty ((Free.functor F).mapDerivedCategory.obj M ≅ N)
  have h : P.localizingClosure
      ((Free.functor F).mapDerivedCategory.obj ((forget F).mapDerivedCategory.obj K)) :=
    P.le_localizingClosure _ ⟨_, hK, ⟨Iso.refl _⟩⟩
  exact P.localizingClosure.ext_of_isTriangulatedClosed₃ _ (hdist K) h h


end CategoryTheory.Endofunctor.IsoAlgebra
