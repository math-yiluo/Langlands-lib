/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Square
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # Short exact resolution sequences of squares exact on injectives

Source: Stacks Project, Cohomology, Lemma 01EB, via the short exact sequence of
section complexes; Homology, the long exact sequence of a short exact sequence.
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A square of additive group valued functors whose associated three-term sequence
is short exact on injective objects. These are underived, objectwise conditions.
Source: Stacks, Cohomology, proof of Lemma 01EB
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
structure InjectivelyExactSquare extends Square (C ⥤ AddCommGrpCat.{w}) where
  additive₁ : X₁.Additive := by infer_instance
  additive₂ : X₂.Additive := by infer_instance
  additive₃ : X₃.Additive := by infer_instance
  additive₄ : X₄.Additive := by infer_instance
  injective : ∀ (I : C), Injective I → Function.Injective
    (fun x : X₁.obj I ↦ (f₁₂.app I x, f₁₃.app I x))
  exact : ∀ (I : C), Injective I → Function.Exact
    (fun x : X₁.obj I ↦ (f₁₂.app I x, f₁₃.app I x))
    (fun x : X₂.obj I × X₃.obj I ↦ f₂₄.app I x.1 - f₃₄.app I x.2)
  surjective : ∀ (I : C), Injective I → Function.Surjective
    (fun x : X₂.obj I × X₃.obj I ↦ f₂₄.app I x.1 - f₃₄.app I x.2)

attribute [instance] InjectivelyExactSquare.additive₁ InjectivelyExactSquare.additive₂
  InjectivelyExactSquare.additive₃ InjectivelyExactSquare.additive₄

namespace InjectivelyExactSquare

variable {C}

/-- The explicit pointwise binary product of two group-valued functors.
Source: Mathlib, Grp/Biproducts, binaryProductLimitCone
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
def pairFunctor (F G : C ⥤ AddCommGrpCat.{w}) : C ⥤ AddCommGrpCat.{w} where
  obj I := AddCommGrpCat.of (F.obj I × G.obj I)
  map f := AddCommGrpCat.ofHom ((F.map f).hom.prodMap (G.map f).hom)
  map_id I := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- The explicit product functor is additive coordinatewise.
Source: Mathlib, Functor.Additive and the additive structure on a product of groups
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
instance pairFunctor_additive (F G : C ⥤ AddCommGrpCat.{w}) [F.Additive] [G.Additive] :
    (pairFunctor F G).Additive where
  map_add := by
    intros
    ext x
    apply Prod.ext <;> simp [pairFunctor]

variable (S : InjectivelyExactSquare.{u, v, w} C)

/-- The diagonal into the explicit product functor.
Source: Stacks, Cohomology, proof of Lemma 01EB
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
def diagonal : S.X₁ ⟶ pairFunctor S.X₂ S.X₃ where
  app I := AddCommGrpCat.ofHom ((S.f₁₂.app I).hom.prod (S.f₁₃.app I).hom)
  naturality := by
    intro I J f
    ext x
    apply Prod.ext
    · exact congrArg (fun h ↦ h x) (S.f₁₂.naturality f)
    · exact congrArg (fun h ↦ h x) (S.f₁₃.naturality f)

/-- The difference from the explicit product functor.
Source: Stacks, Cohomology, proof of Lemma 01EB
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
def difference : pairFunctor S.X₂ S.X₃ ⟶ S.X₄ where
  app I := AddCommGrpCat.ofHom
    ((S.f₂₄.app I).hom.comp (AddMonoidHom.fst _ _) -
      (S.f₃₄.app I).hom.comp (AddMonoidHom.snd _ _))
  naturality := by
    intro I J f
    ext x
    change S.f₂₄.app J (S.X₂.map f x.1) - S.f₃₄.app J (S.X₃.map f x.2) =
      S.X₄.map f (S.f₂₄.app I x.1 - S.f₃₄.app I x.2)
    rw [map_sub]
    exact congrArg₂ (fun a b ↦ a - b)
      (congrArg (fun h ↦ h x.1) (S.f₂₄.naturality f))
      (congrArg (fun h ↦ h x.2) (S.f₃₄.naturality f))

/-- The diagonal followed by the difference vanishes by commutativity of the square.
Source: Stacks, Cohomology, proof of Lemma 01EB
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
theorem diagonal_difference : S.diagonal ≫ S.difference = 0 := by
  ext I x
  exact sub_eq_zero.mpr (congrArg (fun h ↦ h.app I x) S.fac)

variable [EnoughInjectives C]

/-- Apply the diagonal and difference to a chosen injective resolution.
Source: Stacks, Cohomology, proof of Lemma 01EB
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
noncomputable def resolutionSequence (F : C) : ShortComplex (CochainComplex AddCommGrpCat.{w} ℕ) :=
  ShortComplex.mk
    ((NatTrans.mapHomologicalComplex S.diagonal (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex)
    ((NatTrans.mapHomologicalComplex S.difference (ComplexShape.up ℕ)).app
      (injectiveResolution F).cocomplex)
    (by
      ext n x
      exact congrArg (fun h ↦ h.app ((injectiveResolution F).cocomplex.X n) x)
        S.diagonal_difference)

/-- The resolution sequence is short exact, because every resolution term is injective.
Source: Stacks, Cohomology, proof of Lemma 01EB; Mathlib,
HomologicalComplex.shortExact_iff_degreewise_shortExact
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact).
Proof: Evaluate in each degree. The maps are exactly the diagonal and the difference
in the three hypotheses on S; all resolution terms are injective. Injectivity makes
the first morphism mono, exactness is kernel=image, and surjectivity makes the second
morphism epi. Degreewise short exactness is short exactness of complexes. -/
theorem resolutionSequence_shortExact (F : C) : (S.resolutionSequence F).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact (ShortComplex.ab_exact_iff_function_exact _).mpr
      (S.exact ((injectiveResolution F).cocomplex.X n) (by infer_instance))
  · exact (AddCommGrpCat.mono_iff_injective _).mpr
      (S.injective ((injectiveResolution F).cocomplex.X n) (by infer_instance))
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (S.surjective ((injectiveResolution F).cocomplex.X n) (by infer_instance))

/-- The connecting homomorphism transported from the chosen resolution to derived objects.
Source: Stacks, Cohomology, Lemma 01EB, and Mathlib,
ShortComplex.ShortExact.δ and InjectiveResolution.isoRightDerivedObj
(blueprint: lem-sc-injectively-exact-square-resolution-short-exact). -/
noncomputable def boundary (F : C) (n : ℕ) :
    (S.X₄.rightDerived n).obj F ⟶ (S.X₁.rightDerived (n + 1)).obj F :=
  ((injectiveResolution F).isoRightDerivedObj S.X₄ n).hom ≫
    (S.resolutionSequence_shortExact F).δ n (n + 1) rfl ≫
      ((injectiveResolution F).isoRightDerivedObj S.X₁ (n + 1)).inv

end InjectivelyExactSquare

end CategoryTheory
