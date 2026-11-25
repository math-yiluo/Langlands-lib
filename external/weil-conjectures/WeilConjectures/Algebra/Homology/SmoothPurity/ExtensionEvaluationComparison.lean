/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Evaluating a normalized derived extension

Source: Stacks 0FND, 09T5 and 06YT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a av b bv c cv d dv da db dc dd
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace SheafOfModules
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{da} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{db} B]
  {C : Type c} [Category.{cv} C] [Abelian C] [HasDerivedCategory.{dc} C]
  {D : Type d} [Category.{dv} D] [Abelian D] [HasDerivedCategory.{dd} D]
  {R₁ : B ⥤ A} [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  {R₂ : D ⥤ C} [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  {p₁ : CochainComplex A ℤ → Prop} {p₂ : CochainComplex C ℤ → Prop}
  (d₁ : SystemDerivedLeftExtension R₁ p₁) (d₂ : SystemDerivedLeftExtension R₂ p₂)
  (G : A ⥤ C) [G.Additive]
  (H : B ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (GD : DerivedCategory A ⥤ DerivedCategory C)
  (γ : (DerivedCategory.Q (C := A)) ⋙ GD ≅
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (τD : R₁.mapDerivedCategory ⋙ GD ⟶
    H.mapDerivedCategory ⋙ R₂.mapDerivedCategory)

/-- The evaluation comparison before proving invertibility is the actual derived mate.
Source: Stacks 0FND (blueprint: lem-pur-extension-evaluation-comparison). -/
def derivedExtensionMate :
    GD ⋙ d₂.derived ⟶ d₁.derived ⋙ H.mapDerivedCategory :=
  ((mateEquiv d₁.adjunction d₂.adjunction).symm (TwoSquare.mk _ _ _ _ τD))

/-- A normalized derived mate has the prescribed cochain comparison.
Source: Stacks 0FND and 09T5
(blueprint: lem-pur-extension-evaluation-comparison).
Proof: the ordinary unit-transpose identity holds degreewise on complexes. Apply
the categorical derived-mate comparison to the two termwise adjunctions, their
normalized derived pairs, and the canonical exact-functor factorization isomorphisms. -/
theorem derivedExtensionMate_rep
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hτ : ∀ K : CochainComplex B ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          R₂.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
          γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (ι : G ⋙ d₂.ordinary ≅ d₁.ordinary ⋙ H)
    (hι : ∀ P, d₂.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      G.map (d₁.ordinaryAdj.unit.app P) ≫ τ.app (d₁.ordinary.obj P))
    (P : CochainComplex A ℤ) :
    (derivedExtensionMate d₁ d₂ H GD τD).app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategory.map (d₁.comparison.app P) ≫
        H.mapDerivedCategoryFactors.hom.app
          ((d₁.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
      d₂.derived.map (γ.hom.app P) ≫
        d₂.comparison.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ι (.up ℤ)).hom.app P) := by
  have hc (P : CochainComplex A ℤ) :
      (d₂.ordinaryAdj.mapHomologicalComplex (.up ℤ)).homEquiv
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((H.mapHomologicalComplex (.up ℤ)).obj
          ((d₁.ordinary.mapHomologicalComplex (.up ℤ)).obj P))
        ((NatIso.mapHomologicalComplex ι (.up ℤ)).hom.app P) =
      (G.mapHomologicalComplex (.up ℤ)).map
        ((d₁.ordinaryAdj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (τ.mapHomologicalComplex (.up ℤ)).app
          ((d₁.ordinary.mapHomologicalComplex (.up ℤ)).obj P) := by
    apply HomologicalComplex.hom_ext
    intro i
    exact hι (P.X i)
  exact derivedMate_comparison
    (d₁.ordinaryAdj.mapHomologicalComplex (.up ℤ))
    (d₂.ordinaryAdj.mapHomologicalComplex (.up ℤ)) d₁.adjunction d₂.adjunction
    d₁.comparison d₂.comparison R₁.mapDerivedCategoryFactors R₂.mapDerivedCategoryFactors
    γ H.mapDerivedCategoryFactors d₁.transpose d₂.transpose
    (TwoSquare.mk _ _ _ _ (τ.mapHomologicalComplex (.up ℤ)))
    (TwoSquare.mk _ _ _ _ τD) hτ (NatIso.mapHomologicalComplex ι (.up ℤ)).hom hc P

variable
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hτ : ∀ K : CochainComplex B ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          R₂.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
          γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (ι : G ⋙ d₂.ordinary ≅ d₁.ordinary ⋙ H)
    (hι : ∀ P, d₂.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      G.map (d₁.ordinaryAdj.unit.app P) ≫ τ.app (d₁.ordinary.obj P))

include τ hτ ι hι in
/-- The evaluation mate is invertible when the two normalized models compute on a
common resolving class. Source: Stacks 06YT and 09T5
(blueprint: lem-pur-extension-evaluation-comparison).
Proof: on a resolving complex its representative formula has invertible factors,
so cancellation makes the mate invertible. Every complex admits a quasi-isomorphic
resolving representative, and every derived object is isomorphic to a localized
complex. Naturality transports invertibility along these two isomorphisms. -/
theorem derivedExtensionMate_isIso
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), p₁ P ∧ QuasiIso f)
    (hp : ∀ P : CochainComplex A ℤ, p₁ P →
      p₂ ((G.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (derivedExtensionMate d₁ d₂ H GD τD) := by
  let α := derivedExtensionMate d₁ d₂ H GD τD
  have hi (P : CochainComplex A ℤ) (hP : p₁ P) :
      IsIso (α.app (DerivedCategory.Q.obj P)) := by
    have := d₁.computes P hP
    have := d₂.computes _ (hp P hP)
    have h := derivedExtensionMate_rep d₁ d₂ G H GD γ τD τ hτ ι hι P
    have : IsIso (α.app (DerivedCategory.Q.obj P) ≫
        H.mapDerivedCategory.map (d₁.comparison.app P) ≫
        H.mapDerivedCategoryFactors.hom.app
          ((d₁.ordinary.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [show α.app _ ≫ _ ≫ _ = _ from h]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (H.mapDerivedCategory.map (d₁.comparison.app P) ≫
        H.mapDerivedCategoryFactors.hom.app
          ((d₁.ordinary.mapHomologicalComplex (.up ℤ)).obj P))
  have (X : DerivedCategory A) : IsIso (α.app X) := by
    let K := DerivedCategory.Q.objPreimage X
    obtain ⟨P, f, hP, hf⟩ := res K
    have := hf
    let e : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    exact (NatTrans.isIso_app_iff_of_iso α e).1 (hi P hP)
  exact NatIso.isIso_of_isIso_app α

/-- The evaluated derived extension is identified with the level derived tensor by
the inverse of its normalized mate. Source: Stacks 0FND and 06YT
(blueprint: lem-pur-extension-evaluation-comparison). -/
def derivedExtensionEvaluationIso
    (γ : (DerivedCategory.Q (C := A)) ⋙ GD ≅
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (τD : R₁.mapDerivedCategory ⋙ GD ⟶
      H.mapDerivedCategory ⋙ R₂.mapDerivedCategory)
    (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (hτ : ∀ K : CochainComplex B ℤ,
      τD.app (DerivedCategory.Q.obj K) ≫
          R₂.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
          R₂.mapDerivedCategoryFactors.hom.app
            ((H.mapHomologicalComplex (.up ℤ)).obj K) =
        GD.map (R₁.mapDerivedCategoryFactors.hom.app K) ≫
          γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.mapHomologicalComplex (.up ℤ)).app K))
    (ι : G ⋙ d₂.ordinary ≅ d₁.ordinary ⋙ H)
    (hι : ∀ P, d₂.ordinaryAdj.homEquiv _ _ (ι.hom.app P) =
      G.map (d₁.ordinaryAdj.unit.app P) ≫ τ.app (d₁.ordinary.obj P))
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), p₁ P ∧ QuasiIso f)
    (hp : ∀ P : CochainComplex A ℤ, p₁ P →
      p₂ ((G.mapHomologicalComplex (.up ℤ)).obj P)) :
    d₁.derived ⋙ H.mapDerivedCategory ≅ GD ⋙ d₂.derived := by
  have := derivedExtensionMate_isIso d₁ d₂ G H GD γ τD τ hτ ι hι res hp
  exact (asIso (derivedExtensionMate d₁ d₂ H GD τD)).symm

/-- The evaluated derived comparison intertwines the actual adjunction transposes.
Source: Stacks 0FND (blueprint: lem-pur-extension-evaluation-comparison).
Proof: the inverse comparison is the mate of the right square by construction.
Apply the general mate-transpose identity. -/
theorem derivedExtensionEvaluationIso_transpose
    (res : ∀ K : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), p₁ P ∧ QuasiIso f)
    (hp : ∀ P : CochainComplex A ℤ, p₁ P →
      p₂ ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (P : DerivedCategory A) (M : DerivedCategory B) (f : d₁.derived.obj P ⟶ M) :
    d₂.adjunction.homEquiv (GD.obj P) (H.mapDerivedCategory.obj M)
      ((derivedExtensionEvaluationIso d₁ d₂ G H GD γ τD τ hτ ι hι res hp).inv.app P ≫
        H.mapDerivedCategory.map f) =
    GD.map (d₁.adjunction.homEquiv P M f) ≫ τD.app M :=
  adjunctionMate_transpose d₁.adjunction d₂.adjunction (TwoSquare.mk _ _ _ _ τD) P M f

end SheafOfModules
