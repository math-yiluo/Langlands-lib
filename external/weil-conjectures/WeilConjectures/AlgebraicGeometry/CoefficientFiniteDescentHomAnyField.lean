/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf
public import
  WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite descent of coefficient morphisms over any allowed base field

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-descent-to-a-finite-coefficient-field/
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md, clauses (1)--(3),
with the Q30 any-field scope repair of 2026-11-02
(blueprint: lemma-descent-finite-coefficient-field--1).

The old positive-characteristic theorem and the canonical maps it defines remain
available. This statement includes characteristic zero and uses those same maps,
coefficient rings, ordinary derived categories, and bounded constructible objects.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

/-- The natural derived scalar adjunctions, uniformly bounded-below coefficient
complex colimit, and finite descent of every shifted morphism, over any field
whose characteristic differs from the coefficient prime.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-reduction-finite-coefficients/sec-descent-to-a-finite-coefficient-field/
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-hom.md (1)--(3) and its
.proof.md, with the node's Q30 scope repair of 2026-11-02
(blueprint: lemma-descent-finite-coefficient-field--1).

Proof, following the five current DAG steps:
1. A field is Noetherian, including in characteristic zero. A finite type scheme
   over it is Noetherian by lem-weil-pbc-finite-type-over-noetherian. Finite
   subextensions form a set directed by composita
   (def-weil-finite-subextension-directed-set).
2. Apply lem-weil-pbc-condensed-flat-coefficient-calculus to X. Exact extension
   is left adjoint to exact restriction on the ordinary derived categories, and
   the recorded derived extension is termwise tensor. Evaluate the adjunctions
   on C and D_F[r], also over the algebraic closure. The tensor multiplication,
   unit and shift comparisons identify their transitions with coefficient
   inclusions. Adjunction naturality gives the two displayed transition identities.
3. By lemma-comparison-completed-coefficients the algebraic-closure coefficient ring is the
   filtered colimit of finite fields. The tail above E is cofinal by composita.
   Tensor preserves this colimit by the coefficient calculus. Apply this termwise
   to every bounded representative K of D to obtain the specified colimiting
   coefficientComplexCocone. A zero term below a stays zero after scalar extension
   and restriction, so every stage has the same lower bound a.
4. Apply lemma-continuity-ext-out-constructible-complex--1 (1) in its any-field setting to C,
   this coefficient diagram, and r. Its complexes have the common lower bound
   just established; its first-argument hypothesis holds for every bounded
   constructible object over E. This gives the restricted-target Hom colimit
   bijection.
5. Identify that comparison using the natural adjunctions of step 2 and the
   actual colimit of step 3. It is the specified scalar-extension map on Hom.
   Elements of a filtered colimit have finite-stage representatives and two
   representatives agree precisely when they agree at a common later stage.
   The final two conjuncts express exactly its surjectivity and injectivity.
-/
theorem coefficient_finite_descent_hom_of_char_ne
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (_hchar : ringChar k ≠ ℓ)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (C D : BoundedConstructible (padicSubfieldRingObj X ℓ E)) (r : ℤ) :
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      Function.Bijective (finiteCoefficientDerivedHomEquiv X ℓ h C.obj
        (((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧))) ∧
    Function.Bijective (finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj
      (((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧)) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : F ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedHomEquiv X ℓ (h.trans j) C.obj _
          (coefficientDescentHomTransition X ℓ h j C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionTransition X ℓ h j D.obj r) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
      finiteCoefficientDerivedAlgClHomEquiv X ℓ E C.obj _
          (coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f) =
        finiteCoefficientDerivedHomEquiv X ℓ h C.obj _ f ≫
          coefficientDescentRestrictionToAlgCl X ℓ h D.obj r) ∧
    (∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ℤ)
      (_e : DerivedCategory.Q.obj K ≅ D.obj) (a b : ℤ)
      (_hK : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)),
      IsFiltered (AsSmall.{u + 1} (Under E)) ∧
        Nonempty (IsColimit (coefficientComplexCocone X ℓ K (coefficientDescentFields ℓ E)
          (fun i ↦ leOfHom (ULift.down i).hom) (fun i ↦ leOfHom (ULift.down i).hom))) ∧
        ∀ (i : AsSmall.{u + 1} (Under E)) (n : ℤ), n < a →
          IsZero (((coefficientComplexDiagram X ℓ K (coefficientDescentFields ℓ E)
            (fun j ↦ leOfHom (ULift.down j).hom)
            (fun j ↦ leOfHom (ULift.down j).hom)).obj i).X n)) ∧
    (∀ f : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
        ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj D.obj)⟦r⟧,
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
        (g : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧),
        coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r g = f) ∧
    (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (j : E ≤ G)
      (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ h).obj D.obj)⟦r⟧)
      (g : (derivedExtendScalarsSubfield X ℓ j).obj C.obj ⟶
        ((derivedExtendScalarsSubfield X ℓ j).obj D.obj)⟦r⟧),
      coefficientDescentHomToAlgCl X ℓ h C.obj D.obj r f =
        coefficientDescentHomToAlgCl X ℓ j C.obj D.obj r g →
      ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (hF : F ≤ H) (hG : G ≤ H),
        coefficientDescentHomTransition X ℓ h hF C.obj D.obj r f =
          coefficientDescentHomTransition X ℓ j hG C.obj D.obj r g) := by
  sorry

end AlgebraicGeometry.ProEtale
