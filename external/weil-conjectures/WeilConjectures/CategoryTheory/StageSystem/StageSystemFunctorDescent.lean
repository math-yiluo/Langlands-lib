/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import WeilConjectures.CategoryTheory.CommonStage.CoherentPairFunctorDescent
public import WeilConjectures.CategoryTheory.StageSystem.Basic
import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Coherent functor descent on the existing StageSystem quotient

Source: sketch32 common-stage calculus, lines 1291--1338 and 1419--1426;
sketch42 pseudocone and pair universal properties
(blueprint: lem-sbc-coherent-pair-functor-descent).

## Main definitions

* `StageSystem.pairFunctorCoherent`: the specified tower equation.
* `StageSystem.coefficientPairFunctor`: descent on the actual upstream quotient.

The imported original interface retains additive structures, compatible natural
transformations and outer Karoubi extension. This interface transports its functor
construction to the independently existing `StageSystem.PairCategory` carrier.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v u' v'

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  (S : StageSystem C) (T : StageSystem D)
  (φ : ∀ i, C i ⥤ D i)
  (b : ∀ {i j} (h : i ≤ j), φ i ⋙ T.T h ≅ S.T h ⋙ φ j)

/-- The coherent tower equation, with the source and target associators retained.
Source: sketch32, common-stage comparisons, lines 1291--1338 and 1419--1426
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def pairFunctorCoherent : Prop :=
  ∀ {i j k} (h : i ≤ j) (h' : j ≤ k) (X : C i),
    (T.T h').map ((b h).hom.app X) ≫ (b h').hom.app ((S.T h).obj X) ≫
        (φ k).map ((S.assoc h h').hom.app X) =
      (T.assoc h h').hom.app ((φ i).obj X) ≫ (b (h.trans h')).hom.app X

/-- The descended object keeps the coefficient stage.
Source: sketch32, lines 1419--1426
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
def coefficientPairFunctorObject (P : S.PairCategory) : T.PairCategory :=
  match P with
  | ⟨i, X⟩ => ⟨i, (φ i).obj X⟩

omit [IsDirectedOrder I] in
/-- Matching the pair first preserves the original stagewise object formula.
Source: sketch32, lines 1419--1426
(blueprint: lem-sbc-coherent-pair-functor-descent).
Proof: destruct the pair; both sides are the same pair constructor. -/
theorem coefficientPairFunctorObject_eq (P : S.PairCategory) :
    coefficientPairFunctorObject S T φ P = ⟨P.stage, (φ P.stage).obj P.obj⟩ := by
  cases P
  rfl

/-- The functor on the upstream quotient is uniquely prescribed by all representatives.
Source: sketch32, lines 1291--1338 and 1419--1426; sketch42 pair universal property
(blueprint: lem-sbc-coherent-pair-functor-descent).
Proof: conjugate a representative by b at its source and inverse b at its target.
The tower equation identifies this formula after every further transport: expand
transport, use naturality of b, and cancel inverse comparisons. Thus eventual
equality of representatives is preserved and the map descends to the actual
quotient. At a common stage composition cancels the middle comparisons and uses
functoriality of φ; the identity representative cancels b with its inverse.
These are exactly the upstream quotient's category operations. Every arrow has
a representative, so the object and representative formulas give uniqueness.
No extra unit assumption is needed on this quotient: identity representatives
already have both endpoints extended along the same repeated-stage transition. -/
theorem coefficientPairFunctor_exists (hb : pairFunctorCoherent S T φ b) :
    ∃! F : S.PairCategory ⥤ T.PairCategory,
      (∀ P, F.obj P = coefficientPairFunctorObject S T φ P) ∧
      (∀ {P Q : S.PairCategory} (M : I) (hP : P.stage ≤ M) (hQ : Q.stage ≤ M)
        (f : P.toStage hP ⟶ Q.toStage hQ),
        HEq (F.map (PairCategory.mkHom M hP hQ f))
          (PairCategory.mkHom
            (X := coefficientPairFunctorObject S T φ P)
            (Y := coefficientPairFunctorObject S T φ Q) M hP hQ
            ((b hP).hom.app P.obj ≫ (φ M).map f ≫ (b hQ).inv.app Q.obj))) := by
  let G : S.Morphism T := ⟨φ, b, hb⟩
  refine ⟨G.functor, ⟨fun P ↦ by cases P; rfl, fun _ _ _ _ ↦ HEq.rfl⟩, ?_⟩
  intro F hF
  apply Functor.hext hF.1
  intro P Q f
  induction f using PairCategory.hom_induction with
  | h M hP hQ f => exact hF.2 M hP hQ f

/-- Coherent-pair descent, with uniquely determined object and arrow formulas.
Source: sketch32, lines 1291--1338 and 1419--1426
(blueprint: lem-sbc-coherent-pair-functor-descent). -/
@[irreducible] def coefficientPairFunctor (hb : pairFunctorCoherent S T φ b) :=
  ((coefficientPairFunctor_exists S T φ b hb).exists.choose).copyObj
    (coefficientPairFunctorObject S T φ)
    (fun P ↦ eqToIso ((coefficientPairFunctor_exists S T φ b hb).exists.choose_spec.1 P))

end CategoryTheory.StageSystem
