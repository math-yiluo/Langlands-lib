/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationExists
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationUnique

/-! # The finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedVariables false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

/-- There is a uniquely normalized strict augmentation before taking any products.
The second clause prescribes zero on every summand of nonzero exterior degree.
There is no K-flatness, pro-zero, inverse-limit, or Roos assertion here.

Source: Stacks Project, Tags 091N and 099M, the degree-zero augmentation in the
proof of lemma-naive-completion.
(blueprint: lem-weil-pbc-completed-koszul-tensor-quotient-augmentation).

Proof: augment the exterior Koszul complex on the powers a_i^(n+1) to
A/I^(n+1), using the quotient map in degree zero and zero in negative degrees.
The differential into degree zero is killed since each a_i^(n+1) belongs to
I^(n+1). Its diagonal successor is the identity in degree zero, so these maps
commute with the quotient successors. Apply constant module sheafification,
then extension to the completed ring. The finite constant quotient is the
recorded finite coefficient module: its locally constant functions description
agrees with constant sheafification because A/I^(n+1) is finite. Tensor with P
and collapse the single degree-zero factor. This gives the displayed natural
transformation, with its actual tower target. The exterior unit sends one to
one, giving the first equation, and the other summands map to zero. These
formulas determine the map: the degree-zero Koszul unit is an isomorphism of
modules, and the total tensor summand injections jointly detect maps. They
also prove naturality in P and strict compatibility with all successors.
For r=0, I=0 and this is the ordinary scalar unit isomorphism. The same quotient
formulas apply to I=A, the zero ring, the empty scheme and the zero complex. -/
theorem completedKoszulTensorQuotientAugmentation
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃! β : completedKoszulTensorTower T d r a ⟶
        (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ),
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
        completedAdicKoszulTensorUnit T d r a P n ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
            completedQuotientTensorUnit T d P n) ∧
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        completedKoszulTensorSummand T d r a P n p q ≫
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
              (β.app P)).app (op n)).f (p + q) = 0) := by
  obtain ⟨β, hβ⟩ := completedKoszulTensorQuotientAugmentation_exists T d r a ha
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  exact (completedKoszulTensorQuotientAugmentation_unique T d r a β γ hβ hγ).symm

end AlgebraicGeometry.Scheme
