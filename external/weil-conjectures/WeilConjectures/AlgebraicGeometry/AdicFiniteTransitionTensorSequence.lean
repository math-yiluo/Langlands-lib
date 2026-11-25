/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import WeilConjectures.AlgebraicGeometry.AdicFiniteTransitionTensorSequenceCore

/-! # The tensor sequence underlying one adic reduction transition

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1), and
sites-cohomology.tex, Tag 08FZ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- One normalized quotient transition has a short exact cochain presentation whose
kernel homology is a residue tensor test. There is no Tor bound, product or completeness
hypothesis in this assertion.

Source: Stacks Project, proetale.tex, Tag 09C2, proof of (1), using the coefficient
sequence and K-flat computations of Tags 06YS and 06YY.
(auxiliary; not a blueprint node).

Proof: Choose a K-flat representative L of N with flat terms. Apply ordinary scalar
extension to get L_n = L tensor_A A/J^(n+1). The residue complex P = L_0 is K-flat
by change of rings and represents the residue reduction. Let M be the constant
A/J-module associated to J^(n+1)/J^(n+2); its action is well-defined since
J times J^(n+1) is contained in J^(n+2). Sheafify the short exact coefficient
sequence 0 -> J^(n+1)/J^(n+2) -> A/J^(n+2) -> A/J^(n+1) -> 0.
Tensor it degreewise with L. Flatness of each term, defined by exactness of sheaf
tensor, gives a short exact sequence S of complexes of A-module sheaves.
The K-flat computation counits and the chosen representative isomorphism give
Q(S.X2) = U_(n+1) and Q(S.X3) = U_n. On pure tensors the second arrow is quotient
on coefficients. The defining insertion and balancing equations of adicFiniteUnit,
adicFiniteRho and adicFiniteDresComp identify its localized arrow with exactly
adicFiniteTransition, giving the displayed square. Balancing identifies S.X1
with the restriction of P tensor_(A/J) M[0]. Exact restriction commutes with
homology, giving the final isomorphisms in every degree. All comparisons use
cochain counits, so no coherence or transition is supplied as additional data.
For J=0 the kernel vanishes and the coefficient quotient is the identity; for
J=A both quotients and M vanish. The argument also applies to the empty scheme. -/
theorem adicFiniteTransition_tensor_sequence
    (X : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A) (n : ℕ) :
    ∃ P : Cx (constant (coefficientProEtaleModelTopology.{u, v} X) (adicFiniteCoeff J 0)),
      P.IsKFlatIndependentCoefficients ∧
      Nonempty ((Q _).obj P ≅ adicFiniteReduction.{u, v} X J N 0) ∧
      ∃ (M : Mod (constant (coefficientProEtaleModelTopology.{u, v} X)
          (adicFiniteCoeff J 0)))
        (S : ShortComplex (Cx (constant (coefficientProEtaleModelTopology.{u, v} X) A))),
        S.ShortExact ∧
        ∃ (e₂ : (Q _).obj S.X₂ ≅ adicFiniteUnderlying.{u, v} X J N (n + 1))
          (e₃ : (Q _).obj S.X₃ ≅ adicFiniteUnderlying.{u, v} X J N n),
          (Q _).map S.g ≫ e₃.hom = e₂.hom ≫ adicFiniteTransition.{u, v} X J N n ∧
          ∀ q : ℤ, Nonempty (S.X₁.homology q ≅
            (res (quotient (coefficientProEtaleModelTopology.{u, v} X) A J 0)).obj
              (coefficientModelTensorTest _ P M q)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let R := constant T (adicFiniteCoeff J 0)
  obtain ⟨P, hP, _, eP⟩ := exists_coefficientModelFlatKFlatRepresentative
    (R := R) (adicFiniteReduction.{u, v} X J N 0)
  refine ⟨P, hP, eP, ?_⟩
  exact adicFiniteTransition_tensor_sequence_core X A J N n P hP eP

end AlgebraicGeometry.Scheme
