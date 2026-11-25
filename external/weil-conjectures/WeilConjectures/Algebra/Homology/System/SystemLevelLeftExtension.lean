/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
import WeilConjectures.Algebra.Homology.System.SystemCoproducts
import WeilConjectures.Algebra.Homology.System.SystemGrothendieck
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition
import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedEvaluation
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedComposition
import WeilConjectures.Algebra.Homology.System.SystemDerivedTransitionUnit
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedTransition
import WeilConjectures.Algebra.Homology.System.SystemSelectedDerivedCompositionEvaluation

/-! # Derived left extensions of strict semilinear systems

Source: Zheng, Construction 4.1; Stacks 06XN, 0FND and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

-- Unused-variable linting needlessly normalizes the entire extension schema here.
set_option linter.unusedVariables false in
/-- Derived left extensions of arbitrary strict semilinear ring-sheaf systems.
The nonnegative index n denotes the node's positive index n+1. All structure fields
are conclusions: no flatness of the coefficient maps, normalization, or boundedness
is an assumption. The ordinary and derived universal properties determine each left
extension, with its actual unit and counit; normalized Hom formulas specify all
coefficient comparisons and the selected transition, including repeated next indices.

Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
the adic-stage paragraph of theorem-f-shriek-finite-coefficients in the main-20261015
blueprint, before taking inverse limits; Stacks Tags 03DA, 03DB, 06YS, 06YT, 06XN,
0FND and 09T5 (blueprint: lem-pur-system-level-left-extension).

Proof, following the ordinary-derived route of the node, with explicit normalized mates:

1. Construct normalized scalar models from the existing independent-coefficient derived
change-of-rings model. Transfer the normalized homotopy Hom formula to all cochain complexes.
Scalar adjoint uniqueness gives ordinary and derived tensor units and associators, normalized
on local pure tensors and universal cochain comparisons.

2. A strict system is exactly a module sheaf on the ringed sequence site: its covers are
vertical covers at a fixed index and its ring at (n,U) is B_n(U). Both constructions and their
inverse comparisons are identity maps on sections. The small-site module Grothendieck theorem
then gives the Grothendieck property for the actual strict abelian category. Colimits and
exactness are componentwise. Termwise coproducts descend to arbitrary small derived coproducts
by the existing Grothendieck derived coproduct theorem, and exact evaluation preserves them.
Exact evaluation commutes with homology; componentwise zero detection gives joint detection
of isomorphisms and of a common lower or upper cohomological bound.

3. The ordinary singleton extension has level B_m tensor over B_n with P below n and zero
above. Its tensor-adjoint transitions compose by the strict composition law. Transposing a
map P to M_n and then each actual transition gives its inverse Hom map; tensor generators
verify the two inverse identities and additivity.

4. For subsequence r put a=t_r(m), the first index with m≤r(a). The ordinary extension has
level B_m tensor over B_r(a) with N_a. Its transition uses the two canonical scalar associators
and the scalar adjunct of the actual transition of N. On local tensors it sends c tensor x
to the image of c tensor the transition of x. Tensor generators prove the identity,
composition, naturality and adjunction equations, including when next indices coincide.
At r(i), t_r(r(i))=i; the tensor unit therefore supplies the actual adjunction unit.

5. Vertical evaluation on the ringed sequence site is a ringed-topos inverse image with
identity structural ring map. Resolve a system complex once on that site by a K-flat complex
with flat terms. The ringed-topos K-flat pullback theorem makes all evaluated components
flat-term independently K-flat simultaneously. The ordinary singleton and selected extensions
preserve quasi-isomorphisms between their respective resolving objects, by levelwise
independent K-flat change of rings. The existing resolving-class left-derived theorem and
normalized derived adjunction theorem give their universal pointwise exact derived extensions,
with ordinary functors and adjunctions retained definitionally and the prescribed cochain
transpose formula.

6. Localize the actual strict transition and use the exact-functor compositor. Its cochain
formula is the original transition surrounded by the exact evaluation and restriction
factorizations. Localization of the strict identity and composition laws gives the actual
derived identity and composition equations. The derived tensor unit is the transpose of
the identity transition by its adjoint-uniqueness normalization.

7. Below-level singleton and selected evaluation comparisons are inverse mates of the actual
right evaluation-transition squares. On the resolving classes their representative formulas
are invertible, so naturality makes them isomorphisms on every derived object. The general
mate-transpose formula gives both normalized evaluation Hom equations. Singleton vanishing
above n follows by evaluating its resolved tensor-or-zero representative. The right selected
evaluation cocone respects transitions, by localization of the strict composition law.
Transpose this cocone composition through the scalar adjunctions: canonical tensor
associators become restriction compositors. This proves the selected transition formula
on all derived objects, including equal successive selected indices.

8. Successive derived subsequence restrictions have the canonical exact-functor compositor.
Transfer the composite left adjunction along it and take left-adjoint uniqueness against
the composite-selection extension. Its Hom normalization is exactly composition_mate.
Selected evaluation respects restriction composition and actual transitions. Consequently
its right squares paste with the canonical scalar restriction compositor; transposing
identifies the evaluated extension compositor with the canonical scalar associator.
The identity t_(r∘s)(m)=t_s(t_r(m)) supplies precisely systemSelectedTensor_trans and its
specified eqToHom. Thus extensionComposition_eval holds for this actual composition mate.
All these computations take place in the ordinary unbounded derived categories; no
identification with diagrams in level derived categories or flat coefficient maps is used.
-/
theorem systemLevelLeftExtensionTheory : Nonempty (SystemLevelLeftExtensionTheory (J := J)) := by
  classical
  let S : SystemScalarAssignment (J := J) := fun φ ↦ Classical.choice (nonempty_systemScalarModel φ)
  let T := systemTensorCoherence S
  let Sn := fun B n ↦ systemSingleDerivedExtension B n S T
  let Sr := fun B r ↦ systemSelectedDerivedExtension B r S T
  refine ⟨{ scalar := S
            tensor := T
            grothendieck := strictRingSystem_isGrothendieckAbelian
            coproducts := fun B ↦ inferInstance
            derivedCoproducts := strictRingSystem_derivedCoproducts
            levelDerivedCoproducts := systemLevel_derivedCoproducts
            evaluationCoproducts := fun B n I ↦ by
              have (m : ℕ) : HasColimitsOfShape (Discrete I) (systemLevel B m) := by
                have : HasColimitsOfShape (Discrete I) (PresheafOfModules.{w}
                    (derivedChangeRingIndependentCoefficients J (B.obj (op m))).obj) :=
                  PresheafOfModules.hasColimitsOfShape _ _
                exact
                  instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
              exact systemEvaluation_colimitsOfShape B (Discrete I) n
            derivedEvaluationCoproducts := derivedSystemEvaluation_coproducts
            cohomology := systemDerivedCohomology
            detectsIso := systemDerivedEvaluation_isIso_iff
            detectsBounds := systemDerivedEvaluation_bounds_iff
            single := Sn
            singleBelow := fun B {m n} h ↦ systemSingleBelow S T B n h
            singleAbove := fun B m n h P ↦ systemSingleLevelAbove S B n P h
            singleTranspose := fun B {m n} h ↦ systemSingleTranspose S T B n h
            singleDerivedBelow := fun B {m n} h ↦ systemSingleDerivedBelow B h S T
            singleDerivedAbove := fun B m n ↦ systemSingleDerivedAbove S T B m n
            transition := fun B {m n} h ↦ systemDerivedTransition B h
            transition_rep := fun B {m n} h ↦ systemDerivedTransition_rep B h
            transition_identity := fun B n ↦ systemDerivedTransition_tensorUnit B S n
            singleDerivedTranspose := fun B {m n} h ↦ systemSingleDerivedTranspose S T B h
            selected := Sr
            selectedEvaluation := systemDerivedSubsequenceEvaluation
            selectedEvaluation_rep := systemDerivedSubsequenceEvaluation_rep
            selectedBelow := fun B r m ↦ systemSelectedBelow S T B r m
            selectedTranspose := fun B r m ↦ systemSelectedTranspose S T B r m
            selectedDerivedBelow := fun B r m ↦ systemSelectedDerivedBelow B r m S T
            selectedDerivedTranspose := fun B r m ↦ systemSelectedDerivedTranspose S T B r m
            selectedTransition := systemSelectedDerivedTransition S
            restrictionComposition := systemDerivedSubsequenceComposition
            restrictionComposition_rep := systemDerivedSubsequenceComposition_rep
            extensionComposition := systemSelectedDerivedComposition S T
            composition_mate := systemSelectedDerivedComposition_mate S T
            extensionComposition_eval := systemSelectedDerivedComposition_eval S }⟩

end SheafOfModules
