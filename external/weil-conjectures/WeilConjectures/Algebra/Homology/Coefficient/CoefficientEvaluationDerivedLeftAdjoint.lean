/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedExtension
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedAbove
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedBelow
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedTransition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientTensorDerivedUnit

/-!
# Derived extension from a coefficient level
Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03D7, 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint).
Indices in this module are Zheng's nonnegative indices: `n` denotes the paper node's
positive level `n + 1`. No normalization or cartesianness is imposed on a system.
The auxiliary declarations construct the actual strict systems and their evaluations;
the final package records the constructions, universal properties and all coherence laws.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  {O : Type w} [CommRing O] {ell : O} [EssentiallySmall.{w} C]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

-- The original signature retains regularity, although this construction does not need it.
set_option linter.unusedVariables false in
/-- Derived extension from a single varying-coefficient level, with strict models,
coherent truncation maps, and their specified adjunction mates.
Source: Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, printed p. 21;
Stacks Project, Tags 03D7, 06XN and 09T5
(blueprint: lem-pur-coefficient-evaluation-derived-left-adjoint).
Proof plan, following the seven steps of the node:
1. The strict systems are modules over the inverse coefficient-ring sheaf on the
projective-system topos. Kernels, cokernels and cohomology are componentwise, so a chain
map is a quasi-isomorphism exactly when all evaluated chain maps are quasi-isomorphisms
(lem-pur-system-level-left-extension). No normalization is imposed.
2. Define E_n by scalar extension below n and zero above n. From h:F→M_n, at q≤n use
the tensor-adjoint of the iterated transition composed with h, and above n use the unique
map from zero. Balanced tensor relations and the transition equations show these are
system maps. Conversely their component at n determines all components, giving the
natural inverse Hom bijections (lem-weil-pbc-ringed-topoi-module-adjunction). Units send
x to 1 tensor x and counits are the displayed transition-adjoints.
3. E_n is additive and acts termwise on differentials and maps. It preserves homotopies,
shifts and mapping cones. Resolve by flat-term K-flat complexes (lem-pc-kflat-resolution).
Termwise scalar extension preserves quasi-isomorphisms between them
(lem-pur-derived-change-of-rings); the evaluated zero complexes above n do too. Apply
lem-pur-left-derived-from-kflat-class to obtain the universal left derived pair and
its invertible comparison on this class. Evaluation gives the canonical derived tensor
below n and zero above n, with the comparison equation recorded in derivedBelow_rep.
4. Exact evaluation and scalar restriction have termwise derived functors
(lem-weil-pbc-exact-functor-derived-functor). Apply lem-pc-derived-adjoint-functors.
Normalize its bijection using lem-pc-pre-derived-adjoint-functors-general and
lem-weil-pbc-termwise-adjunction-homotopy: on a strict chain map its transpose is the
ordinary transpose followed by exact derived evaluation. Essential constancy and the
pointwise Kan bridge identify this with the universal comparison from step 3
(lem-pur-quasi-isos-saturated-triangulated,
lem-pur-resolving-class-essential-constancy,
lem-pur-left-derived-defined-pointwise-kan-bridge). The same argument normalizes the
derived scalar adjunction, including the unit x→1 tensor x and counit a tensor x→a h(x).
5. Define sigma by transposing the derived unit followed by the system transition,
first under scalar extension/restriction and then under LE_n/e_n. On a flat-term K-flat
representative, scalar extension is again flat-term K-flat
(lem-weil-pbc-ringed-pullback-preserves-kflat). The two transposes give the strict map
whose q-component is the balanced tensor associator for q≤n and zero for q>n. These
maps commute with differentials and transitions, including at q=n,n+1. The universal
comparison equation sigma_rep identifies the derived map with that actual chain map.
6. The unit tensor isomorphism inserts or removes 1. The associator sends
(c tensor (b tensor x)) to (c times the image of b) tensor x. These formulas are fixed
by tensorUnit_normalized and tensorAssoc_normalized. Thus the identity truncation map
is the identity. For three indices, the successive strict maps and the direct map
send every tensor generator to the same product of reduced coefficients. Above the
smallest index both sources are zero. The same computation with four coefficients
proves associator coherence. Pass through the universal comparisons to obtain sigma_id
and sigma_comp, with the canonical derived tensor unit and associator specified on
these representatives. No flatness of quotient-ring maps is used.
7. For f:LE_m N→M and its adjunct h, transpose f sigma twice. Naturality of the derived
system transition gives tau_M h. Its scalar transpose is C(h) followed by the transpose
of tau_M. This is exactly mate, for all derived morphisms, including fractions.
-/
theorem coefficientEvaluationDerivedLeftAdjoint
    (hregular : ∀ x : O, ell * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({ell} : Set O)) O] :
    Nonempty (CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell)) := by
  classical
  obtain ⟨ordinary⟩ := coefficientOrdinaryEvaluationExtension (J := J) (O := O) (ell := ell)
  let := ordinary.extensionAdditive
  let scalar {m n : ℕ} (h : n ≤ m) :=
    (coefficientScalarDerivedAdjunction (J := J) (O := O) (ell := ell) h).some
  obtain ⟨core⟩ := coefficientEvaluationDerivedCore ordinary
  choose transition ht using (fun (m n : ℕ) (h : n ≤ m) ↦
    coefficientEvaluationDerivedTransition ordinary (fun {_ _} h ↦ scalar h) core h)
  choose below hb using (fun (n q : ℕ) (h : q ≤ n) ↦
    coefficientEvaluationDerivedBelow ordinary (fun {_ _} h ↦ scalar h) core h)
  obtain ⟨strict⟩ := coefficientEvaluationOrdinaryCoherence ordinary
  choose unit hu using (fun n ↦ coefficientTensorDerivedUnit
    (fun {_ _} h ↦ scalar h) n (strict.tensorUnit n))
  have unit_rep (n : ℕ) P : (unit n).hom.app (DerivedCategory.Q.obj P) =
      (scalar (Nat.le_refl n)).counit.app P ≫
        DerivedCategory.Q.map (strict.tensorUnitComplex n P).hom := by
    rw [hu n P]
    congr 1
    apply congrArg
    apply HomologicalComplex.hom_f_injective
    funext i
    change (strict.tensorUnit n).hom.app (P.X i) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (strict.tensorUnitComplex_f n P i).symm
  obtain ⟨derived⟩ := coefficientEvaluationDerivedCoherence ordinary
    (fun {_ _} h ↦ scalar h) core (fun {_ _} h ↦ transition _ _ h) strict unit unit_rep
    (fun h K ↦ ht _ _ h K)
  exact ⟨{
    strictTransition := ordinary.strictTransition
    transitionsNormalized := ordinary.transitionsNormalized
    scalar := fun h ↦ scalar h
    extension := ordinary.extension
    extensionAdditive := ordinary.extensionAdditive
    adj := ordinary.adj
    below := ordinary.below
    above := ordinary.above
    hom_formula := ordinary.hom_formula
    evaluation := core.evaluation
    evaluationFactors := core.evaluationFactors
    derivedExtension := core.derivedExtension
    counit := core.counit
    isDerived := core.isDerived
    computes := fun n P hP _ ↦ core.computes n P hP
    derivedAdj := core.derivedAdj
    transpose := core.transpose
    derivedBelow := fun h ↦ below _ _ h
    derivedAbove := coefficientEvaluationDerivedAbove ordinary core
    transition := fun h ↦ transition _ _ h
    transition_rep := fun h K ↦ ht _ _ h K
    sigma := fun h ↦ coefficientEvaluationSigma (fun {_ _} h ↦ scalar h) core
      (fun {_ _} h ↦ transition _ _ h) h
    mate := fun h ↦ CategoryTheory.Adjunction.compositeMate_homEquiv
      (core.derivedAdj _) (core.derivedAdj _) (scalar h).derivedAdj (transition _ _ h)
    tensorUnit := strict.tensorUnit
    tensorUnit_normalized := strict.tensorUnit_normalized
    tensorAssoc := strict.tensorAssoc
    tensorAssoc_normalized := strict.tensorAssoc_normalized
    strictSigma := strict.strictSigma
    strictSigma_below := strict.strictSigma_below
    strictSigma_above := strict.strictSigma_above
    strictSigmaComplex := strict.strictSigmaComplex
    strictSigmaComplex_f := strict.strictSigmaComplex_f
    sigma_rep := derived.sigma_rep
    tensorUnitComplex := strict.tensorUnitComplex
    tensorUnitComplex_f := strict.tensorUnitComplex_f
    tensorAssocComplex := strict.tensorAssocComplex
    tensorAssocComplex_f := strict.tensorAssocComplex_f
    derivedUnit := unit
    derivedUnit_rep := fun n P _ ↦ unit_rep n P
    derivedAssoc := derived.derivedAssoc
    derivedAssoc_rep := derived.derivedAssoc_rep
    sigma_id := derived.sigma_id
    sigma_comp := derived.sigma_comp
    belowComplex := fun h P ↦
      (NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)).app P
    belowComplex_f := fun _ _ _ ↦ rfl
    derivedBelow_rep := fun h P ↦ hb _ _ h P }⟩
end SheafOfModules
