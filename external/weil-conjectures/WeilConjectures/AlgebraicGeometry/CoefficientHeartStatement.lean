/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Constructible coefficient sheaves

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3) (blueprint: lemma-constructible-sheaves).

The coefficient ring is the condensed ring pulled back from the point.  The statement
uses the existing constructible full subcategory, the existing lisse predicate, and the
canonical locally closed extension from the dependency nodes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Constructible coefficient sheaves form an exact essentially small abelian heart and
admit finite filtrations by canonical locally closed extensions of lisse sheaves.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3), and
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/`
`sk-lem-coefficient-heart.proof.md`,
steps (1)--(3)
(blueprint: lemma-constructible-sheaves).

The closure conjuncts render clause (1)'s closure under kernels, cokernels and extensions.
The `Abelian` witness and finite-limit/finite-colimit preservation render its abelian and
exact-inclusion conclusions.  The `EssentiallySmall` conjunct is clause (2).  The final
conjunct is clause (3): its filtration terms are subobjects, successive quotients are
cokernels of the inclusions, and each quotient is the canonical `a_!` of a lisse module.

Proof plan, following the node's eight steps:
1. Finite type over k makes X Noetherian. Finite scalar presentations are finite free;
   choose common adapted strata and use exact restriction to check closure on strata.
2. For extensions, trivialize the ends and locally lift the quotient basis. The resulting
   local splitting identifies the middle term with a finite free direct sum.
3. Over E use the lattice atlas on connected affine etale neighborhoods. The qcqs
   finitely presented Hom/filtered-colimit calculation clears one common denominator.
4. Recover the lattices as limits of their finite reductions. The connected pro-etale
   tower identifies the map with its completed-fibre matrix, whose kernel and cokernel
   become finite free after inverting the uniformizer and choosing linear algebra bases.
5. Over Qbar_l descend the two lisse objects and their map to a finite E. Flat scalar
   extension preserves kernels, and the left adjoint preserves cokernels. Return to strata.
6. Zero has rank zero and extensions give finite sums. Closure under ambient kernels and
   cokernels gives the abelian full subcategory and its exact inclusion.
7. In the fixed universe encode finite stratifications and finite-rank descent/gluing
   data by a set of representatives, giving essential smallness.
8. Refine to ordered open prefixes. Their open-extension counit images form a filtration
   from zero to F, with quotients the canonical locally closed extensions of lisse
   restrictions. Repeated terms, rank zero and empty schemes are allowed.
-/
theorem coefficientHeartStatement (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      EssentiallySmall.{u + 1} (ConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      @CoefficientHeartFiltrationAssertions (coefficientHeartRingObj Λ) _ _ X
        { toIsLocallyNoetherian :=
            LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
          toCompactSpace :=
            QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  sorry

end AlgebraicGeometry.ProEtale
