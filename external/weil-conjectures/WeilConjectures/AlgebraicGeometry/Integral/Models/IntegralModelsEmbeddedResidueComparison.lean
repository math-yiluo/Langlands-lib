/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteFieldCohomologyCriterion
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFirstReductionComparison
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import Mathlib.Topology.Algebra.Ring.Compact

/-! # Residue comparison for embedded coefficients

## References

* Stacks Project Tags 03ET and 06YQ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallDerivedObject IntegralModelsStacks.smallModules
  IntegralModelsStacks.smallMap

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- Constructible cohomology and finite Tor amplitude of the first constant reduction
are equivalent to bounded constructible etale origin of the first completed reduction.
-/
theorem integralModelsEmbeddedResidueComparison
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [IsNoetherian X] :
    ∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      IntegralModelsEmbedded.residueConstructible ℓ E π X
        ((IntegralModelsEmbedded.restriction ℓ E X).obj K) ↔
      integralModelResidueEtaleOrigin X ℓ E π K := by
  intro K
  let : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianHasSheafify.{u + 1, u, u + 1} _
  let : (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    CategoryTheory.siteAbelianWEqualsLocallyBijective.{u + 1, u, u + 1} _
  let A := completedResidue ℓ E π 0
  have : Finite A := by
    dsimp only [A, completedResidue]
    rw [hπ]
    infer_instance
  have : DiscreteTopology A := by
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    have : CompactSpace (PadicAlgCl.integers ℓ E.1) :=
      PadicAlgCl.compactSpace_integers ℓ E.1
    apply QuotientAddGroup.discreteTopology
    change IsOpen (X := PadicAlgCl.integers ℓ E.1) ↑((Ideal.span {π}) ^ (0 + 1))
    rw [hπ]
    exact IsLocalRing.isOpen_maximalIdeal_pow _ _
  have : ((Ideal.span {π}) ^ (0 + 1)).IsMaximal := by
    simpa only [Nat.zero_add, pow_one, hπ] using
      (inferInstance : (IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)).IsMaximal)
  let : Field A := Ideal.Quotient.field _
  let B := (Mod.extendScalars (IntegralModelsEmbedded.residueMap ℓ E π X)).leftDerivedFunctor.obj
    ((IntegralModelsEmbedded.restriction ℓ E X).obj K)
  let C := (integralModelIntrinsicRealization X A).rightDerivedFunctor.obj
    ((Mod.extendScalars (integralModelReductionMap X ℓ E π 1).hom).leftDerivedFunctor.obj K)
  let P := (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
      (ULift.{u + 1, u} (ULift.{u, 0} A)) X) ⋙
    finiteCoefficientIntrinsicDerivedComparison X (ULift.{u, 0} A)).essImage
  have hcomp := IntegralModelsEmbedded.firstReductionComparison ℓ E π hπ X K
  unfold IntegralModelsEmbedded.constantResidueRealization
    IntegralModelsEmbedded.continuousResidueRealization
    IntegralModelsEmbedded.constantFirstReduction
    IntegralModelsEmbedded.continuousFirstReduction at hcomp
  obtain ⟨e⟩ := hcomp
  have hc : IntegralModelsEmbedded.residueConstructible ℓ E π X
      ((IntegralModelsEmbedded.restriction ℓ E X).obj K) ↔
      P ((IntegralModelsEmbedded.finiteRealization X A).obj B) :=
    (IntegralModelsEmbedded.finiteFieldCohomologyCriterion X A B).trans
      ((Scheme.finiteRing_constructibleDerived_origin X (ULift.{u, 0} A)).2.2.1 _).symm
  change _ ↔ ∃ (_ : Finite A) (_ : DiscreteTopology A), P C
  constructor
  · intro h
    exact ⟨inferInstance, inferInstance, P.prop_of_iso e (hc.mp h)⟩
  · rintro ⟨_, _, h⟩
    exact hc.mpr (P.prop_of_iso e.symm h)

end AlgebraicGeometry.ProEtale
