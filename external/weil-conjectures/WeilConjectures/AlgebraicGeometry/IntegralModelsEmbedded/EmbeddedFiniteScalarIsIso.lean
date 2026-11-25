/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.EmbeddedFiniteCoefficientRealization
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing

/-! # Finite constant scalar isomorphism

## References

* Stacks Tag 093J and the finite-discrete condensed-ring comparison
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsEmbedded

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  IntegralModelsStacks.smallMap

attribute [-instance] integralModel_coefficientMonObj in
/-- The specified finite constant-function scalar map is an isomorphism. -/
theorem embeddedFiniteScalarIsIso
    (X : Scheme.{u}) (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso (finiteScalarMap X A) := by
  let J := coherentTopology Profinite.{u}
  let f := Profinite.constantToContinuousRing.{u} A
  have : Presheaf.IsLocallyInjective J f :=
    ⟨fun a b h ↦ Presheaf.equalizerSieve_mem J
      (Profinite.constantToContinuousAb.{u} A) a b h⟩
  have : Presheaf.IsLocallySurjective J f :=
    ⟨fun a ↦ Presheaf.imageSieve_mem J (Profinite.constantToContinuousAb.{u} A) a⟩
  have hf : J.W f := J.W_of_isLocallyBijective f
  have : IsIso ((presheafToSheaf J RingCat.{u + 1}).map f) := (J.W_iff f).mp hf
  have hc : IsIso (constantToContinuous.{u} A) := by
    unfold constantToContinuous
    rw [Adjunction.homEquiv_counit]
    change IsIso (_ ≫ (presheafToSheaf J RingCat.{u + 1}).map f ≫ _)
    infer_instance
  unfold finiteScalarMap finiteScalarPointMap
  infer_instance

end AlgebraicGeometry.ProEtale.IntegralModelsEmbedded
