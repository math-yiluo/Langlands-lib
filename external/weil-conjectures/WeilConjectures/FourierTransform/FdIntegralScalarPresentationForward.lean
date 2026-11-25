/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdIntegralScalarLiftProperty
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCoherence
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCocycle
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AmbientAssociator
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.OrdinaryCocycle
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.AbstractAssembly
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.RepresentativeFormula
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.UnitAssembly
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.LiftAssembly
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.GoodRepresentative
import all WeilConjectures.FourierTransform.FdIntegralOrdinaryScalarModel.FdIntegralOrdinaryScalarModel
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.LiftFormula
import all WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.UnitFormula
import WeilConjectures.FourierTransform.FdIntegralScalarPresentationForward.DerivedCompositionFactors

/-! # Forward coherence of the integral scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

private theorem eqToIso_trans_heq {C D : Type*} [Category C] [Category D] {F F' G : C ⥤ D}
    (h : F = F') (a : F' ≅ G) : (eqToIso h ≪≫ a) ≍ a := by
  subst h
  simp

private theorem trans_eqToIso_heq {C D : Type*} [Category C] [Category D] {F G G' : C ⥤ D}
    (a : F ≅ G) (h : G = G') : (a ≪≫ eqToIso h) ≍ a := by
  subst h
  simp

private theorem ordinaryComparison_heq (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (κ κ' : E →ₐ[ℚ_[l]] M) (h : κ = κ') :
    sfIntegralOrdinaryComparison l E M κ T ≍ sfIntegralOrdinaryComparison l E M κ' T := by
  subst h
  rfl

/-- Forward scalar associativity and the multiplication/completeness unit for
an integral comparison characterized by its good-representative completion lift.
Source: trace-definition coefficient comparison, integral steps 4--6
(blueprint: lem-fd-integral-scalar-presentation-forward).

Proof: Choose the normalized ScalarCompletionAssociatorData. On a good K-flat
representative the lift equation identifies b with the actual chi map after
ordinary coefficient-presentation transport: cancel the scalar-representative
comparison and the coefficient-transport factor in that equation. The generator
normalization of ordinary identifies its derived transport with
fdIntegralOrdinaryPresentation. Naturality along resolving isomorphisms extends
this identification to every integral object. Apply the forward equation of
fdIntegralInverseScalarCocycle to these same chi maps. Naturality of chi for the
second extension at the first chi map replaces chi at the ordinary extension
followed by completed extension of chi with ordinary extension of chi followed
by chi at the completed extension. Under coefficient transport,
fdIntegralOrdinaryBalancing identifies ordinary balancing with pbcAmbientScalarComp.
The specified framework associator is normalized by the same completion maps,
as recorded by integralPullbackComparisonRealization. Insert the stage
integral_identity casts; direct versus composite field embeddings are identified
by coefficientInclusion_laws. Map the requested equation through the faithful
PBC integral inclusion. These identifications turn it into that forward equation,
so faithfulness proves it. For an equal-field inclusion use
fdIntegralInverseScalarUnits: chi is ordinary multiplication followed by inverse
completeness. Ordinary generator transport preserves multiplication. Cancel the
completion unit to obtain b followed by I of integralUnit equal to
pbcIntegralScalarUnit. This argument includes zero objects and repeated fields;
no strict-inclusion assumption is used.
-/
theorem fdIntegralScalarPresentationForward
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hlift : fdIntegralScalarLiftProperty l Ω T stage ordinary b) :
    (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (C l Ω T k).map ((b h).hom.app K) ≫
        (b k).hom.app ((U l Ω T h).obj K) ≫
        (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) =
      (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) ≫ (b (h.trans k)).hom.app K) ∧
    (∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).hom.app K ≫
        (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K) =
      (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app
        ((I l Ω T stage E).obj K)) := by
  refine ⟨fun {E L M} h k K ↦ ?_, fun E K ↦ ?_⟩
  · exact FdIntegralScalarForward.assoc_assembly_full
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T)
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T)
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω M) T)
      _ _ _ (I l Ω T stage E) (I l Ω T stage L) (I l Ω T stage M)
      (integralDetailedTransport T l _) (integralDetailedTransport T l _)
      (integralDetailedTransport T l _)
      (eqToIso (stage E).integral_identity) (eqToIso (stage L).integral_identity)
      (eqToIso (stage M).integral_identity)
      _ _ _ _ _ _ (pbcAmbientScalarExtension l Ω T h) (pbcAmbientScalarExtension l Ω T k)
      (pbcAmbientScalarExtension l Ω T (h.trans k)) _ _ _
      (b h) (b k) (b (h.trans k)) (integralAssoc l Ω T h k)
      (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k)
      (pbcAmbientScalarAssociator l Ω T h k)
      (pbcIntegralScalarAssociator_hom l Ω T dT.out iT.out h k)
      _ _ _ (FdIntegralScalarForward.ODcomp l Ω T h k)
      (FdIntegralScalarForward.eD l Ω T h (ordinary h))
      (FdIntegralScalarForward.eD l Ω T k (ordinary k))
      (FdIntegralScalarForward.eD l Ω T (h.trans k) (ordinary (h.trans k)))
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω h) T)
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω k) T)
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω (h.trans k)) T)
      (lift_formula l Ω T stage ordinary b hlift h) (lift_formula l Ω T stage ordinary b hlift k)
      (lift_formula l Ω T stage ordinary b hlift (h.trans k))
      _ _ (congrArg (fun κ ↦ integralScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) κ T) (FdIntegralScalarForward.inclusion_comp l Ω h k))
      (sfIntegralScalarComp l _ _ (pbcFiniteFieldInclusion l Ω h) T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) _ (pbcFiniteFieldInclusion l Ω k))
      (by unfold integralAssoc; exact trans_eqToIso_heq _ _)
      _ (congrArg (fun κ ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω M) κ T) (FdIntegralScalarForward.inclusion_comp l Ω h k))
      (integralOrdinaryDerivedScalarComp l _ _ (pbcFiniteFieldInclusion l Ω h) T _
        (pbcFiniteFieldInclusion l Ω k))
      (by unfold FdIntegralScalarForward.ODcomp; exact trans_eqToIso_heq _ _)
      (sfIntegralOrdinaryComparison l _ _
        ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T)
      (ordinaryComparison_heq l T _ _ _ _ (FdIntegralScalarForward.inclusion_comp l Ω h k).symm)
      (fun K ↦ (sfIntegralScalarComp_existsUnique l _ _ (pbcFiniteFieldInclusion l Ω h) T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) _
        (pbcFiniteFieldInclusion l Ω k)).exists.choose_spec K)
      DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ (fdCoefficientTransportFactors l _ T) (fdCoefficientTransportFactors l _ T)
      (fdCoefficientTransportFactors l _ T)
      (FdIntegralScalarForward.pbcCounitNT _) (FdIntegralScalarForward.pbcCounitNT _)
      (FdIntegralScalarForward.pbcCounitNT _)
      (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T h (ordinary h))
      (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T k (ordinary k))
      (FdIntegralOrdinaryScalarModel.ordinaryTransportComplex l Ω T (h.trans k)
        (ordinary (h.trans k))) _ _
      (FdIntegralScalarForward.eD_heh l Ω T h (ordinary h))
      (FdIntegralScalarForward.eD_heh l Ω T k (ordinary k))
      (FdIntegralScalarForward.eD_heh l Ω T (h.trans k) (ordinary (h.trans k)))
      -- The categories, instances and functors are given in the form fixed by this goal, so the
      -- kernel never compares two instance paths (see `derived_comp_factors`).
      (fun P ↦ by
        refine FdIntegralScalarForward.derived_comp_factors
          (C₁ := scalarReductionSource l (pbcFiniteField.{u} l Ω E) T)
          (C₂ := scalarReductionSource l (pbcFiniteField.{u} l Ω L) T)
          (C₃ := scalarReductionSource l (pbcFiniteField.{u} l Ω M) T)
          (aC₁ := @SheafOfModules.instAbelian _ _ _ _
            (@GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat _ _ _ T)
            (sfAbBijective T))
          (aC₂ := @SheafOfModules.instAbelian _ _ _ _
            (@GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat _ _ _ T)
            (sfAbBijective T))
          (aC₃ := @SheafOfModules.instAbelian _ _ _ _
            (@GrothendieckTopology.hasSheafify_proEtTopology AddCommGrpCat _ _ _ T)
            (sfAbBijective T))
          (dC₁ := scalarReductionSourceDerived l (pbcFiniteField.{u} l Ω E) T)
          (dC₂ := scalarReductionSourceDerived l (pbcFiniteField.{u} l Ω L) T)
          (dC₃ := scalarReductionSourceDerived l (pbcFiniteField.{u} l Ω M) T)
          (oh := (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h) T).mapHomologicalComplex (.up ℤ))
          (ok := (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω L) (pbcFiniteField.{u} l Ω M)
            (pbcFiniteFieldInclusion l Ω k) T).mapHomologicalComplex (.up ℤ))
          (ohk := (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω (h.trans k)) T
            ).mapHomologicalComplex (.up ℤ))
          (Oh := integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T)
          (Ok := integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω L)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω k) T)
          (Ohk := integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω (h.trans k)) T)
          (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h) T)
          (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω L) (pbcFiniteField.{u} l Ω M)
            (pbcFiniteFieldInclusion l Ω k) T)
          (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
            ((pbcFiniteFieldInclusion l Ω k).comp (pbcFiniteFieldInclusion l Ω h)) T)
          (integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω M)
            (pbcFiniteFieldInclusion l Ω (h.trans k)) T)
          ?_ ?_ ?_ ?_ ?_ ?_ _ _ _ ?_ ?_ ?_
          (integralOrdinaryScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
            (pbcFiniteFieldInclusion l Ω h) T (pbcFiniteField.{u} l Ω M)
            (pbcFiniteFieldInclusion l Ω k))
          (congrArg (fun ι ↦ integralOrdinaryScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) ι T) (FdIntegralScalarForward.inclusion_comp l Ω h k))
          _ (FdIntegralScalarForward.Ocomp_eq l Ω T h k) _ ?_
          (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω M) ι T) (FdIntegralScalarForward.inclusion_comp l Ω h k))
          _ (heq_of_eq (FdIntegralScalarForward.ODcomp_eq l Ω T h k)) P
        all_goals rfl)
      (FdIntegralScalarForward.pbcDerivedComp_counit _ _ _
        (pbcCompletedScalarMap_comp l Ω T h k))
      (FdIntegralScalarForward.chain_cocycle l Ω T h k (ordinary h) (ordinary k)
        (ordinary (h.trans k)))
      (fun P ↦ FdIntegralScalarForward.counit_isIso l Ω T (h.trans k) _) K
  · exact FdIntegralScalarForward.unit_assembly_of_spec
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T) _ (I l Ω T stage E)
      (integralDetailedTransport T l _) (eqToIso (stage E).integral_identity)
      _ _ (pbcAmbientScalarExtension l Ω T (le_refl E)) _ (b (le_refl E))
      (integralUnit l Ω T E) (pbcIntegralScalarUnit l Ω T dT.out iT.out E)
      (pbcAmbientScalarUnit l Ω T E) (pbcIntegralScalarUnit_hom l Ω T dT.out iT.out E) _
      (FdIntegralScalarForward.eD l Ω T (le_refl E) (ordinary (le_refl E)))
      (sfIntegralOrdinaryComparison l _ _ (pbcFiniteFieldInclusion l Ω (le_refl E)) T)
      (lift_formula l Ω T stage ordinary b hlift (le_refl E))
      _ _ (congrArg (fun ι ↦ integralScalarExtension l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω E) ι T) (FdIntegralScalarForward.inclusion_id l Ω E).symm)
      (sfIntegralScalarUnit l _ T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)))
      (by unfold integralUnit; exact eqToIso_trans_heq _ _)
      _ (congrArg (fun ι ↦ integralOrdinaryDerivedScalar l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω E) ι T) (FdIntegralScalarForward.inclusion_id l Ω E).symm)
      (sfIntegralOrdinaryComparison l _ _ (AlgHom.id ℚ_[l] (pbcFiniteField.{u} l Ω E)) T)
      (ordinaryComparison_heq l T _ _ _ _ (FdIntegralScalarForward.inclusion_id l Ω E))
      (fun Y ↦ (integralOrdinaryDerivedScalarUnit l (pbcFiniteField.{u} l Ω E) T).hom.app Y)
      (fun K ↦ (sfIntegralScalarUnit_existsUnique l _ T 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).exists.choose_spec K)
      (eD_unit l Ω T E (ordinary (le_refl E))) K

end WeilConjectures
