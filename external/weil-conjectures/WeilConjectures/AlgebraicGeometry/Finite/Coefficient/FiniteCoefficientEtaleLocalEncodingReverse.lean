/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceModelTransport
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LocalSite
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantEtaleSections
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Presheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
import all Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
import all WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import all WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import all WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import all WeilConjectures.RingTheory.IndEtaleSmallIndex
import all WeilConjectures.RingTheory.ProEtale.Etale
import all Mathlib.CategoryTheory.Limits.MorphismProperty
import all Mathlib.CategoryTheory.Limits.FinallySmall
import all Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsPullback
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink

/-! # Reverse transport from fixed-scalar pro-etale models to etale finite models

Source: Stacks Project, proetale.tex, Tag 099Y; sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-reverse).

This is the reverse direction of the local-model comparison. It is split from
`finiteCoefficient_etaleLocal_encoding` so that the descent from pro-etale
constant charts to etale charts can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

/-- Apply the coefficient-sized chart theorem, then undo the site equivalences.
Source: Stacks Project, Tag 099Y. -/
private theorem fixed_etale_charts (X : Scheme.{t}) (B : Type (t + 1))
    [CommRing B] [IsNoetherianRing B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{t + 1} B))
    (hF : ProFiniteModels.fixedModels (ProEt.topology X) B F) :
    ∃ (I : Type (t + 1)) (U : I → X.Etale), X.smallEtaleTopology.CoversTop U ∧
      ∀ i, ∃ M : ModuleCat.{t + 1} B, Module.Finite B M ∧ Nonempty
        ((ProEtale.upperStar (ModuleCat.{t + 1} B) (U i).hom).obj F ≅
          (constantSheaf (ProEt.topology (U i).left) (ModuleCat.{t + 1} B)).obj M) := by
  let K := coefficientProEtaleModelTopology.{t, t} X
  let H := ((AsSmall.equiv : X.ProEt ≌ coefficientProEtaleSiteModel.{t, t} X).sheafCongr
    (ProEt.topology X) K (ModuleCat.{t + 1} B)).functor.obj F
  have hs : ProFiniteModels.fixedModels K B H :=
    (ProFiniteModels.fixedModels_asSmall (ProEt.topology X) B F).mp hF
  have hfp : ∀ V : coefficientProEtaleSiteModel.{t, t} X,
      ∃ S : Sieve V, S ∈ K V ∧ ∀ (W : coefficientProEtaleSiteModel.{t, t} X)
        (f : W ⟶ V), S f → ∃ M : ModuleCat.{t + 1} B,
          Module.FinitePresentation B M ∧
            Nonempty (H.over W ≅ (constantSheaf (K.over W) _).obj M) := by
    intro V
    obtain ⟨S, hS, hm⟩ := hs V
    refine ⟨S, hS, fun W f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := hm W f hf
    have := hM
    exact ⟨M, Module.finitePresentation_of_finite B M, he⟩
  obtain ⟨I, U, hU, hm⟩ := coefficientFpLocalSystem_etaleCover.{t, t} X B H hfp
  have hc := comparison_coversTop_reflect.{t, t} X U hU
  let D : smallModelComparisonEtaleSite.{t, t} X ⥤ X.Etale := AsSmall.down
  refine ⟨I, fun i ↦ D.obj (U i), ?_, fun i ↦ ?_⟩
  · intro W
    apply X.smallEtaleTopology.superset_covering _
      ((CoverPreserving.of_isContinuous D _ _).cover_preserve (hc (AsSmall.up.obj W)))
    rintro Z f ⟨Y, a, q, ⟨i, ⟨g⟩⟩, _⟩
    exact ⟨i, ⟨q ≫ D.map g⟩⟩
  · obtain ⟨M, hM, ⟨e⟩⟩ := hm i
    have := hM
    let W := (smallModelComparisonInclusion.{t, t} X).obj (U i)
    have hd : (Over.post (X := W) AsSmall.down).IsDenseSubsite
        (K.over W) ((ProEt.topology X).over (AsSmall.down.obj W)) := by
      refine { functorPushforward_mem_iff := ?_ }
      intro Z S
      rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff]
      rw [Sieve.overEquiv_functorPushforward_post]
      exact AsSmall.down.functorPushforward_mem_iff K (ProEt.topology X)
    let d := (Over.post (X := W) AsSmall.down).asEquivalence.symm
    have : d.inverse.IsDenseSubsite (K.over W)
        ((ProEt.topology X).over (AsSmall.down.obj W)) := by
      change (Over.post (X := W) AsSmall.down).IsDenseSubsite _ _
      exact hd
    let E := d.sheafCongr
      ((ProEt.topology X).over (AsSmall.down.obj W)) (K.over W) (ModuleCat.{t + 1} B)
    let c := (d.constantSheafSheafCongrIso ((ProEt.topology X).over (AsSmall.down.obj W))
        (K.over W) (ModuleCat.{t + 1} B) Over.mkIdTerminal).app M
    let e' : F.over ((toProEt X).obj (D.obj (U i))) ≅
        (constantSheaf ((ProEt.topology X).over ((toProEt X).obj (D.obj (U i)))) _).obj M :=
      E.fullyFaithfulFunctor.preimageIso (e ≪≫ c.symm)
    have hfinite : Module.Finite B M := inferInstance
    exact ⟨M, hfinite,
      ⟨(fixedModelSchemeIso F ((toProEt X).obj (D.obj (U i))) M).toFun e'⟩⟩

/-- A finite module over the lifted ring has a representative in the original universe.
Source: finite generation and the small-carrier equivalence, Stacks Tag 00DV. -/
private theorem small_finite_module (B : Type t) [CommRing B]
    (M : ModuleCat.{t + 1} (ULift.{t + 1} B)) [Module.Finite (ULift.{t + 1} B) M] :
    ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
      ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).obj N ≅ M) := by
  let : RingHomInvPair
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom :=
    ⟨by ext x; rfl, by ext x; rfl⟩
  let : RingHomInvPair
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom :=
    ⟨by ext x; rfl, by ext x; rfl⟩
  let N := (ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom).obj M
  let e : LinearEquiv
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
      (σ' := (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).symm.toRingHom) M N :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have : Module.Finite B N := Module.Finite.of_surjective e.toLinearMap e.surjective
  have : Small.{t} N := Module.Finite.small B N
  let P := ModuleCat.of B (Shrink.{t} N)
  let f : P ≃ₗ[B] N := Shrink.linearEquiv B N
  let fl : (ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).obj P ≃ₗ[ULift.{t + 1} B] M :=
    { toFun := fun x ↦ f x.down
      invFun := fun x ↦ ULift.up (f.symm x)
      left_inv := fun x ↦ by apply ULift.ext; exact f.symm_apply_apply x.down
      right_inv := fun x ↦ f.apply_symm_apply x
      map_add' := fun x y ↦ f.map_add x.down y.down
      map_smul' := fun r x ↦ f.map_smul r.down x.down }
  exact ⟨P, Module.Finite.equiv f.symm, ⟨fl.toModuleIso⟩⟩

attribute [local irreducible] completedAdicChangeData pbcScalarAdjunction

/-- Reflect a supplied constant model through the fixed-scalar slice coordinates.
Source: Stacks Project, Tags 03CY and 04IX. -/
private theorem ringed_model_of_fixed (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) [IsIso φ] (W : X.Etale)
    (F : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (M : ModuleCat.{t + 1} (ULift.{t + 1} B)) [Module.Finite (ULift.{t + 1} B) M]
    (e : (finiteCoefficientSliceRestriction X B R φ W).obj F ≅
      (constantSheaf (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj M) :
    ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
      ((SheafOfModules.overFunctor.{t + 1} _ ((toProEt X).obj W)).obj F ≅
        (SheafOfModules.overFunctor.{t + 1} _ ((toProEt X).obj W)).obj
          ((completedAdicChange X φ).obj
            ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
              (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                koszulConstantFunctor X B).obj N))) := by
  obtain ⟨N, hN, ⟨eN⟩⟩ := small_finite_module B M
  let L := (ModuleCat.uliftFunctor.{t + 1, t} B ⋙ ModuleCat.restrictScalars.{t + 1}
    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).obj N
  let K := (koszulConstantFunctor X B).obj L
  let G := proEtaleModuleRestriction X B ⋙ ProEtale.localizationRestriction
    (ModuleCat.{t + 1} (ULift.{t + 1} B)) W.hom inferInstance
  have : (pbcRestrict φ).IsEquivalence :=
    SliceModelTransportProof.scalarRestrictionIso_equivalence X B R φ
  let η : 𝟭 _ ≅ completedAdicChange X φ ⋙ pbcRestrict φ :=
    asIso (pbcScalarAdjunction φ).unit
  let c : (finiteCoefficientSliceRestriction X B R φ W).obj
      ((completedAdicChange X φ).obj K) ≅
        (constantSheaf (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B))).obj L :=
    G.mapIso (η.symm.app K) ≪≫
      (Functor.isoWhiskerRight (SliceModelTransportProof.koszulConstantScalarIso X B)
        (ProEtale.localizationRestriction
          (ModuleCat.{t + 1} (ULift.{t + 1} B)) W.hom inferInstance)).app L ≪≫
      (SliceModelTransportProof.constantLocalizationIso X B W).app L
  let E := SliceModelTransportProof.sliceCoordinates X B R φ W
  have : E.IsEquivalence := SliceModelTransportProof.sliceCoordinates_equivalence X B R φ W
  let sq := SliceModelTransportProof.sliceCoordinatesSquare X B R φ W
  exact ⟨N, hN, ⟨(Functor.FullyFaithful.ofFullyFaithful E).preimageIso
    (sq.app F ≪≫ e ≪≫ (constantSheaf (ProEt.topology W.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapIso eN.symm ≪≫ c.symm ≪≫
        (sq.app ((completedAdicChange X φ).obj K)).symm)⟩⟩

/-- Fixed-scalar pro-etale finite local models give etale finite local models.

Source: Stacks Project, proetale.tex, Tag 099Y, and sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-reverse).

Proof: Restrict fixed-scalar charts to etale objects and use finite presentation
over the finite coefficient ring. Apply the coefficient-sized etale-cover theorem,
then transport the resulting charts through the normalized constant-module and
ringed-slice comparisons. -/
theorem finiteCoefficient_etaleLocal_encoding_reverse
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ) (V : X.Etale)
    (F : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    let R₀ := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ)).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    ProFiniteModels.fixedModels (ProEt.topology V.left) (ULift.{t + 1} B)
      ((finiteCoefficientSliceRestriction X B R φ V).obj F) → P F := by
  let := hφ
  dsimp only
  intro hF
  let A := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let H := (finiteCoefficientSliceRestriction X B R φ V).obj F
  obtain ⟨I, U, hU, hm⟩ := fixed_etale_charts V.left (ULift.{t + 1} B) H hF
  let Z (i : I) : X.Etale := Etale.mk ((U i).hom ≫ V.hom)
  let a (i : I) : Z i ⟶ V := MorphismProperty.Over.homMk (U i).hom rfl
  have hc : Sieve.ofArrows Z a ∈ X.smallEtaleTopology V := by
    apply (ofArrows_mem_smallEtaleTopology_iff a).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨T, f, ⟨i, ⟨q⟩⟩, y, hy⟩ := (mem_smallEtaleTopology_iff _).mp
      (hU (Etale.mk (𝟙 V.left))) x
    refine Set.mem_iUnion.mpr ⟨i, q.left y, ?_⟩
    change (U i).hom (q.left y) = x
    have hq := MorphismProperty.Over.w q
    have hf := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 V.left = T.hom at hf
    calc
      (U i).hom (q.left y) = T.hom y := congrArg (fun f ↦ f y) hq
      _ = f.left y := congrArg (fun f ↦ f y) ((Category.comp_id f.left).symm.trans hf).symm
      _ = x := hy
  intro W g
  refine ⟨(Sieve.ofArrows Z a).pullback g,
    X.smallEtaleTopology.pullback_stable g hc, ?_⟩
  intro T f hf
  obtain ⟨Z', q, a', ⟨i⟩, hq⟩ := hf
  obtain ⟨M, hM, ⟨e⟩⟩ := hm i
  have := hM
  let b : T ⟶ Z i := q
  let j := ProEtale.upperStar A b.left
  let r := SliceModelTransportProof.fixedRestrictionComp X B R φ (Z i) T b
  let z := SliceModelTransportProof.fixedRestrictionComp X B R φ V (Z i) (a i)
  let c := fixedConstantPullbackIso b.left (ULift.{t + 1} B) M
  let e' : (finiteCoefficientSliceRestriction X B R φ T).obj F ≅
      (constantSheaf (ProEt.topology T.left) A).obj M :=
    r.app F ≪≫ j.mapIso (z.app F ≪≫ e) ≪≫ c
  exact ringed_model_of_fixed X B R φ T F M e'

end AlgebraicGeometry.Scheme
