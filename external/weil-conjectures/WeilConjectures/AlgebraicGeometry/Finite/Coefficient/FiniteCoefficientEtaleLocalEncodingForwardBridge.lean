/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceModelTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsPullback
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Etale local models imply the fixed-coefficient pro-etale local-system condition

Source: Stacks Project, proetale.tex, Tag 099Y; sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-forward-bridge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The displayed etale-local condition yields the fixed-coefficient pro-etale local-system
condition for the slice restriction.

Source: Stacks Project, proetale.tex, Tag 099Y, and sites-modules.tex, Tag 04IX.
Proof: take the identity etale chart, regard each etale covering sieve as a pro-etale
covering, and pull it back along every pro-etale object. The scalar restriction,
localization, and normalized constant-module comparisons identify the resulting models
with fixed-scalar constant sheaves. This is the transport step needed before applying
the intrinsic fixed-model comparison.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-forward-bridge). -/
theorem finiteCoefficient_etaleLocal_encoding_forward_bridge
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
    P F → IsFinitelyPresentedLocallyConstantProEtaleModule
      ((proEtaleModuleEncoding V.left B).inverse.obj
        ((finiteCoefficientSliceRestriction X B R φ V).obj F)) := by
  classical
  let := hφ
  dsimp only
  intro hP
  let A := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let H := (finiteCoefficientSliceRestriction X B R φ V).obj F
  obtain ⟨S, hS, hm⟩ := hP V (𝟙 V)
  obtain ⟨I, Z, a, rfl⟩ := S.exists_eq_ofArrows
  have hc : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (a i).left) ∈
      proetalePrecoverage V.left := by
    apply etalePrecoverage_le_proetalePrecoverage
    refine (ofArrows_mem_precoverage_iff _).mpr ⟨?_, fun i ↦ inferInstance⟩
    intro x
    have hx : x ∈ ⋃ i, Set.range (a i).left := by
      rw [(ofArrows_mem_smallEtaleTopology_iff a).mp hS]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx
  have models (i : I) : ∃ M : A, Module.Finite (ULift.{t + 1} B) M ∧
      Nonempty ((ProEtale.upperStar A (a i).left).obj H ≅
        (constantSheaf (ProEt.topology (Z i).left) A).obj M) := by
    obtain ⟨N, hN, ⟨e⟩⟩ := hm (Z i) (a i) (Sieve.ofArrows_mk _ _ i)
    let M := (ModuleCat.uliftFunctor.{t + 1, t} B ⋙
      ModuleCat.restrictScalars.{t + 1}
        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).obj N
    let K := (koszulConstantFunctor X B).obj M
    have := hN
    have : Finite N := Module.finite_of_finite B
    have : Finite M := inferInstanceAs (Finite (ULift.{t + 1} N))
    have hM : Module.Finite (ULift.{t + 1} B) M := Module.Finite.of_finite
    let E := SliceModelTransportProof.sliceCoordinates X B R φ (Z i)
    let sq := SliceModelTransportProof.sliceCoordinatesSquare X B R φ (Z i)
    let G := proEtaleModuleRestriction X B ⋙ ProEtale.localizationRestriction A
      (Z i).hom inferInstance
    have : (pbcRestrict φ).IsEquivalence :=
      SliceModelTransportProof.scalarRestrictionIso_equivalence X B R φ
    let η : 𝟭 _ ≅ completedAdicChange X φ ⋙ pbcRestrict φ :=
      asIso (pbcScalarAdjunction φ).unit
    let c : (finiteCoefficientSliceRestriction X B R φ (Z i)).obj
        ((completedAdicChange X φ).obj K) ≅
          (constantSheaf (ProEt.topology (Z i).left) A).obj M :=
      G.mapIso (η.symm.app K) ≪≫
        (Functor.isoWhiskerRight (SliceModelTransportProof.koszulConstantScalarIso X B)
          (ProEtale.localizationRestriction A (Z i).hom inferInstance)).app M ≪≫
        (SliceModelTransportProof.constantLocalizationIso X B (Z i)).app M
    exact ⟨M, hM, ⟨((SliceModelTransportProof.fixedRestrictionComp X B R φ V
      (Z i) (a i)).app F).symm ≪≫ (sq.app F).symm ≪≫ E.mapIso e ≪≫
        sq.app ((completedAdicChange X φ).obj K) ≪≫ c⟩⟩
  have hfixed : ProFiniteModels.fixedModels (ProEt.topology V.left)
      (ULift.{t + 1} B) H := by
    intro T
    let g (i : I) := (a i).left
    have : ∀ i, WeaklyEtale (g i) := fun i ↦ inferInstance
    let W (i : I) := ProEt.baseChange (g i) T
    let w (i : I) : W i ⟶ T := ProEt.baseChangeHom (g i) T
    refine ⟨Sieve.ofArrows W w, ProEt.ofArrows_baseChange_mem_topology T g hc,
      fun Q f hf ↦ ?_⟩
    obtain ⟨D, d, e, ⟨i⟩, rfl⟩ := hf
    obtain ⟨M, hM, ⟨em⟩⟩ := models i
    let p : Q.left ⟶ (Z i).left := d.left ≫ pullback.snd T.hom (g i)
    have hp : Q.hom = p ≫ (a i).left := by
      calc
        Q.hom = d.left ≫ (W i).hom := (MorphismProperty.Over.w d).symm
        _ = d.left ≫ (pullback.snd T.hom (g i) ≫ g i) :=
          congrArg (fun k ↦ d.left ≫ k) (pullback.condition (f := T.hom) (g := g i))
        _ = p ≫ (a i).left := by simp only [p, g, Category.assoc]
    refine ⟨M, hM, ⟨(fixedModelSchemeIso H Q M).symm ?_⟩⟩
    exact eqToIso (congrArg (fun q ↦ (ProEtale.upperStar A q).obj H) hp) ≪≫
      (ProEtale.upperStarComp A p (a i).left).app H ≪≫
      (ProEtale.upperStar A p).mapIso em ≪≫
      fixedConstantPullbackIso p (ULift.{t + 1} B) M
  apply (ProFiniteModels.intrinsic_fixedModels V.left B _).mpr
  exact ProFiniteModels.fixedModels_of_iso (ProEt.topology V.left) (ULift.{t + 1} B)
    ((proEtaleModuleEncoding V.left B).counitIso.app H).symm hfixed

end AlgebraicGeometry.Scheme
