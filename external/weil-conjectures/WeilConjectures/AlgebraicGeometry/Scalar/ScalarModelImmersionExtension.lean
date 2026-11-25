/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.SixFunctors.NoetherianComplementaryStratifications
import all WeilConjectures.AlgebraicGeometry.IntegralContinuousCokernelLocalModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Immersion extensions and finite constant scalar models

The assertion includes exactness, preservation of constructibility, and the extended
adapted stratifications. Isomorphisms on the old strata retain every chosen covering
and scalar presentation; the complementary stratum has the zero model.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek CondensedRing.upperStarLowerStarAdjunction
  CondensedRing.openImmersionLowerShriekUpperStarAdjunction CondensedRing.upperStarComp
  CondensedRing.comapPullbackHomCompIso

/-- The open and closed extension assertions for one condensed coefficient ring.
The two existential stratifications contain exactly the original strata and one
complementary stratum, as schemes over the target, and are adapted to the extension.
The stratum isomorphisms retain the original covers and finitely presented scalar modules.
`IsZero` on the additional stratum specifies the zero scalar model, using the identity
cover and the zero presentation over the point. -/
def ScalarModelImmersionExtensionAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z T : Scheme.{u}}
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) : Prop :=
  PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
  PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
  PreservesFiniteLimits (CondensedRing.lowerStar Λ i) ∧
  PreservesFiniteColimits (CondensedRing.lowerStar Λ i) ∧
  (∀ F : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
    IsConstantModelConstructible Λ U F →
      IsConstantModelConstructible Λ T
        ((CondensedRing.openImmersionLowerShriek Λ j).obj F)) ∧
  (∀ G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z),
    IsConstantModelConstructible Λ Z G →
      IsConstantModelConstructible Λ T ((CondensedRing.lowerStar Λ i).obj G)) ∧
  (∀ (F : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
      (S : Scheme.Stratification U),
    (∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj F)) →
    (∃ (R : Scheme.Stratification T) (e : Fin R.n ≃ Option (Fin S.n)),
      (∀ b : Fin R.n, match e b with
        | none => Nonempty (Over.mk (R.immersion b) ≅ Over.mk i)
        | some a => Nonempty (Over.mk (R.immersion b) ≅ Over.mk (S.immersion a ≫ j))) ∧
      (∀ b : Fin R.n, HasFiniteConstantLocalModel Λ (R.domain b)
        ((CondensedRing.upperStar Λ (R.immersion b)).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj F)))) ∧
    (∀ a : Fin S.n,
      Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ j)).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj F) ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj F)) ∧
    IsZero ((CondensedRing.upperStar Λ i).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj F))) ∧
  (∀ (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (S : Scheme.Stratification Z),
    (∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj G)) →
    (∃ (R : Scheme.Stratification T) (e : Fin R.n ≃ Option (Fin S.n)),
      (∀ b : Fin R.n, match e b with
        | none => Nonempty (Over.mk (R.immersion b) ≅ Over.mk j)
        | some a => Nonempty (Over.mk (R.immersion b) ≅ Over.mk (S.immersion a ≫ i))) ∧
      (∀ b : Fin R.n, HasFiniteConstantLocalModel Λ (R.domain b)
        ((CondensedRing.upperStar Λ (R.immersion b)).obj
          ((CondensedRing.lowerStar Λ i).obj G)))) ∧
    (∀ a : Fin S.n,
      Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ i)).obj
          ((CondensedRing.lowerStar Λ i).obj G) ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj G)) ∧
    IsZero ((CondensedRing.upperStar Λ j).obj ((CondensedRing.lowerStar Λ i).obj G)))

private theorem local_model_zero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun a ↦ ?_⟩
  exact ⟨0, Mod.IsFinitelyPresented.of_isZero (isZero_zero _),
    ⟨((CondensedRing.upperStar Λ _).map_isZero h).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))⟩⟩

private theorem closed_operations
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z T : Scheme.{u}}
    [CompactSpace T] [QuasiSeparatedSpace T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hji : Set.range j = (Set.range i)ᶜ) :
    PreservesFiniteColimits (CondensedRing.lowerStar Λ i) ∧
      IsIso (CondensedRing.upperStarLowerStarAdjunction Λ i).counit := by
  obtain ⟨hc, hε, _⟩ := ringSheaf_closed_localization i j hji (condensedRingObj Λ T)
  have : PreservesFiniteColimits (CondensedRing.linearLowerStar Λ i) := hc
  have : IsIso (ringSheafAdjunction i (condensedRingObj Λ T)).counit :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hε
  have : (CondensedRing.linearLowerStar Λ i).Full :=
    (ringSheafAdjunction i (condensedRingObj Λ T)).fullyFaithfulROfIsIsoCounit.full
  have : (CondensedRing.linearLowerStar Λ i).Faithful :=
    (ringSheafAdjunction i (condensedRingObj Λ T)).fullyFaithfulROfIsIsoCounit.faithful
  have : (Mod.comap (condensedPullbackHom Λ i)).Full :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulFunctor.full
  let e := CondensedRing.comapPullbackHomCompIso Λ i
  have : (CondensedRing.lowerStar Λ i).Full := Functor.Full.of_iso e
  have : (CondensedRing.lowerStar Λ i).Faithful := Functor.Faithful.of_iso e
  exact ⟨preservesFiniteColimits_of_natIso e,
    (CondensedRing.upperStarLowerStarAdjunction Λ i).counit_isIso_of_R_fully_faithful⟩

private def AdaptedExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (h : X ⟶ T) (k : Y ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (S : Scheme.Stratification X) : Prop :=
    (∃ (E : Scheme.Stratification T) (f : Fin E.n ≃ Option (Fin S.n)),
      (∀ b, match f b with
        | none => Nonempty (Over.mk (E.immersion b) ≅ Over.mk k)
        | some a => Nonempty (Over.mk (E.immersion b) ≅ Over.mk (S.immersion a ≫ h))) ∧
      (∀ b, HasFiniteConstantLocalModel Λ (E.domain b)
        ((CondensedRing.upperStar Λ (E.immersion b)).obj H))) ∧
    (∀ a, Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H ≅
      (CondensedRing.upperStar Λ (S.immersion a)).obj M)) ∧
    IsZero ((CondensedRing.upperStar Λ k).obj H)

private theorem snoc_label {D : Type*} {n : ℕ} (v : Fin n → D) (w : D)
    (a : Fin (n + 1)) :
    match finSuccEquivLast a with
    | none => Fin.snoc (α := fun _ : Fin (n + 1) ↦ D) v w a = w
    | some b => Fin.snoc (α := fun _ : Fin (n + 1) ↦ D) v w a = v b := by
  refine Fin.lastCases ?_ (fun b ↦ ?_) a
  · simp only [finSuccEquivLast_last, Fin.snoc_last]
  · simp only [finSuccEquivLast_castSucc, Fin.snoc_castSucc]

private theorem snoc_property {D : Type*} {n : ℕ} (P : D → Prop)
    (v : Fin n → D) (w : D) (hv : ∀ a, P (v a)) (hw : P w)
    (a : Fin (n + 1)) : P (Fin.snoc (α := fun _ : Fin (n + 1) ↦ D) v w a) := by
  refine Fin.lastCases ?_ (fun b ↦ ?_) a
  · simpa only [Fin.snoc_last] using hw
  · simpa only [Fin.snoc_castSucc] using hv b

private theorem reindexed_snoc_property {D : Type*} {n m : ℕ} (P : D → Prop)
    (v : Fin n → D) (w : D) (r : Fin m → D) (e : Fin (n + 1) ≃ Fin m)
    (he : ∀ a, r (e a) = Fin.snoc (α := fun _ : Fin (n + 1) ↦ D) v w a)
    (hv : ∀ a, P (v a)) (hw : P w) : ∀ b, P (r b) := by
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [he a]
  exact snoc_property P v w hv hw a

private def withConstructibleStrata {T : Scheme.{u}}
    (R : Scheme.FiniteLocallyClosedStratification T)
    (hR : ∀ a, Topology.IsConstructible (R.stratum a)) : Scheme.Stratification T where
  n := R.n
  stratum := R.stratum
  isLocallyClosed_stratum := R.isLocallyClosed_stratum
  iUnion_stratum_eq_univ := R.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := R.pairwise_disjoint_stratum
  domain := R.domain
  immersion := R.immersion
  isImmersion := R.isImmersion
  range_immersion := R.range_immersion
  isConstructible_stratum := hR

-- Keep geometric reindexing abstract from the coefficient functors: substituting
-- dependent scheme/map pairs directly into their model predicate is expensive.
private theorem models_reindexed {X Y T : Scheme.{u}}
    (h : X ⟶ T) (k : Y ⟶ T) (S : Scheme.Stratification X)
    (R : Scheme.Stratification T) (e : Fin (S.n + 1) ≃ Fin R.n)
    (he : ∀ a, (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ T) =
      Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ T)
        (fun b ↦ ⟨S.domain b, S.immersion b ≫ h⟩) ⟨Y, k⟩ a)
    (P : ∀ W : Scheme.{u}, (W ⟶ T) → Prop)
    (hS : ∀ a, P (S.domain a) (S.immersion a ≫ h)) (hk : P Y k) :
    ∀ b, P (R.domain b) (R.immersion b) :=
  reindexed_snoc_property (fun d : Σ W : Scheme.{u}, W ⟶ T ↦ P d.1 d.2)
    (fun b ↦ ⟨S.domain b, S.immersion b ≫ h⟩) ⟨Y, k⟩
    (fun b ↦ ⟨R.domain b, R.immersion b⟩) e he hS hk

private theorem extended_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y T : Scheme.{u}}
    (h : X ⟶ T) (k : Y ⟶ T)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (H : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (eh : (CondensedRing.upperStar Λ h).obj H ≅ M)
    (hk : IsZero ((CondensedRing.upperStar Λ k).obj H))
    (S : Scheme.Stratification X)
    (hS : ∀ a, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M))
    (R : Scheme.Stratification T)
    (e : Fin (S.n + 1) ≃ Fin R.n)
    (he : ∀ a, (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ T) =
      Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ T)
        (fun b ↦ ⟨S.domain b, S.immersion b ≫ h⟩) ⟨Y, k⟩ a)
    : AdaptedExtension Λ h k M H S := by
  have old (a : Fin S.n) :
      (CondensedRing.upperStar Λ (S.immersion a ≫ h)).obj H ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M :=
    (CondensedRing.upperStarComp Λ (S.immersion a) h).app H ≪≫
      (CondensedRing.upperStar Λ (S.immersion a)).mapIso eh
  refine ⟨⟨R, e.symm.trans finSuccEquivLast, ?_, ?_⟩, fun a ↦ ⟨old a⟩, hk⟩
  · intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    change (match finSuccEquivLast (e.symm (e a)) with
      | none => Nonempty (Over.mk (R.immersion (e a)) ≅ Over.mk k)
      | some b => Nonempty (Over.mk (R.immersion (e a)) ≅
          Over.mk (S.immersion b ≫ h)))
    rw [e.symm_apply_apply]
    have hl := snoc_label
      (fun b : Fin S.n ↦ (⟨S.domain b, S.immersion b ≫ h⟩ : Σ W : Scheme.{u}, W ⟶ T))
      (⟨Y, k⟩ : Σ W : Scheme.{u}, W ⟶ T) a
    cases ha : finSuccEquivLast a with
    | none =>
      rw [ha] at hl
      exact ⟨eqToIso (congrArg (fun d : Σ W : Scheme.{u}, W ⟶ T ↦ Over.mk d.2)
        ((he a).trans hl))⟩
    | some b =>
      rw [ha] at hl
      exact ⟨eqToIso (congrArg (fun d : Σ W : Scheme.{u}, W ⟶ T ↦ Over.mk d.2)
        ((he a).trans hl))⟩
  · exact models_reindexed h k S R e he
      (fun W f ↦ HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ f).obj H))
      (fun b ↦ ContinuousRingUniverse.model_of_iso Λ (old b) (hS b))
      (local_model_zero Λ _ hk)

private theorem immersion_assertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Z T : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) [IsClosedImmersion i]
    (hji : Set.range j = (Set.range i)ᶜ) :
    ScalarModelImmersionExtensionAssertions Λ j i := by
  obtain ⟨_, hU, hZ, _, _, _, _, hj, hjS, hiS⟩ :=
    Scheme.noetherian_complementary_stratifications j i hji
  have := hU
  have := hZ
  have := hj
  obtain ⟨hcol, hε⟩ := closed_operations Λ j i hji
  have := hε
  have hopen (F : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) (S : Scheme.Stratification U)
      (hS : ∀ a, HasFiniteConstantLocalModel Λ (S.domain a)
        ((CondensedRing.upperStar Λ (S.immersion a)).obj F)) :
      AdaptedExtension Λ j i F ((CondensedRing.openImmersionLowerShriek Λ j).obj F) S := by
    let S' : Scheme.FiniteLocallyClosedStratification U :=
      { n := S.n
        stratum := S.stratum
        isLocallyClosed_stratum := S.isLocallyClosed_stratum
        iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
        pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
        domain := S.domain
        immersion := S.immersion
        isImmersion := S.isImmersion
        range_immersion := S.range_immersion }
    obtain ⟨R, e, he, hR⟩ := hjS S'
    have hz := CondensedRing.isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint
      Λ j i (by rw [hji]; exact disjoint_compl_left) F
    exact extended_models Λ j i F _
      (asIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app F)).symm
      hz S hS (withConstructibleStrata R hR) e he
  have hclosed (G : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)) (S : Scheme.Stratification Z)
      (hS : ∀ a, HasFiniteConstantLocalModel Λ (S.domain a)
        ((CondensedRing.upperStar Λ (S.immersion a)).obj G)) :
      AdaptedExtension Λ i j G ((CondensedRing.lowerStar Λ i).obj G) S := by
    let S' : Scheme.FiniteLocallyClosedStratification Z :=
      { n := S.n
        stratum := S.stratum
        isLocallyClosed_stratum := S.isLocallyClosed_stratum
        iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
        pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
        domain := S.domain
        immersion := S.immersion
        isImmersion := S.isImmersion
        range_immersion := S.range_immersion }
    obtain ⟨R, e, he, hR⟩ := hiS S'
    have hzero : IsZero ((ProEtale.upperStar Ab.{u + 1} j).obj
        (((CondensedRing.lowerStar Λ i).obj G).X)) := by
      rw [CondensedRing.lowerStar_obj_X]
      exact ProEtale.isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j
        (by rw [hji]; exact disjoint_compl_right) G.X
    have hz : IsZero ((CondensedRing.upperStar Λ j).obj
        ((CondensedRing.lowerStar Λ i).obj G)) :=
      CondensedRing.isZero_of_isZero_X Λ
        (hzero.of_iso (CondensedRing.upperStarObjXIso Λ j _))
    exact extended_models Λ i j G _
      (asIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app G))
      hz S hS (withConstructibleStrata R hR) e he
  refine ⟨inferInstance, inferInstance, inferInstance, hcol, ?_, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨S, hS⟩ := (show IsFiniteConstantStratified Λ U F from by
      simpa only [IsConstantModelConstructible, ite_eq_left
        (show CompactSpace U ∧ QuasiSeparatedSpace U from ⟨inferInstance, inferInstance⟩)]
        using hF)
    obtain ⟨⟨R, e, _, hR⟩, _, _⟩ := hopen F S hS
    exact (by
      simpa only [IsConstantModelConstructible, ite_eq_left
        (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)]
        using (show IsFiniteConstantStratified Λ T _ from ⟨R, hR⟩))
  · intro G hG
    obtain ⟨S, hS⟩ := (show IsFiniteConstantStratified Λ Z G from by
      simpa only [IsConstantModelConstructible, ite_eq_left
        (show CompactSpace Z ∧ QuasiSeparatedSpace Z from ⟨inferInstance, inferInstance⟩)]
        using hG)
    obtain ⟨⟨R, e, _, hR⟩, _, _⟩ := hclosed G S hS
    exact (by
      simpa only [IsConstantModelConstructible, ite_eq_left
        (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)]
        using (show IsFiniteConstantStratified Λ T _ from ⟨R, hR⟩))
  · intro F S hS
    exact ⟨(hopen F S hS).1, (hopen F S hS).2.1, (hopen F S hS).2.2⟩
  · intro G S hS
    exact ⟨(hclosed G S hS).1, (hclosed G S hS).2.1, (hclosed G S hS).2.2⟩

/-- Exact open extension by zero and closed direct image preserve finite constant
scalar-model constructibility, retaining the source stratification and its local models
and adjoining the complementary locus with zero model, for every admissible coefficient. -/
theorem scalarModelImmersionExtension
    (ℓ : ℕ) [Fact ℓ.Prime] {U Z T : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] (i : Z ⟶ T) [IsClosedImmersion i]
    (_hComplement : Set.range j = (Set.range i)ᶜ) :
    (∀ (A : Type u) [CommRing A] [Finite A],
      ScalarModelImmersionExtensionAssertions (cartesianFinitePointRing A) j i) ∧
    ScalarModelImmersionExtensionAssertions (Profinite.continuousMapRingObj (PadicInt ℓ)) j i ∧
    ScalarModelImmersionExtensionAssertions (Profinite.continuousMapRingObj (Padic ℓ)) j i ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ScalarModelImmersionExtensionAssertions (Profinite.padicIntegersRingObj ℓ E.1) j i ∧
      ScalarModelImmersionExtensionAssertions (Profinite.continuousMapRingObj E.1) j i) ∧
    ScalarModelImmersionExtensionAssertions (Profinite.padicAlgClRingObj ℓ) j i := by
  exact ⟨fun A _ _ ↦ immersion_assertions _ j i _hComplement,
    immersion_assertions _ j i _hComplement, immersion_assertions _ j i _hComplement,
    fun E ↦ ⟨immersion_assertions _ j i _hComplement,
      immersion_assertions _ j i _hComplement⟩, immersion_assertions _ j i _hComplement⟩

end AlgebraicGeometry.ProEtale
