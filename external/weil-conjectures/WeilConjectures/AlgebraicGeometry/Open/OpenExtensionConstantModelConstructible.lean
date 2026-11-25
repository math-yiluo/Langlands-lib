/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Extension by zero and finite constant local models
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

namespace CondensedRing

set_option backward.isDefEq.respectTransparency false in
private theorem open_unit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openImmersionLowerShriekUpperStarAdjunction Λ j).unit := by
  let a₀ := ProEtale.openImmersionLowerShriekAdjunction Ab.{u + 1} j
  have : IsIso a₀.unit :=
    (ProEtale.openImmersionAdjunctionTriple Ab.{u + 1} j).isIso_unit_iff_isIso_counit.mpr
      (ProEtale.isIso_openImmersionRestrictionLowerStarAdjunction_counit Ab.{u + 1} j)
  have ff₀ := a₀.fullyFaithfulLOfIsIsoUnit
  have := ff₀.full
  have := ff₀.faithful
  have hu : IsIso (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit :=
    Adjunction.unit_isIso_of_L_fully_faithful _
  have hlin : IsIso (linearOpenImmersionLowerShriekAdjunction Λ j).unit := by
    have hlinapp (M) : IsIso ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M) := by
      have hh : IsIso ((Mod.forget _).map
          ((linearOpenImmersionLowerShriekAdjunction Λ j).unit.app M)) := by
        dsimp [linearOpenImmersionLowerShriekAdjunction, Adjunction.mapModLeftAdjunction,
          Adjunction.mkOfHomEquiv, Adjunction.mk', Mod.forget, Mod.Hom.mk']
        rw [Adjunction.homEquiv_unit]
        simp only [Mod.id_hom']
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
        infer_instance
      exact isIso_of_reflects_iso _ (Mod.forget _)
    exact NatIso.isIso_of_isIso_app _
  have ff := (linearOpenImmersionLowerShriekAdjunction Λ j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (Mod.comap (condensedPullbackHom Λ j)).Full :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.full
  have : (Mod.comap (condensedPullbackHom Λ j)).Faithful :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)).fullyFaithfulFunctor.faithful
  have : (openImmersionLowerShriek Λ j).Full :=
    inferInstanceAs ((Mod.comap (condensedPullbackHom Λ j)) ⋙
      linearOpenImmersionLowerShriek Λ j).Full
  have : (openImmersionLowerShriek Λ j).Faithful :=
    inferInstanceAs ((Mod.comap (condensedPullbackHom Λ j)) ⋙
      linearOpenImmersionLowerShriek Λ j).Faithful
  exact (openImmersionLowerShriekUpperStarAdjunction Λ j).unit_isIso_of_L_fully_faithful

end CondensedRing

set_option backward.isDefEq.respectTransparency false in
private lemma restriction_pushforward_isZero {U W X : Scheme.{u}}
    (g : W ⟶ X) (j : U ⟶ X) [IsOpenImmersion j]
    (hgj : Set.range g.base ∩ Set.range j.base = ∅)
    (F : Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) :
    IsZero ((openImmersionRestriction Ab.{u + 1} j).obj ((g)_*[Ab.{u + 1}].obj F)) := by
  refine Sheaf.isZero_of_isZero_obj _ ?_
  rintro ⟨T⟩
  let W' := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj
    ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj T)
  have : IsEmpty W'.left := by
    refine ⟨fun z ↦ ?_⟩
    have hz : (pullback.fst (T.hom ≫ j) g ≫ T.hom ≫ j).base z ∈
        Set.range g.base ∩ Set.range j.base := by
      refine ⟨?_, ⟨T.hom.base (pullback.fst (T.hom ≫ j) g z), rfl⟩⟩
      rw [pullback.condition]
      exact ⟨_, rfl⟩
    rw [hgj] at hz
    exact hz
  exact (isZero_zero _).of_iso
    ((Scheme.ProEt.isTerminalSectionsOfIsEmpty F W').uniqueUpToIso
      HasZeroObject.zeroIsTerminal)

private lemma pullback_lowerShriek_isZero {U W X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Set.range j.base ∩ Set.range g.base = ∅)
    (F : Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) :
    IsZero ((g)^*[Ab.{u + 1}].obj ((j)_!open[Ab.{u + 1}].obj F)) := by
  have hz : IsInitial ((g)^*[Ab.{u + 1}].obj ((j)_!open[Ab.{u + 1}].obj F)) := by
    refine IsInitial.ofUnique (h := fun H ↦ ?_)
    haveI : Unique (F ⟶ (openImmersionRestriction Ab.{u + 1} j).obj
        ((g)_*[Ab.{u + 1}].obj H)) := by
      have h := restriction_pushforward_isZero g j (by rwa [Set.inter_comm]) H
      exact ⟨⟨h.isTerminal.from F⟩, fun a ↦ h.isTerminal.hom_ext _ _⟩
    exact Equiv.unique
      (((upperStarLowerStarAdjunction Ab.{u + 1} g).homEquiv _ H).trans
        ((openImmersionLowerShriekAdjunction Ab.{u + 1} j).homEquiv F _))
  exact (isZero_zero _).of_iso (hz.uniqueUpToIso HasZeroObject.zeroIsInitial)

private lemma constant_model_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hN : HasFiniteConstantLocalModel Λ X N) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨𝒰, h𝒰⟩ := hN
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e ≪≫ eP⟩⟩

private lemma constant_model_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨Precoverage.ZeroHypercover.singleton (𝟙 X)
    (Precoverage.mem_coverings_of_isIso (J := Scheme.proetalePrecoverage) _), fun i ↦ ?_⟩
  refine ⟨0, ?_, ?_⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso
      (isZero_cokernel_of_epi (𝟙 (Mod.finiteFree Λ 0)))⟩⟩
  · change Nonempty ((CondensedRing.upperStar Λ (𝟙 X)).obj M ≅
      ((upperStarFromPoint X).mapMod Λ).obj 0)
    have : pointUpperStar.{u}.IsLeftAdjoint :=
      pointUpperStarLowerStarAdjunction.isLeftAdjoint
    have : PreservesFiniteColimits (upperStarFromPoint X) := by
      unfold upperStarFromPoint
      infer_instance
    have : ((upperStarFromPoint X).mapMod Λ).PreservesZeroMorphisms :=
      inferInstance
    exact ⟨((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))⟩

private lemma module_isZero_of_isEmpty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} [IsEmpty X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsZero M := by
  have hM : IsZero M.X := by
    refine Sheaf.isZero_of_isZero_obj _ ?_
    rintro ⟨T⟩
    have : IsEmpty T.left := ⟨fun t ↦ @IsEmpty.false X ‹IsEmpty X› (T.hom t)⟩
    exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X T).isZero
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ X)).map_injective
  exact hM.eq_of_src _ _

private lemma module_pullback_lowerShriek_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U W X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (g : W ⟶ X)
    (hjg : Set.range j.base ∩ Set.range g.base = ∅)
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    IsZero ((CondensedRing.upperStar Λ g).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) := by
  let N := (CondensedRing.openImmersionLowerShriek Λ j).obj M
  have hzAb := pullback_lowerShriek_isZero j g hjg M.X
  let e : CondensedRing.upperStar Λ g ⋙ Mod.forget (condensedRingObj Λ W) ≅
      Mod.forget (condensedRingObj Λ X) ⋙ ProEtale.upperStar Ab.{u + 1} g :=
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((ProEtale.upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ X))
        (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ g)))
      (Mod.forget (condensedRingObj Λ W))
  have hz' := hzAb.of_iso (e.app N)
  apply (IsZero.iff_id_eq_zero _).2
  apply (Mod.forget (condensedRingObj Λ W)).map_injective
  exact hz'.eq_of_src _ _

private noncomputable def extendedStratification {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (S : Scheme.FiniteLocallyClosedStratification U) :
    Scheme.FiniteLocallyClosedStratification X where
  n := S.n + 1
  domain b := (Fin.cases (motive := fun _ ↦ Over X) (Over.mk j.closedComplement)
    (fun a ↦ Over.mk (S.immersion a ≫ j)) b).left
  immersion b := (Fin.cases (motive := fun _ ↦ Over X) (Over.mk j.closedComplement)
    (fun a ↦ Over.mk (S.immersion a ≫ j)) b).hom
  stratum := Fin.cases (Set.range j.closedComplement)
    (fun a ↦ Set.range (S.immersion a ≫ j))
  isImmersion := by
    intro b
    induction b using Fin.cases with
    | zero => exact inferInstanceAs (IsImmersion j.closedComplement)
    | succ a =>
      have := S.isImmersion a
      exact inferInstanceAs (IsImmersion (S.immersion a ≫ j))
  range_immersion := by
    intro b
    induction b using Fin.cases <;> rfl
  isLocallyClosed_stratum := by
    intro b
    induction b using Fin.cases with
    | zero => exact j.closedComplement.isLocallyClosed_range
    | succ a =>
      have := S.isImmersion a
      exact (S.immersion a ≫ j).isLocallyClosed_range
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Set.range j
    · obtain ⟨y, rfl⟩ := hx
      have hy : y ∈ ⋃ a, S.stratum a := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
      rw [← S.range_immersion a] at ha
      obtain ⟨z, rfl⟩ := ha
      exact Set.mem_iUnion.mpr ⟨a.succ, ⟨z, rfl⟩⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨0, ?_⟩
      change x ∈ Set.range j.closedComplement
      simpa only [j.range_closedComplement, Set.mem_compl_iff] using hx
  pairwise_disjoint_stratum := by
    intro a b hab
    induction a using Fin.cases with
    | zero =>
      induction b using Fin.cases with
      | zero => exact (hab rfl).elim
      | succ b =>
        apply Set.disjoint_left.mpr
        rintro x hx ⟨y, rfl⟩
        change (S.immersion b ≫ j) y ∈ Set.range j.closedComplement at hx
        rw [j.range_closedComplement] at hx
        exact hx ⟨S.immersion b y, rfl⟩
    | succ a =>
      induction b using Fin.cases with
      | zero =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ hx
        change (S.immersion a ≫ j) y ∈ Set.range j.closedComplement at hx
        rw [j.range_closedComplement] at hx
        exact hx ⟨S.immersion a y, rfl⟩
      | succ b =>
        apply Set.disjoint_left.mpr
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        have h := j.isOpenEmbedding.injective hz
        exact Set.disjoint_left.mp
          (S.pairwise_disjoint_stratum (fun h ↦ hab (congrArg Fin.succ h)))
          ((S.range_immersion a) ▸ Set.mem_range_self y)
          ((S.range_immersion b) ▸ ⟨z, h⟩)

private theorem extendedStratification_property {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (S : Scheme.FiniteLocallyClosedStratification U)
    (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (h₀ : P _ j.closedComplement)
    (hS : ∀ a : Fin S.n, P _ (S.immersion a ≫ j)) :
    ∀ b : Fin (extendedStratification j S).n,
      P ((extendedStratification j S).domain b)
        ((extendedStratification j S).immersion b) := by
  intro b
  induction b using Fin.cases with
  | zero => exact h₀
  | succ a => exact hS a

private theorem extendedStratification_identification {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (S : Scheme.FiniteLocallyClosedStratification U) :
    ∀ b : Fin (extendedStratification j S).n,
      match finSuccEquiv S.n b with
      | none => Nonempty
          (Over.mk ((extendedStratification j S).immersion b) ≅ Over.mk j.closedComplement)
      | some a => Nonempty
          (Over.mk ((extendedStratification j S).immersion b) ≅ Over.mk (S.immersion a ≫ j)) := by
  intro b
  induction b using Fin.cases with
  | zero => exact ⟨Iso.refl _⟩
  | succ a => exact ⟨Iso.refl _⟩

private def finiteToStratification {X : Scheme.{u}}
    (T : Scheme.FiniteLocallyClosedStratification X)
    (hT : ∀ b : Fin T.n, Topology.IsConstructible (T.stratum b)) :
    Scheme.Stratification X where
  n := T.n
  stratum := T.stratum
  isLocallyClosed_stratum := T.isLocallyClosed_stratum
  isConstructible_stratum := hT
  iUnion_stratum_eq_univ := T.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := T.pairwise_disjoint_stratum
  domain := T.domain
  immersion := T.immersion
  isImmersion := T.isImmersion
  range_immersion := T.range_immersion

private theorem stratified_of_property {X : Scheme.{u}}
    (P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop)
    (T : Scheme.FiniteLocallyClosedStratification X)
    (hT : ∀ b : Fin T.n, Topology.IsConstructible (T.stratum b))
    (hP : ∀ b : Fin T.n, P (T.domain b) (T.immersion b)) :
    ∃ R : Scheme.Stratification X, ∀ b : Fin R.n, P (R.domain b) (R.immersion b) := by
  exact ⟨finiteToStratification T hT, hP⟩

set_option backward.isDefEq.respectTransparency true in
private theorem constant_constructible_of_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hN : IsFiniteConstantStratified Λ X N) :
    IsConstantModelConstructible Λ X N := by
  classical
  exact (show IsConstantModelConstructible Λ X N = IsFiniteConstantStratified Λ X N from
    ite_eq_left ⟨inferInstance, inferInstance⟩).mpr hN

set_option backward.isDefEq.respectTransparency true in
/-- Extension by zero preserves constructibility with finite constant scalar models.
The supplied stratification witnesses the constructibility hypothesis. The equivalence
of indices identifies the extended stratification, as schemes over X, with precisely the
old strata and the reduced closed complement; empty strata are allowed. -/
theorem constantModelConstructible_openImmersionLowerShriek
    (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (S : Scheme.FiniteLocallyClosedStratification U)
    (_hS : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (_hM : ∀ a : Fin S.n, HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M)) :
    IsConstantModelConstructible Λ X ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ∧
    (∃ (T : Scheme.FiniteLocallyClosedStratification X)
        (e : Fin T.n ≃ Option (Fin S.n)),
      (∀ b : Fin T.n, Topology.IsConstructible (T.stratum b)) ∧
      (∀ b : Fin T.n, match e b with
        | none => Nonempty (Over.mk (T.immersion b) ≅ Over.mk j.closedComplement)
        | some a => Nonempty (Over.mk (T.immersion b) ≅ Over.mk (S.immersion a ≫ j)))) ∧
    (∀ a : Fin S.n,
      Nonempty ((CondensedRing.upperStar Λ (S.immersion a ≫ j)).obj
          ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M)) ∧
    IsZero ((CondensedRing.upperStar Λ j.closedComplement).obj
      ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) ∧
    (IsEmpty U → IsZero M ∧ IsZero ((CondensedRing.openImmersionLowerShriek Λ j).obj M)) ∧
    (IsIso j → IsEmpty (Scheme.IdealSheafData.vanishingIdeal
      ⟨(j.opensRange : Set X)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subscheme) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let N := (CondensedRing.openImmersionLowerShriek Λ j).obj M
  have hu := CondensedRing.open_unit_isIso Λ j
  let eU : (CondensedRing.upperStar Λ j).obj N ≅ M :=
    (asIso ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M)).symm
  let eS (a : Fin S.n) :
      (CondensedRing.upperStar Λ (S.immersion a ≫ j)).obj N ≅
        (CondensedRing.upperStar Λ (S.immersion a)).obj M :=
    (CondensedRing.upperStarComp Λ (S.immersion a) j).app N ≪≫
      (CondensedRing.upperStar Λ (S.immersion a)).mapIso eU
  have hz := module_pullback_lowerShriek_isZero Λ j j.closedComplement
    (by rw [j.range_closedComplement]; exact Set.inter_compl_self _) M
  let T := extendedStratification j S
  have hT (b : Fin T.n) : Topology.IsConstructible (T.stratum b) :=
    (T.isLocallyClosed_stratum b).isConstructible_of_noetherianSpace
  let P : (Y : Scheme.{u}) → (Y ⟶ X) → Prop := fun Y f ↦
    HasFiniteConstantLocalModel Λ Y ((CondensedRing.upperStar Λ f).obj N)
  have hzero : P _ j.closedComplement := constant_model_of_isZero Λ _ hz
  have hold (a : Fin S.n) : P (S.domain a) (S.immersion a ≫ j) :=
    constant_model_of_iso Λ (eS a) (_hM a)
  have hmodels := extendedStratification_property j S P hzero hold
  have hstrat := stratified_of_property P (extendedStratification j S) hT hmodels
  have hc := constant_constructible_of_models Λ N hstrat
  refine ⟨hc, ⟨T, finSuccEquiv S.n, hT, extendedStratification_identification j S⟩,
    (fun a ↦ ⟨eS a⟩), hz, ?_, ?_⟩
  · intro hU
    have hM := module_isZero_of_isEmpty Λ M
    exact ⟨hM, (CondensedRing.openImmersionLowerShriek Λ j).map_isZero hM⟩
  · intro hj
    refine ⟨fun z ↦ ?_⟩
    have hz' : j.closedComplement z ∈ Set.range j.closedComplement := Set.mem_range_self z
    rw [j.range_closedComplement] at hz'
    exact hz' (j.homeomorph.surjective (j.closedComplement z))

end AlgebraicGeometry.ProEtale
