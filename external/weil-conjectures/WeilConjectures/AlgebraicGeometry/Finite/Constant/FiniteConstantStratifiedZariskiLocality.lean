/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement

import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore

/-!
# Zariski locality of finite constant stratified constructibility

Source: Stacks Project, Topology, Tags 005J, 09YD and 053W; Etale Cohomology,
Tag 095E, finite-affine-cover argument; blueprint chap-The-pro-etale-site,
definition-constructible-sheaves, clause 2 (blueprint: lem-sfb-constructible-zariski-locality).

The three clauses state restriction to quasi-compact opens, assembly over a finite
quasi-compact open cover, and the equivalent affine-local criterion on qcqs schemes.
The coefficients are arbitrary commutative condensed rings and the local models are
finite constant scalar models, as in the recorded constructibility definition.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar upperStarFromPoint
  CondensedRing.upperStarComp CondensedRing.upperStarLowerStarAdjunction

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem model_of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (C.f i)).mapIso e.symm ≪≫ eP⟩⟩

private theorem stratified_of_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun i ↦ model_of_iso Λ
    ((CondensedRing.upperStar Λ (S.immersion i)).mapIso e) (hS i)⟩

private noncomputable def squarePullbackIso {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ D) (d : C ⟶ D)
    (h : a ≫ c = b ≫ d) :
    CondensedRing.upperStar Λ c ⋙ CondensedRing.upperStar Λ a ≅
      CondensedRing.upperStar Λ d ⋙ CondensedRing.upperStar Λ b :=
  (CondensedRing.upperStarComp Λ a c).symm ≪≫
    eqToIso (congrArg (CondensedRing.upperStar Λ) h) ≪≫
    CondensedRing.upperStarComp Λ b d

private theorem model_of_natIso {X Y : Scheme.{u}}
    {F G : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : F ≅ G)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (h : HasFiniteConstantLocalModel Λ X (F.obj M)) :
    HasFiniteConstantLocalModel Λ X (G.obj M) :=
  model_of_iso Λ (e.app M) h

private theorem pullbackStratification_exists {X Y : Scheme.{u}} (g : X ⟶ Y)
    (S : Scheme.Stratification Y) :
    ∃ (T : Scheme.Stratification X) (idx : Fin T.n → Fin S.n)
      (q : ∀ i, T.domain i ⟶ S.domain (idx i)),
      ∀ i, q i ≫ S.immersion (idx i) = T.immersion i ≫ g := by
  exact ⟨S.pullback g, id, fun i ↦ Limits.pullback.fst (S.immersion i) g,
    fun i ↦ Limits.pullback.condition⟩

private theorem stratified_pullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (h : IsFiniteConstantStratified Λ Y M) :
    IsFiniteConstantStratified Λ X ((CondensedRing.upperStar Λ g).obj M) := by
  obtain ⟨S, hS⟩ := h
  obtain ⟨T, idx, q, hq⟩ := pullbackStratification_exists g S
  refine ⟨T, fun i ↦ ?_⟩
  exact model_of_natIso Λ
    (squarePullbackIso Λ (q i) (T.immersion i) (S.immersion (idx i)) g (hq i)) M
    (pullback_finiteConstantLocalModel Λ _ _ (hS (idx i)))

private theorem stratified_of_affine_cover {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (W : Fin n → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
    (hcover : (⋃ i, (W i : Set X)) = Set.univ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ i, IsFiniteConstantStratified Λ (W i).toScheme
      ((CondensedRing.upperStar Λ (W i).ι).obj M)) :
    IsFiniteConstantStratified Λ X M := by
  classical
  obtain ⟨T, hT⟩ := Classical.axiomOfChoice hM
  obtain ⟨S, _, hS⟩ := Scheme.exists_global_stratification_factoring_local
    n W hW hcover T (fun i ↦ (T i).isConstructible_stratum)
  refine ⟨S, fun i ↦ ?_⟩
  obtain ⟨a, b, q, hq⟩ := hS i
  have hcomp := model_of_natIso Λ
    (CondensedRing.upperStarComp Λ ((T a).immersion b) (W a).ι).symm M (hT a b)
  have hp := pullback_finiteConstantLocalModel Λ q _ hcomp
  have hcomp' := model_of_natIso Λ
    (CondensedRing.upperStarComp Λ q ((T a).immersion b ≫ (W a).ι)).symm M hp
  exact model_of_natIso Λ (eqToIso (congrArg (CondensedRing.upperStar Λ) hq)) M hcomp'

private theorem finite_open_subcover {X : Scheme.{u}} [CompactSpace X]
    (V : X → X.Opens) (hx : ∀ x, x ∈ V x) :
    ∃ (n : ℕ) (idx : Fin n → X), (⋃ i, (V (idx i) : Set X)) = Set.univ := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (V x : Set X)) (fun x ↦ (V x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i ↦ (e i).val, Set.eq_univ_of_forall fun x ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨e.symm ⟨a, ha⟩, by simpa using hxa⟩

private theorem finite_affine_subcover_with_property {X : Scheme.{u}} [CompactSpace X]
    (P : X.Opens → Prop)
    (h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ P V) :
    ∃ (n : ℕ) (W : Fin n → X.Opens),
      (∀ i, IsAffineOpen (W i)) ∧ (⋃ i, (W i : Set X)) = Set.univ ∧ ∀ i, P (W i) := by
  classical
  obtain ⟨V, hV⟩ := Classical.axiomOfChoice h
  obtain ⟨n, idx, hcover⟩ := finite_open_subcover V (fun x ↦ (hV x).2.1)
  exact ⟨n, fun i ↦ V (idx i), fun i ↦ (hV (idx i)).1, hcover,
    fun i ↦ (hV (idx i)).2.2⟩

private theorem stratified_of_affine_neighborhoods {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧
      IsFiniteConstantStratified Λ V.toScheme ((CondensedRing.upperStar Λ V.ι).obj M)) :
    IsFiniteConstantStratified Λ X M := by
  classical
  obtain ⟨n, W, hW, hcover, hM⟩ := finite_affine_subcover_with_property
    (fun V ↦ IsFiniteConstantStratified Λ V.toScheme
      ((CondensedRing.upperStar Λ V.ι).obj M)) h
  exact stratified_of_affine_cover Λ n W hW hcover M hM

/-- Finite constant stratified constructibility restricts to quasi-compact opens of
qcqs schemes, glues over finite quasi-compact open covers of qcqs opens, and is
therefore equivalent to the affine-local condition on a qcqs scheme.

Source: Stacks Project, Topology, Tags 005J, 09YD and 053W; Etale Cohomology,
Tag 095E, proof of (2) implies (3); blueprint definition-constructible-sheaves, clause 2
(blueprint: lem-sfb-constructible-zariski-locality).

Proof:
1. An open subscheme of a quasi-separated scheme is quasi-separated: use the affine
   basis (lem-weil-pbc-affine-opens-basis) and both directions of the affine-intersection
   criterion (lem-weil-pbc-quasi-separated-affine-cover-criterion).
2. Pull a witnessing stratification back to the open W using
   lemma-constructible-pullback-stratification. The stratum images are constructible
   by lem-weil-pbc-constructible-open-restriction (005J); the fibre-product square is
   def-pc-fibre-product. Thus these are finite constructible locally closed strata.
3. Pull each finite constant model back along the first projection using
   new-unbounded-pullback-finite-constant-local-model. The composition isomorphisms of
   sk-def-sfb-module-pushforward-pullback identify its restriction with the restriction
   of M to the new stratum. Compose the witnessing model isomorphisms to transfer the
   property definition-constructible-sheaves--1, proving the restriction clause.
4. Refine the finite open cover by affine neighborhoods and extract a finite subcover
   using lem-weil-pbc-affine-opens-basis and def-weil-pbc-quasi-compact-scheme. Each chart
   is qcqs by lem-weil-pbc-affine-scheme-qcqs. Apply the restriction clause on its given
   covering member; successive module restrictions agree by upperStarComp.
5. Apply theorem-comparison-constructible-sheaves to these finite affine-local
   stratifications. Each global stratum factors by an actual scheme morphism through
   one local stratum. Pull back its finite constant model by
   new-unbounded-pullback-finite-constant-local-model and use upperStarComp to obtain
   the required restriction of M. This proves assembly without any Noetherian condition.
6. Restriction gives the forward affine-local implication; a finite affine subcover
   and assembly give the reverse. These are the two readings of definition-constructible-sheaves.
   Empty schemes and the empty cover use the zero-stratum stratification of
   definition-constructible-sheaves--2. Empty strata may remain. The zero module has the
   identity stratum and cover, with the zero scalar module and its rank-zero finite
   presentation in definition-constructible-sheaves--1. -/
theorem finiteConstantStratified_zariski_locality
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (CompactSpace Y → QuasiSeparatedSpace Y → IsFiniteConstantStratified Λ Y M →
      ∀ W : Y.Opens, IsCompact (W : Set Y) →
        IsFiniteConstantStratified Λ W.toScheme ((CondensedRing.upperStar Λ W.ι).obj M)) ∧
    (∀ W : Y.Opens, IsCompact (W : Set Y) → QuasiSeparatedSpace W.toScheme →
      ∀ (r : ℕ) (U : Fin r → W.toScheme.Opens),
        (∀ k : Fin r, IsCompact (U k : Set W.toScheme)) →
        (⋃ k : Fin r, (U k : Set W.toScheme)) = Set.univ →
        (∀ k : Fin r, IsFiniteConstantStratified Λ (U k).toScheme
          ((CondensedRing.upperStar Λ ((U k).ι ≫ W.ι)).obj M)) →
        IsFiniteConstantStratified Λ W.toScheme ((CondensedRing.upperStar Λ W.ι).obj M)) ∧
    (CompactSpace Y → QuasiSeparatedSpace Y →
      (IsFiniteConstantStratified Λ Y M ↔
        ∀ V : Y.Opens, IsAffineOpen V →
          IsFiniteConstantStratified Λ V.toScheme
            ((CondensedRing.upperStar Λ V.ι).obj M))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ h W _
    exact stratified_pullback Λ W.ι M h
  · intro W hW hqs r U _ hcover hU
    let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    let : QuasiSeparatedSpace W.toScheme := hqs
    apply stratified_of_affine_neighborhoods Λ
    intro x
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    obtain ⟨V, hV, hxV, hVU⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.toScheme.isBasis_affineOpens) hxk
    refine ⟨V, hV, hxV, ?_⟩
    have hp := stratified_pullback Λ (W.toScheme.homOfLE hVU) _ (hU k)
    apply stratified_of_iso Λ _ hp
    exact (squarePullbackIso Λ (W.toScheme.homOfLE hVU)
      (Scheme.Opens.ι V) ((U k).ι ≫ W.ι) W.ι
      (by rw [← Category.assoc, Scheme.homOfLE_ι])).app M
  · intro hqc hqs
    let : CompactSpace Y := hqc
    let : QuasiSeparatedSpace Y := hqs
    constructor
    · intro h V _
      exact stratified_pullback Λ V.ι M h
    · intro h
      apply stratified_of_affine_neighborhoods Λ M
      intro x
      obtain ⟨V, hV, hxV, _⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
          (show x ∈ (⊤ : Y.Opens) from trivial)
      exact ⟨V, hV, hxV, h V hV⟩

end AlgebraicGeometry.ProEtale
