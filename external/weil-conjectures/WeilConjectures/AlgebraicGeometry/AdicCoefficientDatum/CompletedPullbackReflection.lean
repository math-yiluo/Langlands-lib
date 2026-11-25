/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantPresentationTransport
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction

/-! # Reflection through the specified completed pullback unit -/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem unit_isIso_of_iso
    {C : Type*} [Category C] (G : C ⥤ C) (η : 𝟭 C ⟶ G)
    {X Y : C} (e : X ≅ Y) [IsIso (η.app Y)] : IsIso (η.app X) := by
  have hn := η.naturality e.hom
  dsimp only [Functor.id_map] at hn
  have : IsIso (η.app X ≫ G.map e.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.map e.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotient_reflection (T : Scheme.{t}) :
    (∀ K : d.derived T, d.TowerComplete T
      ((completedRlim T (d.completedRing T)).obj ((completedReductionTower T d).obj K))) ∧
    ∀ (K L : d.derived T), d.TowerComplete T L →
      Function.Bijective (fun a :
        (completedRlim T (d.completedRing T)).obj ((completedReductionTower T d).obj K) ⟶ L ↦
        d.completionUnit T K ≫ a) := by
  classical
  obtain ⟨D⟩ := completed_constant_presentation_transport T d
  let F := D.equivalence.functor
  let J := completedCechTopology T
  let G := ConstantCompletion.completion J A d.ideal true
  let η := ConstantCompletion.completionUnit J A d.ideal true
  let C := completedReductionTower T d ⋙ completedRlim T (d.completedRing T)
  have : IsNoetherianRing A := d.noetherian
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  obtain ⟨_, _, hc, hb, hi⟩ :=
    ConstantCompletion.koszul_quotient_reflector J A d.ideal true r a ha
  have hq (K : d.derived T) : ∃ q : F.obj (C.obj K) ≅ G.obj (F.obj K),
      F.map (d.completionUnit T K) ≫ q.hom = η.app (F.obj K) := by
    obtain ⟨q, hq⟩ := D.quotient K
    refine ⟨q, ?_⟩
    simpa only [completedQuotientCompletionUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, AdicCoefficientDatum.constantRlimAdjunction,
      AdicCoefficientDatum.completionUnit, completedReductionAugmentation] using hq
  have hcomplete (K : d.derived T) :
      d.TowerComplete T K ↔ IsIso (η.app (F.obj K)) := by
    obtain ⟨q, hq⟩ := hq K
    change IsIso (d.completionUnit T K) ↔ _
    rw [← hq]
    constructor
    · intro h
      have := h
      infer_instance
    · intro h
      have := h
      have : IsIso (F.map (d.completionUnit T K)) :=
        IsIso.of_isIso_comp_right _ q.hom
      exact isIso_of_reflects_iso (d.completionUnit T K) F
  constructor
  · intro K
    apply (hcomplete (C.obj K)).mpr
    obtain ⟨q, _⟩ := hq K
    have : IsIso (η.app (G.obj (F.obj K))) := (hi _).mpr (hc _)
    exact unit_isIso_of_iso G η q
  · intro K L hL
    have hL' := (hi _).mp ((hcomplete L).mp hL)
    have hbij := hb (F.obj K) (F.obj L) hL'
    obtain ⟨q, hq⟩ := hq K
    constructor
    · intro a b hab
      apply F.map_injective
      apply (cancel_epi q.inv).mp
      apply hbij.1
      change η.app (F.obj K) ≫ (q.inv ≫ F.map a) =
        η.app (F.obj K) ≫ (q.inv ≫ F.map b)
      rw [← hq]
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, F.map_comp] using
        congrArg F.map hab
    · intro a
      obtain ⟨b, hb⟩ := hbij.2 (F.map a)
      obtain ⟨c, hc⟩ := F.map_surjective (q.hom ≫ b)
      refine ⟨c, F.map_injective ?_⟩
      rw [F.map_comp, hc, ← Category.assoc, hq]
      exact hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed pullback is the reflection of ordinary pullback on every ambient input.
Source: Stacks Tag 099N, proof of (2) and (5), together with Tag 099M;
blueprint completed-exchange coherence, proof steps 1 and 4.
(blueprint: lem-weil-pbc-completed-pullback-reflection).
Proof: take a flat-term K-flat representative of K and form its whole strict quotient
sequence. Tensor balancing identifies its pullback with the quotient sequence of the
ordinary pullback, including all transitions and the augmentation. The Koszul/quotient
comparison identifies its derived inverse limit with the completion reflector. The
map ordinaryToCompleted is the adjunct of that augmentation, so the comparison carries
its unit to the actual reflector unit. The reflector has complete output and gives
bijective precomposition into every complete object. Restriction to constant
coefficients and the complete-category equivalence transport these assertions back
to the completed coefficient category; this uses the unit-preserving comparison,
not an inference from levelwise equalities. The representative K need not be complete. -/
theorem AdicCoefficientDatum.completedPull_reflection {U V : Scheme.{t}} (u : U ⟶ V) :
    (∀ K : d.derived V, d.TowerComplete U ((d.completedPull u).obj K)) ∧
      ∀ (K : d.derived V) (L : d.derived U), d.TowerComplete U L →
        Function.Bijective (fun a : (d.completedPull u).obj K ⟶ L ↦
          d.ordinaryToCompleted u K ≫ a) := by
  let R := completedRlim U (d.completedRing U)
  let τ := stratumReductionIso d u
  have he (K : d.derived V) :
      d.ordinaryToCompleted u K ≫ R.map (τ.hom.app K) =
        d.completionUnit U ((d.pull u).obj K) := by
    unfold AdicCoefficientDatum.ordinaryToCompleted AdicCoefficientDatum.completionUnit
    rw [Category.assoc, ← R.map_comp, Category.assoc,
      stratumReduction_augmentation d u K]
    rw [← Category.assoc, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, Category.id_comp]
    rfl
  have hr := quotient_reflection d U
  constructor
  · intro K
    let e : (d.completedPull u).obj K ≅
        R.obj ((completedReductionTower U d).obj ((d.pull u).obj K)) :=
      R.mapIso (τ.app K)
    change IsIso (d.completionUnit U ((d.completedPull u).obj K))
    have h := hr.1 ((d.pull u).obj K)
    change IsIso (d.completionUnit U (R.obj
      ((completedReductionTower U d).obj ((d.pull u).obj K)))) at h
    -- Completeness is invariant under isomorphism by naturality of its unit.
    let η := completedQuotientCompletionUnit U d
    have hη : IsIso (η.app (R.obj
        ((completedReductionTower U d).obj ((d.pull u).obj K)))) := by
      simpa only [η, completedQuotientCompletionUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, AdicCoefficientDatum.completionUnit,
        AdicCoefficientDatum.constantRlimAdjunction, completedReductionAugmentation] using h
    have hi := unit_isIso_of_iso _ η e
    simpa only [η, completedQuotientCompletionUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, AdicCoefficientDatum.completionUnit,
      AdicCoefficientDatum.constantRlimAdjunction, completedReductionAugmentation] using hi
  · intro K L hL
    let e : (d.completedPull u).obj K ≅
        R.obj ((completedReductionTower U d).obj ((d.pull u).obj K)) :=
      R.mapIso (τ.app K)
    have hb := hr.2 ((d.pull u).obj K) L hL
    constructor
    · intro a b hab
      have hx : e.inv ≫ a = e.inv ≫ b := hb.1 (by
        rw [← he K]
        change (d.ordinaryToCompleted u K ≫ e.hom) ≫ (e.inv ≫ a) =
          (d.ordinaryToCompleted u K ≫ e.hom) ≫ (e.inv ≫ b)
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hab)
      exact (cancel_epi e.inv).mp hx
    · intro a
      obtain ⟨b, hb⟩ := hb.2 a
      refine ⟨e.hom ≫ b, ?_⟩
      change d.ordinaryToCompleted u K ≫ (R.map (τ.hom.app K) ≫ b) = a
      rw [← Category.assoc, he K]
      exact hb

end AlgebraicGeometry.Scheme
