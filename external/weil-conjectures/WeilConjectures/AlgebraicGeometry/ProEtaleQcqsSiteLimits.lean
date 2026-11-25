/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Site axioms and limits for the qcqs pro-etale subsite

Source: Stacks Project, Tags 09A1 and 098M
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.ProEt

set_option backward.isDefEq.respectTransparency false in
private theorem qcqs_closed_pullbacks (X : Scheme.{u}) :
    (qcqsObjects X).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro P ⟨h⟩
    let F := h.diag
    let c : Cone F := ⟨P, h.π⟩
    let c' := (Cone.postcompose (diagramIsoCospan F).hom).obj c
    have hc' : IsLimit c' := (IsLimit.postcomposeHomEquiv _ c).symm h.isLimit
    have hp := (IsPullback.of_isLimit hc').map (ProEt.forget X ⋙ Over.forget X)
    have : CompactSpace (F.obj WalkingCospan.left).left := (h.prop_diag_obj _).1
    have : QuasiSeparatedSpace (F.obj WalkingCospan.left).left :=
      (h.prop_diag_obj _).2
    have : QuasiSeparatedSpace (F.obj WalkingCospan.one).left :=
      (h.prop_diag_obj _).2
    have : QuasiCompact ((ProEt.forget X ⋙ Over.forget X).map
        (F.map WalkingCospan.Hom.inl)) := by
      change QuasiCompact (F.map WalkingCospan.Hom.inl).left
      infer_instance
    have : QuasiSeparated ((ProEt.forget X ⋙ Over.forget X).map
        (F.map WalkingCospan.Hom.inl)) := by
      change QuasiSeparated (F.map WalkingCospan.Hom.inl).left
      infer_instance
    have : QuasiCompact ((ProEt.forget X ⋙ Over.forget X).map (c'.π.app WalkingCospan.right)) :=
      MorphismProperty.of_isPullback hp inferInstance
    have : QuasiSeparated ((ProEt.forget X ⋙ Over.forget X).map
        (c'.π.app WalkingCospan.right)) :=
      MorphismProperty.of_isPullback hp inferInstance
    exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ _
        ((ProEt.forget X ⋙ Over.forget X).map (c'.π.app WalkingCospan.right))
        ‹_› (h.prop_diag_obj WalkingCospan.right).1,
      @quasiSeparatedSpace_of_quasiSeparated _ _
        ((ProEt.forget X ⋙ Over.forget X).map (c'.π.app WalkingCospan.right))
        (h.prop_diag_obj WalkingCospan.right).2 ‹_›⟩

private theorem qc_mem_of_le {T : Scheme.{u}} {R S : Presieve T}
    (h : R ≤ S) (hR : R ∈ qcPrecoverage T) : S ∈ qcPrecoverage T := by
  have : QuasiCompactCover R.preZeroHypercover :=
    presieve₀_mem_qcPrecoverage_iff.mp (by simpa using hR)
  let φ : R.preZeroHypercover.Hom S.preZeroHypercover :=
    { s₀ := fun i ↦ ⟨i.1, h _ _ i.2⟩
      h₀ := fun _ ↦ 𝟙 _ }
  have : QuasiCompactCover S.preZeroHypercover := QuasiCompactCover.of_hom φ
  simpa using (presieve₀_mem_qcPrecoverage_iff.mpr this)

/-- The qcqs full subcategory is a site for finite pro-etale covers; fibre products,
slice finite limits, and (for qcqs base) finite limits are computed in schemes.
Adjoining finitely many arrows to a cover preserves the covering property.
Source: Stacks Project, Tag 09A1, qcqs subsite paragraph, and Tag 098M.
(auxiliary; not a blueprint node)

Proof plan:
1. Every map between objects is weakly etale (`lemma-stability--5`).
   Weakly etale maps are stable under base change and composition
   (`lem-weil-pbc-weakly-etale-composition-base-change`). A map from a qcqs scheme
   to a qcqs scheme is qcqs, and these properties persist under base change and
   composition (`lem-weil-pbc-qcqs-morphism-permanence`). Thus scheme fibre products
   belong to the full subcategory, and their universal properties restrict to it.
2. Isomorphism covers, finite composites of finite covers, and pullbacks of finite
   covers are covers in the full pro-etale site. Step 1 keeps their sources qcqs.
   This gives a pretopology with exactly the prescribed finite covering presieves,
   and inclusion sends covers to covers. Use the pretopology axioms: the stronger
   precoverage classes also quantify over infinite presentations of finite presieves.
3. Over a qcqs object T, the identity is terminal. Products come from step 1.
   The equalizer of a,b : U → V is U ×_(V ×_T V) V, using (a,b) and the diagonal.
   These universal properties hold in schemes over T. Products and equalizers
   construct all finite limits, including the empty limit T. If X is qcqs, X/X
   itself is terminal, giving finite limits over X in the same way.
4. Additional arrows are weakly etale by the between-objects lemma. The original
   finite affine-open witnesses for the fpqc condition still cover each affine
   open after adjoining arrows; the enlarged index set remains finite.
-/
theorem qcqs_site_limits (X : Scheme.{u}) :
    ∃ h : HasPullbacks (Qcqs X),
    ∃ J : @Pretopology (Qcqs X) inferInstance h,
    J.toPrecoverage = qcqsPrecoverage X ∧
    PreservesLimitsOfShape WalkingCospan (qcqsInclusion X) ∧
    PreservesLimitsOfShape WalkingCospan
      (qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X) ∧
    (∀ (T : Qcqs X) (R : Presieve T), R ∈ qcqsPrecoverage X T →
      R.map (qcqsInclusion X) ∈ precoverage X ((qcqsInclusion X).obj T)) ∧
    (∀ T : Qcqs X, HasFiniteLimits (Over T) ∧
      PreservesFiniteLimits
        (Over.post (X := T) (qcqsInclusion X ⋙ ProEt.forget X) ⋙
          Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T))) ∧
    (CompactSpace X → QuasiSeparatedSpace X →
      HasFiniteLimits (Qcqs X) ∧
        PreservesFiniteLimits (qcqsInclusion X ⋙ ProEt.forget X)) ∧
    (∀ (T : Qcqs X) (R S : Presieve T), R ∈ qcqsPrecoverage X T →
      S ∈ Precoverage.finite (Qcqs X) T → R ⊔ S ∈ qcqsPrecoverage X T) := by
  let := qcqs_closed_pullbacks X
  have h : HasPullbacks (Qcqs X) := inferInstance
  have : (qcqsInclusion X).Full := inferInstanceAs (qcqsObjects X).ι.Full
  have : (qcqsInclusion X).Faithful := inferInstanceAs (qcqsObjects X).ι.Faithful
  have hi : PreservesLimitsOfShape WalkingCospan (qcqsInclusion X) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (qcqsObjects X).ι)
  have hs : PreservesLimitsOfShape WalkingCospan
      (qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X) := inferInstance
  have : (precoverage X).HasIsos := by dsimp [precoverage]; infer_instance
  have : (precoverage X).IsStableUnderComposition := by
    dsimp [precoverage]
    infer_instance
  have : (precoverage X).IsStableUnderBaseChange := by
    dsimp [precoverage]
    infer_instance
  let J := ((precoverage X).comap (qcqsInclusion X)).toPretopology ⊓
    Pretopology.finite (Qcqs X)
  refine ⟨h, J, rfl, hi, hs, ?_, ?_, ?_, ?_⟩
  · intro T R hR
    exact hR.1
  · intro T
    have : HasTerminal (Over T) := Over.over_hasTerminal T
    have hf : HasFiniteLimits (Over T) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    let F := qcqsInclusion X ⋙ ProEt.forget X
    have : PreservesLimitsOfShape WalkingCospan F := inferInstance
    have : PreservesLimitsOfShape WalkingCospan
        (Over.post (X := T) F ⋙ Over.forget (F.obj T)) := by
      rw [Over.post_forget_eq_forget_comp]
      infer_instance
    have : PreservesLimitsOfShape WalkingCospan (Over.post (X := T) F) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget (F.obj T))
    have : PreservesLimit (Functor.empty (Over T)) (Over.post (X := T) F) := by
      apply preservesLimit_of_preserves_limit_cone (Over.mkIdTerminal (X := T))
      refine (isLimitMapConeEmptyConeEquiv (Over.post (X := T) F)
        (Over.mk (𝟙 T))).symm ?_
      change IsTerminal (Over.mk (F.map (𝟙 T)))
      rw [F.map_id]
      exact Over.mkIdTerminal
    have : PreservesLimitsOfShape (Discrete PEmpty) (Over.post (X := T) F) :=
      preservesLimitsOfShape_pempty_of_preservesTerminal _
    have : PreservesFiniteLimits (Over.post (X := T) F) :=
      preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
    have : PreservesFiniteLimits (Over.iteratedSliceForward (F.obj T)) :=
      inferInstanceAs (PreservesFiniteLimits (Over.iteratedSliceEquiv (F.obj T)).functor)
    change HasFiniteLimits (Over T) ∧ PreservesFiniteLimits
      (Over.post (X := T) F ⋙ Over.iteratedSliceForward (F.obj T))
    exact ⟨hf, inferInstance⟩
  · intro hX hX'
    let t : Qcqs X := ⟨ProEt.mk (𝟙 X), hX, hX'⟩
    have ht' : IsTerminal ((qcqsInclusion X).obj t) :=
      MorphismProperty.Over.mkIdTerminal _ _
    have ht : IsTerminal t := ht'.isTerminalOfObj (qcqsInclusion X) t
    have : HasTerminal (Qcqs X) := ht.hasTerminal
    have hf : HasFiniteLimits (Qcqs X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    have : PreservesLimit (Functor.empty (Qcqs X)) (qcqsInclusion X) := by
      apply preservesLimit_of_preserves_limit_cone ht
      exact (isLimitMapConeEmptyConeEquiv _ _).symm ht'
    have : PreservesLimitsOfShape (Discrete PEmpty) (qcqsInclusion X) :=
      preservesLimitsOfShape_pempty_of_preservesTerminal _
    have : PreservesFiniteLimits (qcqsInclusion X) :=
      preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
    exact ⟨hf, inferInstance⟩
  · intro T R S hR hS
    refine ⟨?_, ?_⟩
    · let G := ProEt.forget X ⋙ Over.forget X
      have hR' := hR.1
      change (R.map (qcqsInclusion X)).map G ∈ proetalePrecoverage _ at hR'
      change ((R ⊔ S).map (qcqsInclusion X)).map G ∈ proetalePrecoverage _
      have hle : (R.map (qcqsInclusion X)).map G ≤
          ((R ⊔ S).map (qcqsInclusion X)).map G :=
        Presieve.map_monotone (Presieve.map_monotone le_sup_left)
      refine ⟨qc_mem_of_le hle hR'.1, ?_, ?_⟩
      · intro x
        obtain ⟨Y, f, hf, hx⟩ := hR'.2.1 x
        exact ⟨Y, f, Presieve.map_monotone hle _ _ hf, hx⟩
      · intro Y f hf
        rcases hf with @⟨U, f, hf⟩
        rcases hf with @⟨V, g, hg⟩
        change WeaklyEtale g.hom.left
        have hw : g.hom.left ≫ T.obj.hom = V.obj.hom := by
          simp
        have : WeaklyEtale (g.hom.left ≫ T.obj.hom) := by
          rw [hw]
          infer_instance
        exact WeaklyEtale.of_comp g.hom.left T.obj.hom
    · change (R ⊔ S).uncurry.Finite
      change (R.uncurry ∪ S.uncurry).Finite
      exact hR.2.union hS

end AlgebraicGeometry.Scheme.ProEt
