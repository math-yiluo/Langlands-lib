/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientOriginAffineOpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientOriginOpenCover
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Stratified descent of etale origin in the coefficient universe

Source: Stacks Project, proetale.tex, lemma-compare-constructible (Tag 09AK),
the finite-partition induction after classicality on each stratum is known.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

private abbrev fixedComparison (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

private def fixedComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type (max v (u + 1))) [CommRing A] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, v} (f ≫ g) A ≅
      Scheme.coefficientProEtaleFixedModulePullback.{u, v} g A ⋙
        Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A := by
  let af := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Y) (Scheme.coefficientProEtaleModelTopology X)
  let ag := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} g) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Z) (Scheme.coefficientProEtaleModelTopology Y)
  let ac := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} (f ≫ g)) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Z) (Scheme.coefficientProEtaleModelTopology X)
  let e : Scheme.coefficientProEtaleModelBaseChange.{u, v} g ⋙
      Scheme.coefficientProEtaleModelBaseChange.{u, v} f ≅
        Scheme.coefficientProEtaleModelBaseChange.{u, v} (f ≫ g) :=
    Functor.isoWhiskerLeft AsSmall.down
      (Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm AsSmall.up)
  let i := Functor.sheafPushforwardContinuousComp' (eFG := e) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Z)
    (Scheme.coefficientProEtaleModelTopology Y)
    (Scheme.coefficientProEtaleModelTopology X)
  exact ((conjugateIsoEquiv ac (ag.comp af)).symm i.symm).symm

private def fixedComparisonPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (max v (u + 1))) [CommRing A] :
    fixedComparison Y A ⋙ Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A ≅
      Scheme.coefficientEtaleFixedPullback.{u, v} f A ⋙ fixedComparison X A := by
  let ay := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} Y) (ModuleCat A)
    (Scheme.smallModelComparisonEtaleTopology Y) (Scheme.coefficientProEtaleModelTopology Y)
  let ax := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat A)
    (Scheme.smallModelComparisonEtaleTopology X) (Scheme.coefficientProEtaleModelTopology X)
  let ap := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Y) (Scheme.coefficientProEtaleModelTopology X)
  let ae := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientEtaleBaseChange.{u, v} f) (ModuleCat A)
    (Scheme.smallModelComparisonEtaleTopology Y) (Scheme.smallModelComparisonEtaleTopology X)
  exact (conjugateIsoEquiv (ae.comp ax) (ay.comp ap)).symm (Iso.refl _)

private theorem fixedOrigin_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (max v (u + 1))) [CommRing A]
    {F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat A)}
    (hF : (fixedComparison Y A).essImage F) :
    (fixedComparison X A).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A).obj F) := by
  obtain ⟨G, ⟨e⟩⟩ := hF
  exact ⟨(Scheme.coefficientEtaleFixedPullback.{u, v} f A).obj G,
    ⟨((fixedComparisonPullback f A).app G).symm ≪≫
      (Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A).mapIso e⟩⟩

private theorem fixedOrigin_strata_pullback
    (A : Type (max v (u + 1))) [CommRing A] {X Y : Scheme.{u}}
    (S : Scheme.Stratification X) (g : Y ⟶ X)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X) (ModuleCat A))
    (hS : ∀ k, (fixedComparison (S.domain k) A).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} (S.immersion k) A).obj F))
    (k : Fin S.n) :
    (fixedComparison ((S.pullback g).domain k) A).essImage
      ((Scheme.coefficientProEtaleFixedModulePullback.{u, v}
        ((S.pullback g).immersion k) A).obj
          ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} g A).obj F)) := by
  let e := ((fixedComp (pullback.fst (S.immersion k) g) (S.immersion k) A).app F).symm ≪≫
    eqToIso (congrArg
      (fun m ↦ (Scheme.coefficientProEtaleFixedModulePullback.{u, v} m A).obj F)
      pullback.condition) ≪≫
    (fixedComp (pullback.snd (S.immersion k) g) g A).app F
  exact ((fixedComparison _ A).essImage).prop_of_iso e
    (fixedOrigin_pullback (pullback.fst (S.immersion k) g) A (hS k))

private def eraseEmptyStratum {X : Scheme.{u}} (S : Scheme.Stratification X)
    {n : ℕ} (hn : S.n = n + 1) (k : Fin (n + 1))
    (hk : S.stratum (Fin.cast hn.symm k) = ∅) : Scheme.Stratification X where
  n := n
  stratum i := S.stratum (Fin.cast hn.symm (k.succAbove i))
  isLocallyClosed_stratum i := S.isLocallyClosed_stratum _
  isConstructible_stratum i := S.isConstructible_stratum _
  pairwise_disjoint_stratum a b hab := S.pairwise_disjoint_stratum
    (by
      intro h
      apply hab
      apply k.succAbove_right_injective
      exact Fin.cast_injective hn.symm h)
  iUnion_stratum_eq_univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx : x ∈ ⋃ i, S.stratum i := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hik : Fin.cast hn i ≠ k := by
      intro he
      have hie : i = Fin.cast hn.symm k := by subst he; simp
      rw [hie, hk] at hi
      exact hi
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hik
    refine ⟨j, ?_⟩
    simpa [hj] using hi
  domain i := S.domain (Fin.cast hn.symm (k.succAbove i))
  immersion i := S.immersion (Fin.cast hn.symm (k.succAbove i))
  isImmersion i := S.isImmersion _
  range_immersion i := S.range_immersion _

/-- Etale origin glues across a finite constructible locally closed stratification.
The restrictions may be arbitrary etale inverse images; their models need not be finite.

Source: Stacks Project, Tag 09AK, lemma-compare-constructible, induction step;
blueprint constructible-comparison proof, finite-stratification paragraph
(auxiliary; not a blueprint node).

Proof: etale origin is Zariski local, since the comparison counit can be tested on
an open cover. Induct on the number of strata, simultaneously for all schemes.
Near a point shrink to an affine open where its stratum is closed and has
quasi-compact open complement. Pull back the partition. On the complement the
chosen stratum is empty; remove it and apply induction to the remaining strata.
Comparison commutes with scheme pullback, so all their restricted sheaves still
have etale origin. The chosen closed stratum has etale origin by hypothesis.
The open-closed short exact sequence presents F as an extension of extension by
zero from the complement by closed direct image from the chosen stratum.
Comparison commutes with both operations, and its essential image is closed
under extensions by derived full faithfulness (equivalently, apply the comparison
counit to this sequence and use the short five lemma). Thus F has etale origin on
the affine neighborhood and hence globally. For zero strata the scheme is empty.
A full-image immersion is treated by the closed-immersion argument, without
assuming it is an isomorphism. Transport this argument along the two AsSmall site
equivalences: pullbacks are the stated Kan-extension/sheafification functors by
uniqueness of left adjoints, and all coefficient actions and coverings are retained. -/
theorem coefficientFixed_essImage_of_stratification (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (S : Scheme.Stratification X)
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (hS : ∀ k : Fin S.n,
      (Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallModelComparisonInclusion.{u, v} (S.domain k))
        (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} (S.domain k))
        (Scheme.coefficientProEtaleModelTopology.{u, v} (S.domain k))).essImage
          ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} (S.immersion k) A).obj F)) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage F := by
  classical
  suffices H : ∀ n, ∀ {X : Scheme.{u}} (S : Scheme.Stratification X), S.n = n →
      ∀ (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
        (ModuleCat.{max v (u + 1)} A)),
      (∀ k, (fixedComparison (S.domain k) A).essImage
        ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} (S.immersion k) A).obj F)) →
      (fixedComparison X A).essImage F from H S.n S rfl F hS
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X S hn F hS
    have hloc : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
        (fixedComparison V A).essImage
          ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} V.ι A).obj F) := by
      intro x
      have hx : x ∈ ⋃ k, S.stratum k := by rw [S.iUnion_stratum_eq_univ]; trivial
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      cases n with
      | zero => exact Fin.elim0 (Fin.cast hn k)
      | succ m =>
        obtain ⟨V, hV, hxV, hc, _, hcomp⟩ := exists_affineOpen_closed_stratum X S.n
          S.stratum S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum
          S.isLocallyClosed_stratum S.isConstructible_stratum x k hk
        let T := S.pullback V.ι
        let i := T.immersion k
        have hi : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i
          (by rw [T.range_immersion]; exact hc)
        let U : (V : Scheme.{u}).Opens := ⟨(Set.range i)ᶜ,
          i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
        have hcompact : CompactSpace U := by
          apply isCompact_iff_compactSpace.mp
          change IsCompact ((Set.range i)ᶜ)
          rw [T.range_immersion]
          exact hcomp
        have : IsAffine (V : Scheme.{u}) := hV
        have : QuasiCompact U.ι := inferInstance
        let R := T.pullback U.ι
        have hempty : R.stratum k = ∅ := by
          ext y
          change (U.ι y ∈ T.stratum k) ↔ False
          rw [← T.range_immersion]
          exact ⟨fun hy ↦ y.property hy, False.elim⟩
        let R' := eraseEmptyStratum R hn (Fin.cast hn k) (by simpa using hempty)
        have hR : (fixedComparison U A).essImage
            ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} U.ι A).obj
              ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} V.ι A).obj F)) := by
          apply ih m (Nat.lt_succ_self m) R' rfl
          intro a
          exact fixedOrigin_strata_pullback A T U.ι
            ((Scheme.coefficientProEtaleFixedModulePullback.{u, v} V.ι A).obj F)
            (fixedOrigin_strata_pullback A S V.ι F hS) _
        refine ⟨V, hxV, coefficientFixed_essImage_affine_openClosed A i U.ι
          (by rw [U.range_ι]; rfl) _ ?_ hR⟩
        exact fixedOrigin_strata_pullback A S V.ι F hS k
    choose V hxV hV using hloc
    exact coefficientFixed_essImage_of_openCover X A V (fun x ↦ ⟨x, hxV x⟩) F hV

end AlgebraicGeometry.ProEtale
