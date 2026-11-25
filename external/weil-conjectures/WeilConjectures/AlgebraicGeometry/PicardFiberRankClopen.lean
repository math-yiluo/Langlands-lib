/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField

import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Clopen fibre-rank and empty-fibre loci

Source: Stacks Project, Tag 0BDP, first proof paragraph (rank decomposition).
(blueprint: lem-sc-picard-fiber-rank-clopen).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

-- Use local frames directly; a separate global stalk-rank construction is unnecessary.
private def localRank {X : Scheme.{u}} (E : X.Modules) (r : ℕ) : Set X :=
  {x | ∃ U : X.Opens, x ∈ U ∧ (E.restrict U.ι).IsFiniteLocallyFreeOfRank r}

private theorem rank_unique {X : Scheme.{u}} (E : X.Modules) (r n : ℕ)
    (hr : E.IsFiniteLocallyFreeOfRank r) (hn : E.IsFiniteLocallyFreeOfRank n) (x : X) :
    r = n := by
  have := hr
  have h₁ := Modules.finiteLocallyFreeOfRank_stalk_finrank E r x
  have := hn
  have h₂ := Modules.finiteLocallyFreeOfRank_stalk_finrank E n x
  exact h₁.symm.trans h₂

private theorem rank_restrict_le {X : Scheme.{u}} (E : X.Modules) {U V : X.Opens}
    (h : U ≤ V) (r : ℕ) (hr : (E.restrict V.ι).IsFiniteLocallyFreeOfRank r) :
    (E.restrict U.ι).IsFiniteLocallyFreeOfRank r := by
  have := hr
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (Modules.restrictCompIso E V.ι (X.homOfLE h) U.ι (X.homOfLE_ι h)).symm

private theorem localRank_unique {X : Scheme.{u}} (E : X.Modules) {r n : ℕ}
    {x : X} (hr : x ∈ localRank E r) (hn : x ∈ localRank E n) : r = n := by
  obtain ⟨U, hxU, hr⟩ := hr
  obtain ⟨V, hxV, hn⟩ := hn
  exact rank_unique (E.restrict (U ⊓ V).ι) r n
    (rank_restrict_le E inf_le_left r hr) (rank_restrict_le E inf_le_right n hn)
    ⟨x, hxU, hxV⟩

private theorem exists_localRank {X : Scheme.{u}} (E : X.Modules)
    [E.IsFiniteLocallyFree] (x : X) : ∃ n, x ∈ localRank E n := by
  classical
  obtain ⟨U, I, hI, hx, ⟨e⟩⟩ := Modules.exists_mem_over_iso_free E x
  let n := Fintype.card I
  let e' : E.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin n)) :=
    Modules.overIsoFreeEquiv E U I e ≪≫ SheafOfModules.freeFunctor.mapIso
      ((Fintype.equivFin I).trans Equiv.ulift.symm).toIso
  exact ⟨n, U, hx, SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e'.symm⟩

private theorem localRank_isOpen {X : Scheme.{u}} (E : X.Modules) (r : ℕ) :
    IsOpen (localRank E r) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro x ⟨U, hx, hr⟩
  exact ⟨U, fun y hy ↦ ⟨U, hy, hr⟩, U.isOpen, hx⟩

private theorem localRank_isClopen {X : Scheme.{u}} (E : X.Modules)
    [E.IsFiniteLocallyFree] (r : ℕ) : IsClopen (localRank E r) := by
  classical
  refine ⟨?_, localRank_isOpen E r⟩
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨n, U, hxU, hn⟩ := exists_localRank E x
  refine ⟨U, ?_, U.isOpen, hxU⟩
  intro y hy hyr
  have heq : r = n := localRank_unique E hyr ⟨U, hy, hn⟩
  exact hx (heq.symm ▸ ⟨U, hxU, hn⟩)

-- Restriction and pullback commute by the morphismRestrict square.
private noncomputable def restrictPullbackIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : X.Modules) (U : X.Opens) :
    ((Modules.pullback g).obj E).restrict (g ⁻¹ᵁ U).ι ≅
      (Modules.pullback (g ∣_ U)).obj (E.restrict U.ι) :=
  (Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι).app _ ≪≫
    (Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app E ≪≫
    (Modules.pullbackCongr (morphismRestrict_ι g U).symm).app E ≪≫
    (Modules.pullbackComp (g ∣_ U) U.ι).symm.app E ≪≫
    (Modules.pullback (g ∣_ U)).mapIso ((Modules.restrictFunctorIsoPullback U.ι).symm.app E)

private theorem pullback_rank_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    ((Modules.pullback g).obj E).IsFiniteLocallyFreeOfRank r ↔
      ∀ y : Y, g y ∈ localRank E r := by
  classical
  let N := (Modules.pullback g).obj E
  constructor
  · intro hr y
    have := hr
    obtain ⟨n, U, hyU, hn⟩ := exists_localRank E (g y)
    have := hn
    have hNr : (N.restrict (g ⁻¹ᵁ U).ι).IsFiniteLocallyFreeOfRank r := inferInstance
    have hNn : (N.restrict (g ⁻¹ᵁ U).ι).IsFiniteLocallyFreeOfRank n :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (restrictPullbackIso g E U).symm
    have heq := rank_unique (N.restrict (g ⁻¹ᵁ U).ι) r n hNr hNn ⟨y, hyU⟩
    exact heq.symm ▸ ⟨U, hyU, hn⟩
  · intro h
    choose U hy hr using h
    apply Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top N (fun y ↦ g ⁻¹ᵁ U y)
    · apply eq_top_iff.mpr
      intro y _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hy y⟩
    · intro y
      have := hr y
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        (restrictPullbackIso g E (U y)).symm

private theorem tensorPullback_rank_iff {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    ((Modules.tensorPullback g).obj E).IsFiniteLocallyFreeOfRank r ↔
      ∀ y : Y, g y ∈ localRank E r := by
  let e : Modules.tensorPullback g ≅ Modules.pullback g :=
    (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction g)
  rw [← pullback_rank_iff g E r]
  exact ⟨fun h ↦ by
    have := h
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e.app E), fun h ↦ by
    have := h
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e.app E).symm⟩

/-- The empty-fibre locus and the locus of a prescribed constant fibre rank are clopen.
Empty fibres belong to every fixed-rank locus.
Source: Stacks Project, Tag 0BDP, first proof paragraph; the open-and-closed rank
argument applied without connectedness or surjectivity.
(blueprint: lem-sc-picard-fiber-rank-clopen).

Proof:
1. Finite local freeness gives a locally constant stalk-rank function on X. Its
   rank-r locus A and its complement B are both open and closed. Tensor pullback
   preserves stalk rank, so E on X_s has constant rank r iff X_s avoids B.
2. Flatness and local finite presentation make f an open map. Properness makes it
   a closed map. Thus f(A), f(B), and f(X) are all open and closed; the images of
   A and B may overlap, and no disjointness of their images is needed.
3. The fixed-rank locus is S minus f(B), and the empty-fibre locus is S minus f(X).
   These complements are clopen. For an empty fibre the rank condition is vacuous,
   which accounts for its inclusion even when r is positive. -/
theorem picardFiberRank_clopen {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    IsClopen {s : S | IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u})} ∧
      IsClopen {s : S | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r} := by
  classical
  have hRange : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩
  have hEmpty : {s : S | IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u})} =
      (Set.range f)ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Scheme.isEmpty_pullback_iff,
      range_fromSpecResidueField, Set.disjoint_singleton_right]
  have hBad : IsClopen ((localRank E r)ᶜ) := (localRank_isClopen E r).compl
  have hImage : IsClopen (f '' (localRank E r)ᶜ) :=
    ⟨f.isClosedMap _ hBad.isClosed, f.isOpenMap _ hBad.isOpen⟩
  have hRank : {s : S | SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r} =
        (f '' (localRank E r)ᶜ)ᶜ := by
    ext s
    change _ ↔ s ∉ f '' (localRank E r)ᶜ
    simp only [Set.mem_ofPred_eq]
    rw [tensorPullback_rank_iff]
    constructor
    · intro h hs
      obtain ⟨x, hx, hxs⟩ := hs
      have hxq : x ∈ Set.range (pullback.fst f (S.fromSpecResidueField s)) := by
        rw [Pullback.range_fst, range_fromSpecResidueField]
        exact hxs
      obtain ⟨y, rfl⟩ := hxq
      exact hx (h y)
    · intro h y
      by_contra hy
      apply h
      refine ⟨(pullback.fst f (S.fromSpecResidueField s)) y, hy, ?_⟩
      change f ((pullback.fst f (S.fromSpecResidueField s)) y) = s
      rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
      exact fromSpecResidueField_apply _ _
  rw [hEmpty, hRank]
  exact ⟨hRange.compl, hImage.compl⟩

end AlgebraicGeometry.Scheme
