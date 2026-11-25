/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.Mathlib.Topology.Constructible

/-!
# Complementary stratifications of a Noetherian scheme

The output uses the recorded finite locally closed stratification interface and states
constructibility separately. Equality of scheme/morphism dependent pairs records the actual
composites and the given complementary scheme, without replacing either by isomorphic data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem append_complementary_stratum
    {T V W : Scheme.{u}} [IsNoetherian T]
    (h : V ⟶ T) (k : W ⟶ T) [IsImmersion h] [IsImmersion k]
    (hhk : Set.range h = (Set.range k)ᶜ)
    (S : FiniteLocallyClosedStratification V) :
    ∃ (R : FiniteLocallyClosedStratification T) (e : Fin (S.n + 1) ≃ Fin R.n),
      (∀ a : Fin (S.n + 1),
        (⟨R.domain (e a), R.immersion (e a)⟩ : Σ Y : Scheme.{u}, Y ⟶ T) =
          Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ Y : Scheme.{u}, Y ⟶ T)
            (fun b : Fin S.n ↦
              (⟨S.domain b, S.immersion b ≫ h⟩ : Σ Y : Scheme.{u}, Y ⟶ T))
            (⟨W, k⟩ : Σ Y : Scheme.{u}, Y ⟶ T) a) ∧
      (∀ a : Fin R.n, Topology.IsConstructible (R.stratum a)) := by
  let D : Fin (S.n + 1) → Σ Y : Scheme.{u}, Y ⟶ T :=
    Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ Y : Scheme.{u}, Y ⟶ T)
      (fun b ↦ ⟨S.domain b, S.immersion b ≫ h⟩) ⟨W, k⟩
  have hlast : D (Fin.last S.n) = ⟨W, k⟩ := Fin.snoc_last _ _
  have hcast (b : Fin S.n) : D b.castSucc = ⟨S.domain b, S.immersion b ≫ h⟩ :=
    Fin.snoc_castSucc _ _ _
  have himm : ∀ a, IsImmersion (D a).2 := by
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · rw [hlast]
      exact inferInstance
    · have := S.isImmersion b
      rw [hcast]
      exact inferInstance
  have hdisj : Pairwise (Function.onFun Disjoint (fun a ↦ Set.range (D a).2)) := by
    intro a
    refine Fin.lastCases ?_ (fun a ↦ ?_) a
    · intro b
      refine Fin.lastCases ?_ (fun b ↦ ?_) b
      · intro hab
        exact (hab rfl).elim
      · intro _
        change Disjoint (Set.range (D (Fin.last S.n)).2) (Set.range (D b.castSucc).2)
        rw [hlast, hcast]
        apply Set.disjoint_left.mpr
        rintro x hx ⟨z, rfl⟩
        have hz : (S.immersion b ≫ h) z ∈ Set.range h := ⟨S.immersion b z, rfl⟩
        rw [hhk] at hz
        exact hz hx
    · intro b
      refine Fin.lastCases ?_ (fun b ↦ ?_) b
      · intro _
        change Disjoint (Set.range (D a.castSucc).2) (Set.range (D (Fin.last S.n)).2)
        rw [hcast, hlast]
        apply Set.disjoint_left.mpr
        rintro x ⟨z, rfl⟩ hx
        have hz : (S.immersion a ≫ h) z ∈ Set.range h := ⟨S.immersion a z, rfl⟩
        rw [hhk] at hz
        exact hz hx
      · intro hab
        change Disjoint (Set.range (D a.castSucc).2) (Set.range (D b.castSucc).2)
        rw [hcast, hcast]
        apply Set.disjoint_left.mpr
        rintro x ⟨z, rfl⟩ ⟨w, hw⟩
        have he := h.isEmbedding.injective hw
        exact Set.disjoint_left.mp
          (S.pairwise_disjoint_stratum (fun heq ↦ hab (congrArg Fin.castSucc heq)))
          ((S.range_immersion a) ▸ Set.mem_range_self z)
          ((S.range_immersion b) ▸ ⟨w, he⟩)
  let R : FiniteLocallyClosedStratification T :=
    { n := S.n + 1
      stratum := fun a ↦ Set.range (D a).2
      domain := fun a ↦ (D a).1
      immersion := fun a ↦ (D a).2
      isImmersion := himm
      range_immersion := fun _ ↦ rfl
      isLocallyClosed_stratum := fun a ↦ by
        have := himm a
        exact (D a).2.isLocallyClosed_range
      pairwise_disjoint_stratum := hdisj
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro x
        by_cases hx : x ∈ Set.range h
        · obtain ⟨y, rfl⟩ := hx
          have hy : y ∈ ⋃ a, S.stratum a :=
            S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y
          obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy
          rw [← S.range_immersion a] at ha
          obtain ⟨z, rfl⟩ := ha
          refine Set.mem_iUnion.mpr ⟨a.castSucc, ?_⟩
          rw [hcast]
          exact ⟨z, rfl⟩
        · refine Set.mem_iUnion.mpr ⟨Fin.last S.n, ?_⟩
          rw [hlast]
          simpa only [hhk, Set.mem_compl_iff, not_not] using hx }
  exact ⟨R, Equiv.refl _, fun _ ↦ rfl,
    fun a ↦ (R.isLocallyClosed_stratum a).isConstructible_of_noetherianSpace⟩

/-- Complementary open and closed immersions in a Noetherian scheme preserve finite
stratifications when the complementary scheme is adjoined as one stratum. -/
theorem noetherian_complementary_stratifications
    {T U Z : Scheme.{u}} [IsLocallyNoetherian T] [CompactSpace T]
    (j : U ⟶ T) (i : Z ⟶ T) [IsOpenImmersion j] [IsClosedImmersion i]
    (hji : Set.range j = (Set.range i)ᶜ) :
    IsNoetherian T ∧ IsNoetherian U ∧ IsNoetherian Z ∧
    (CompactSpace T ∧ QuasiSeparatedSpace T) ∧
    (CompactSpace U ∧ QuasiSeparatedSpace U) ∧
    (CompactSpace Z ∧ QuasiSeparatedSpace Z) ∧
    (∀ A : Set T, IsCompact A) ∧ QuasiCompact j ∧
    (∀ S : FiniteLocallyClosedStratification U,
      ∃ (R : FiniteLocallyClosedStratification T) (e : Fin (S.n + 1) ≃ Fin R.n),
        (∀ a : Fin (S.n + 1),
          (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ T) =
            Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ T)
              (fun b : Fin S.n ↦
                (⟨S.domain b, S.immersion b ≫ j⟩ : Σ W : Scheme.{u}, W ⟶ T))
              (⟨Z, i⟩ : Σ W : Scheme.{u}, W ⟶ T) a) ∧
        (∀ a : Fin R.n, Topology.IsConstructible (R.stratum a))) ∧
    (∀ S : FiniteLocallyClosedStratification Z,
      ∃ (R : FiniteLocallyClosedStratification T) (e : Fin (S.n + 1) ≃ Fin R.n),
        (∀ a : Fin (S.n + 1),
          (⟨R.domain (e a), R.immersion (e a)⟩ : Σ W : Scheme.{u}, W ⟶ T) =
            Fin.snoc (α := fun _ : Fin (S.n + 1) ↦ Σ W : Scheme.{u}, W ⟶ T)
              (fun b : Fin S.n ↦
                (⟨S.domain b, S.immersion b ≫ i⟩ : Σ W : Scheme.{u}, W ⟶ T))
              (⟨U, j⟩ : Σ W : Scheme.{u}, W ⟶ T) a) ∧
        (∀ a : Fin R.n, Topology.IsConstructible (R.stratum a))) := by
  have : IsNoetherian T := ⟨⟩
  have : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : TopologicalSpace.NoetherianSpace U := j.isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace Z := i.isClosedEmbedding.isInducing.noetherianSpace
  have : IsNoetherian U := ⟨⟩
  have : IsNoetherian Z := ⟨⟩
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance⟩, TopologicalSpace.NoetherianSpace.isCompact, inferInstance,
    append_complementary_stratum j i hji, ?_⟩
  exact append_complementary_stratum i j (by rw [hji, compl_compl])

end AlgebraicGeometry.Scheme
