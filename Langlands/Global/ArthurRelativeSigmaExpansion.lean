import Langlands.Global.ArthurTruncation
import Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport

/-! # The expansion in sigma on the actual standard parabolic indices -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open ArthurRelative

section FixedData

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

local notation "Δ" => simpleFinset ν hG hi
local notation "B₀" => ArthurRelative.base hG hi hν D
local notation "Θ" => standardIndex hG hi ν
local notation "P" => rootPairing hG hi D
local notation "τ" => ArthurRelative.tau hG hi ν D
local notation "τ̂" => ArthurRelative.tauHat hG hi ν D
local notation "σ₀" => ArthurRelative.sigma hG hi ν D

private def rootCharacterEmbedding : RelativeRoot.indivisibleRoots i ↪ characterLattice T :=
  ⟨Subtype.val, Subtype.val_injective⟩

private theorem standardIndex_map_character {S : Finset (characterLattice T)} (hS : S ⊆ Δ) :
    (Θ (S : Set (characterLattice T))).map rootCharacterEmbedding = S := by
  ext a
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ((mem_standardIndex hG hi ν).mp hx).2
  · intro ha
    have hΔ : a ∈ simpleRelativeRoots i ν := (mem_simpleFinset hG hi).mp (hS ha)
    refine ⟨⟨a, simpleRelativeRoots_subset_indivisibleRoots hG hi ν hΔ⟩, ?_, rfl⟩
    exact (mem_standardIndex hG hi ν).mpr ⟨hΔ, ha⟩

private theorem standardIndex_card_sdiff {R S : Finset (characterLattice T)} (hR : R ⊆ Δ)
    (hS : S ⊆ Δ) : (Θ (S : Set (characterLattice T)) \ Θ (R : Set (characterLattice T))).card =
      (S \ R).card := by
  rw [← Finset.card_map (f := rootCharacterEmbedding), Finset.map_sdiff,
    standardIndex_map_character hG hi hS, standardIndex_map_character hG hi hR]

private theorem sum_over_standardIndex {E : Type*} [AddCommMonoid E]
    (S : Finset (characterLattice T)) (hS : S ⊆ Δ)
    (f : Finset (RelativeRoot.indivisibleRoots i) → E) :
    ∑ W ∈ (B₀).support.powerset.filter (Θ (S : Set (characterLattice T)) ⊆ ·), f W =
      ∑ R ∈ (Δ).powerset.filter (S ⊆ ·), f (Θ (R : Set (characterLattice T))) := by
  let valMap := Finset.map (rootCharacterEmbedding (i := i))
  let indexMap (R : Finset (characterLattice T)) := Θ (R : Set (characterLattice T))
  have hval {W : Finset (RelativeRoot.indivisibleRoots i)} (hW : W ⊆ (B₀).support) :
      valMap W ⊆ Δ := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    exact (mem_simpleFinset hG hi).mpr ((mem_support_base hG hi hν D).mp (hW hx))
  have hindex {W : Finset (RelativeRoot.indivisibleRoots i)} (hW : W ⊆ (B₀).support) :
      indexMap (valMap W) = W := by
    apply Finset.map_injective rootCharacterEmbedding
    exact standardIndex_map_character hG hi (hval hW)
  symm
  refine Finset.sum_nbij' indexMap valMap ?_ ?_ ?_ ?_ ?_
  · intro R hR
    obtain ⟨hRΔ, hSR⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (standardIndex_subset_support hG hi D hν _),
      standardIndex_mono hG hi ν (show (S : Set (characterLattice T)) ⊆ R from hSR)⟩
  · intro W hW
    obtain ⟨hWb, hSW⟩ := Finset.mem_filter.mp hW
    have hs : valMap (indexMap S) ⊆ valMap W := Finset.map_subset_map.mpr hSW
    rw [show valMap (indexMap S) = S from standardIndex_map_character hG hi hS] at hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hval (Finset.mem_powerset.mp hWb)), hs⟩
  · intro R hR
    exact standardIndex_map_character hG hi (Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1)
  · intro W hW
    exact hindex (Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1)
  · intro R _
    rfl

include hν in
/-- The defining expansion of sigma, indexed by the actual simple roots. -/
theorem arthurRelative_sigma_eq_sum (R S : Finset (characterLattice T)) (hS : S ⊆ Δ) (H : V T) :
    σ₀ (R : Set (characterLattice T)) (S : Set (characterLattice T)) H =
      ∑ Q ∈ (Δ).powerset.filter (S ⊆ ·),
        (-1 : ℤ) ^ (Q \ S).card * τ (R : Set (characterLattice T)) (Q : Set (characterLattice T)) H *
          τ̂ (Q : Set (characterLattice T)) (simpleRelativeRoots i ν) H := by
  let := finite_indivisibleRoots hG hi
  unfold ArthurRelative.sigma ArthurCombinatorics.sigma
  rw [standardIndex_simpleRelativeRoots hG hi D hν,
    sum_over_standardIndex hG hi hν D S hS]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  have hQΔ := Finset.mem_powerset.mp (Finset.mem_filter.mp hQ).1
  rw [standardIndex_card_sdiff hG hi hS hQΔ]
  unfold ArthurRelative.tau ArthurRelative.tauHat
  rw [standardIndex_simpleRelativeRoots hG hi D hν]

include hν in
/-- Arthur's product expansion (8.2), indexed by the actual standard parabolics. -/
theorem arthurRelative_tau_mul_tauHat_eq_sum_sigma (R S : Finset (characterLattice T))
    (hRS : R ⊆ S) (hS : S ⊆ Δ) (H : V T) :
    τ (R : Set (characterLattice T)) (S : Set (characterLattice T)) H *
        τ̂ (S : Set (characterLattice T)) (simpleRelativeRoots i ν) H =
      ∑ Q ∈ (Δ).powerset.filter (S ⊆ ·), σ₀ (R : Set (characterLattice T)) (Q : Set (characterLattice T)) H := by
  let := finite_indivisibleRoots hG hi
  have h := ArthurCombinatorics.tauTauHatSigmaExpansionStatement P B₀
    (Θ (R : Set (characterLattice T))) (Θ (S : Set (characterLattice T)))
    (standardIndex_mono hG hi ν (show (R : Set (characterLattice T)) ⊆ S from hRS))
    (standardIndex_subset_support hG hi D hν _) (toCorootSpan hG hi D H)
  rw [sum_over_standardIndex hG hi hν D S hS] at h
  simpa only [ArthurRelative.tau, ArthurRelative.tauHat, ArthurRelative.sigma,
    standardIndex_simpleRelativeRoots hG hi D hν] using h

include hν in
/-- The sigma function on the actual parabolic indices is a characteristic function. -/
theorem arthurRelative_sigma_eq_zero_or_one (R S : Finset (characterLattice T))
    (hRS : R ⊆ S) (H : V T) :
    σ₀ (R : Set (characterLattice T)) (S : Set (characterLattice T)) H = 0 ∨
      σ₀ (R : Set (characterLattice T)) (S : Set (characterLattice T)) H = 1 := by
  let := finite_indivisibleRoots hG hi
  unfold ArthurRelative.sigma
  rw [standardIndex_simpleRelativeRoots hG hi D hν]
  exact ArthurCombinatorics.sigma_eq_zero_or_one (b := B₀)
    (standardIndex_mono hG hi ν (show (R : Set (characterLattice T)) ⊆ S from hRS))
    (standardIndex_subset_support hG hi D hν _) Finset.Subset.rfl _

end FixedData

/-- The actual relative chamber expansion in Arthur's functions `sigma`, and
their characteristic value property, on the standard parabolic indices. -/
def ArthurRelativeSigmaExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i),
    IsGenericCocharacter i ν → ∀ D : RelativeRootReflectionData i,
    ∀ (R S : Finset (characterLattice T)), R ⊆ S → S ⊆ simpleFinset ν hG hi → ∀ H : V T,
      let Δ := simpleFinset ν hG hi
      let τ := ArthurRelative.tau hG hi ν D
      let hatTau := ArthurRelative.tauHat hG hi ν D
      let σ₀ := ArthurRelative.sigma hG hi ν D
      (σ₀ (R : Set (characterLattice T)) S H =
        ∑ Q ∈ Δ.powerset.filter (S ⊆ ·), (-1 : ℤ) ^ (Q \ S).card *
          τ (R : Set (characterLattice T)) Q H * hatTau (Q : Set (characterLattice T))
            (simpleRelativeRoots i ν) H) ∧
      (τ (R : Set (characterLattice T)) S H *
          hatTau (S : Set (characterLattice T)) (simpleRelativeRoots i ν) H =
        ∑ Q ∈ Δ.powerset.filter (S ⊆ ·), σ₀ (R : Set (characterLattice T)) Q H) ∧
      (σ₀ (R : Set (characterLattice T)) S H = 0 ∨ σ₀ (R : Set (characterLattice T)) S H = 1)

theorem arthurRelativeSigmaExpansion : ArthurRelativeSigmaExpansionStatement.{u} := by
  intro F _ G _ T i _ ν hG hi hν D R S hRS hS H
  exact ⟨arthurRelative_sigma_eq_sum hG hi hν D R S hS H,
    arthurRelative_tau_mul_tauHat_eq_sum_sigma hG hi hν D R S hRS hS H,
    arthurRelative_sigma_eq_zero_or_one hG hi hν D R S hRS H⟩

end Langlands.Global.ArthurTruncation
