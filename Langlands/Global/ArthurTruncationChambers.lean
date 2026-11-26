import Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics
import Langlands.LinearAlgebra.ArthurCombinatoricsLanglandsLemma
import Mathlib.Basic.Complex.Basic

/-! # Chamber identities for Arthur's partial truncation -/

noncomputable section

open CategoryTheory AlgebraicGeometry Finset
open scoped CategoryTheory.MonObj Classical

universe u

namespace Langlands.GroupScheme.ArthurRelative

open RealTorusSpace

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

include hν in
/-- The open simple-root chamber lies in the open chamber defined by the weights. -/
theorem tauHat_ne_zero_of_tau_ne_zero {J L : Set (characterLattice T)}
    (hJL : J ⊆ L) {H : V T}
    (htau : tau hG hi ν D J L H ≠ 0) : tauHat hG hi ν D J L H ≠ 0 := by
  classical
  have := finite_indivisibleRoots hG hi
  let P := rootPairing hG hi D
  let b := base hG hi hν D
  let Θ := standardIndex hG hi ν J
  let Ψ := standardIndex hG hi ν L
  let x := toCorootSpan hG hi D H
  have hsub : Θ ⊆ Ψ := standardIndex_mono hG hi ν hJL
  have hΨ : Ψ ⊆ b.support := standardIndex_subset_support hG hi D hν L
  have hx : ∀ j ∈ Ψ \ Θ, 0 < P.root' j (ArthurCombinatorics.levelProjection P Θ x) := by
    change (if _ then (1 : ℤ) else 0) ≠ 0 at htau
    by_contra hn
    exact htau (ite_eq_right hn)
  change (if _ then (1 : ℤ) else 0) ≠ 0
  rw [ite_eq_left]
  · exact one_ne_zero
  · intro j hj
    obtain ⟨hjΨ, hjΘ⟩ := mem_sdiff.mp hj
    rw [← ArthurCombinatorics.weightCoordinate_levelProjection b hsub hΨ hjΨ hjΘ]
    apply ArthurCombinatorics.weightCoordinate_pos b hΨ hjΨ _ (hx j hj)
    intro l hl
    by_cases hlΘ : l ∈ Θ
    · rw [ArthurCombinatorics.root'_levelProjection_eq_zero b (hsub.trans hΨ) x hlΘ]
    · exact (hx l (mem_sdiff.mpr ⟨hl, hlΘ⟩)).le

private theorem map_standardIndex (S : Finset (characterLattice T))
    (hS : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν) :
    (standardIndex hG hi ν (S : Set (characterLattice T))).map
      (Function.Embedding.subtype (· ∈ RelativeRoot.indivisibleRoots i)) = S := by
  classical
  ext α
  rw [mem_map]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ((mem_standardIndex hG hi ν).mp hβ).2
  · intro hα
    refine ⟨⟨α, simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hS hα)⟩, ?_, rfl⟩
    exact (mem_standardIndex hG hi ν).mpr ⟨hS hα, hα⟩

set_option maxHeartbeats 700000 in
include hν in
/-- The alternating cone identity in Arthur 2005, (8.11), in the simple-root indexing. -/
theorem sum_tauHat_mul_tau {SQ SP : Finset (characterLattice T)}
    (hQP : SQ ⊆ SP) (hSP : (SP : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν) (H : V T) :
    ∑ SR ∈ SP.powerset.filter (SQ ⊆ ·),
      (-1 : ℂ) ^ (SR.card - SQ.card) *
        (tauHat hG hi ν D (SQ : Set (characterLattice T)) (SR : Set (characterLattice T)) H : ℂ) *
        (tau hG hi ν D (SR : Set (characterLattice T)) (SP : Set (characterLattice T)) H : ℂ) =
      if SQ = SP then 1 else 0 := by
  classical
  have := finite_indivisibleRoots hG hi
  let P := rootPairing hG hi D
  let b := base hG hi hν D
  let x := toCorootSpan hG hi D H
  let idx (S : Finset (characterLattice T)) := standardIndex hG hi ν (S : Set (characterLattice T))
  let valEmb := Function.Embedding.subtype (· ∈ RelativeRoot.indivisibleRoots i)
  have hmap {S : Finset (characterLattice T)} (hS : S ⊆ SP) : (idx S).map valEmb = S :=
    map_standardIndex hG hi S (fun _ ha => hSP (hS ha))
  have hidx {A B : Finset (characterLattice T)} (hAB : A ⊆ B) : idx A ⊆ idx B :=
    standardIndex_mono hG hi ν hAB
  have hcard {S : Finset (characterLattice T)} (hS : S ⊆ SP) : (idx S).card = S.card := by
    rw [← card_map (f := valEmb), hmap hS]
  have htop : idx SP ⊆ b.support := standardIndex_subset_support hG hi D hν _
  have hchar (A B : Finset (RelativeRoot.indivisibleRoots i)) :
      ArthurCombinatorics.epsilon P A B (0 : _) * ArthurCombinatorics.phi P A B 0 x =
        (-1 : ℤ) ^ (B \ A).card * ArthurCombinatorics.tauHat P A B x := by
    simp [ArthurCombinatorics.epsilon, ArthurCombinatorics.phi, ArthurCombinatorics.tauHat,
      ArthurCombinatorics.corootValue]
  have hsum := ArthurCombinatorics.langlandsCombinatorial_eq (P := P) (b := b) (idx SQ) 0 x
    (idx SP) (hidx hQP) htop
  simp only [hchar] at hsum
  have hright : (if ∃ j ∈ idx SP \ idx SQ,
          ArthurCombinatorics.corootValue P (idx SQ) 0 j ≤ 0 then (0 : ℤ) else 1) =
      if SQ = SP then 1 else 0 := by
    by_cases he : SQ = SP
    · simp [he]
    · have hn : ¬ idx SP ⊆ idx SQ := by
        intro hs
        have hm := congrArg (fun s => s.map valEmb) (Subset.antisymm (hidx hQP) hs)
        rw [hmap hQP, hmap le_rfl] at hm
        exact he hm
      obtain ⟨j, hjP, hjQ⟩ := not_subset.mp hn
      have hj : ∃ j ∈ idx SP \ idx SQ,
          ArthurCombinatorics.corootValue P (idx SQ) 0 j ≤ 0 :=
        ⟨j, mem_sdiff.mpr ⟨hjP, hjQ⟩, by simp [ArthurCombinatorics.corootValue]⟩
      rw [ite_eq_left hj, ite_eq_right he]
  rw [hright] at hsum
  have hreindex : (∑ SR ∈ SP.powerset.filter (SQ ⊆ ·),
      (-1 : ℤ) ^ (SR.card - SQ.card) * tauHat hG hi ν D (SQ : Set _) (SR : Set _) H *
        tau hG hi ν D (SR : Set _) (SP : Set _) H) =
      ∑ R ∈ (idx SP).powerset.filter (idx SQ ⊆ ·),
        (-1 : ℤ) ^ (R \ idx SQ).card * ArthurCombinatorics.tauHat P (idx SQ) R x *
          ArthurCombinatorics.tau P R (idx SP) x := by
    apply sum_bij (fun SR _ => idx SR)
    · intro SR hSR
      rcases mem_filter.mp hSR with ⟨hSR, hQR⟩
      exact mem_filter.mpr ⟨mem_powerset.mpr (hidx (mem_powerset.mp hSR)), hidx hQR⟩
    · intro R hR R' hR' he
      have hm := congrArg (fun s => s.map valEmb) he
      rwa [hmap (mem_powerset.mp (mem_filter.mp hR).1),
        hmap (mem_powerset.mp (mem_filter.mp hR').1)] at hm
    · intro R hR
      obtain ⟨hRP, hQR⟩ := mem_filter.mp hR
      have hRP := mem_powerset.mp hRP
      let SR := R.map valEmb
      have hSR : SR ⊆ SP := by
        rw [← hmap le_rfl]
        exact map_subset_map.mpr hRP
      have hQSR : SQ ⊆ SR := by
        rw [← hmap hQP]
        exact map_subset_map.mpr hQR
      exact ⟨SR, mem_filter.mpr ⟨mem_powerset.mpr hSR, hQSR⟩,
        map_injective (f := valEmb) (hmap hSR)⟩
    · intro R hR
      obtain ⟨hRP, hQR⟩ := mem_filter.mp hR
      have hRP := mem_powerset.mp hRP
      rw [card_sdiff_of_subset (hidx hQR), hcard hRP, hcard hQP]
      rfl
  have hZ := hreindex.trans hsum
  exact_mod_cast hZ

end Langlands.GroupScheme.ArthurRelative
