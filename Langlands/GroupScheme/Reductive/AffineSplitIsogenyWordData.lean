import Langlands.GroupScheme.Reductive.AffineSplitIsogenyWeylMap
import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly

/-! # Compatible descending simple words for a root-datum isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {I I' J J' : Type u} [Fintype I] [Fintype I'] [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)

/-- Corresponding roots have Cartan pairings with the same sign. -/
theorem pairing_pos_iff (a c : J') :
    0 < P.pairing (f.indexEquiv a) (f.indexEquiv c) ↔ 0 < Q.pairing a c := by
  have h := f.pairing_apply (Q.root a) (P.coroot (f.indexEquiv c))
  rw [f.root_weightMap, f.coroot_coweightMap] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    RootPairing.root_coroot_eq_pairing] at h
  have ha : 0 < (f.rootFactor a : ℤ) := by exact_mod_cast f.rootFactor_pos a
  have hc : 0 < (f.rootFactor c : ℤ) := by exact_mod_cast f.rootFactor_pos c
  constructor
  · intro hp
    have hh := mul_pos ha hp
    rw [h] at hh
    exact (mul_pos_iff_of_pos_left hc).mp hh
  · intro hq
    have hh := mul_pos hc hq
    rw [← h] at hh
    exact (mul_pos_iff_of_pos_left ha).mp hh

variable {b : P.Base} {b' : Q.Base}

/-- A complete target family of simple words, obtained by transporting the source words. -/
def targetSimpleWords
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (α' : J') : SimpleWord Q b' α' where
  simple := f.indexEquiv.symm (W (f.indexEquiv α')).simple
  simple_mem := hb _ (W (f.indexEquiv α')).simple_mem
  word := (W (f.indexEquiv α')).word.map f.indexEquiv.symm
  word_mem := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact hb c ((W (f.indexEquiv α')).word_mem c hc)
  root_eq := by
    have h := (transportSimpleWord f hb (W (f.indexEquiv α'))).root_eq
    simpa only [transportSimpleWord, Equiv.symm_apply_apply] using h

/-- The target word maps already constructed are the usual Weyl family for these words. -/
theorem targetWordFamily_eq_weylFamily
    {R : Type u} [CommRing R] {H : GroupScheme (Spec (CommRingCat.of R))}
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
    (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H)) :
    targetWordFamily f W u' = weylFamily Q (targetSimpleWords f hb W) u' := rfl

/-- Descending source words remain descending under corresponding positive systems. -/
theorem isDescendingWords_targetSimpleWords
    (hsupp : ∀ a', f.indexEquiv a' ∈ b.support ↔ a' ∈ b'.support)
    (hpos : ∀ a', b.IsPos (f.indexEquiv a') ↔ b'.IsPos a')
    (W : ∀ α, SimpleWord P b α) (hW : IsDescendingWords P b W) :
    IsDescendingWords Q b'
      (targetSimpleWords f (fun a ha => (hsupp _).mp (by simpa only
        [Equiv.apply_symm_apply] using ha)) W) := by
  let hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support :=
    fun a ha => (hsupp _).mp (by simpa only [Equiv.apply_symm_apply] using ha)
  change IsDescendingWords Q b' (targetSimpleWords f hb W)
  refine ⟨?_, ?_, ?_⟩
  · intro a' ha'
    obtain ⟨hs, hw⟩ := hW.1 _ ((hsupp a').mpr ha')
    simp only [targetSimpleWords, hs, hw, List.map_nil, Equiv.symm_apply_apply, and_self]
  · intro α' hp' hn'
    have hp := (hpos α').mpr hp'
    have hn : f.indexEquiv α' ∉ b.support := fun h => hn' ((hsupp α').mp h)
    obtain ⟨c, hc, hpair, hs, hw⟩ := hW.2.1 _ hp hn
    refine ⟨f.indexEquiv.symm c, hb c hc, ?_, ?_, ?_⟩
    · apply (pairing_pos_iff f α' (f.indexEquiv.symm c)).mp
      simpa only [Equiv.apply_symm_apply] using hpair
    · change f.indexEquiv.symm (W (f.indexEquiv α')).simple =
        f.indexEquiv.symm
          (W (f.indexEquiv (Q.reflectionPerm (f.indexEquiv.symm c) α'))).simple
      rw [f.indexEquiv_reflectionPerm, f.indexEquiv.apply_symm_apply]
      exact congrArg f.indexEquiv.symm hs
    · change (W (f.indexEquiv α')).word.map f.indexEquiv.symm =
        f.indexEquiv.symm c ::
          (W (f.indexEquiv (Q.reflectionPerm (f.indexEquiv.symm c) α'))).word.map
            f.indexEquiv.symm
      rw [f.indexEquiv_reflectionPerm, f.indexEquiv.apply_symm_apply, hw, List.map_cons]
  · intro α' hn'
    have hn : ¬ b.IsPos (f.indexEquiv α') := fun h => hn' ((hpos α').mp h)
    obtain ⟨hs, hw⟩ := hW.2.2 _ hn
    constructor
    · change f.indexEquiv.symm (W (f.indexEquiv α')).simple =
        f.indexEquiv.symm (W (f.indexEquiv (Q.reflectionPerm α' α'))).simple
      rw [f.indexEquiv_reflectionPerm]
      exact congrArg f.indexEquiv.symm hs
    · change (W (f.indexEquiv α')).word.map f.indexEquiv.symm =
        (W (f.indexEquiv (Q.reflectionPerm α' α'))).word.map f.indexEquiv.symm ++
          [f.indexEquiv.symm (W (f.indexEquiv (Q.reflectionPerm α' α'))).simple]
      rw [f.indexEquiv_reflectionPerm, hw, List.map_append, List.map_cons, List.map_nil]

end Langlands.GroupScheme.AffineRootDatumIsogeny
