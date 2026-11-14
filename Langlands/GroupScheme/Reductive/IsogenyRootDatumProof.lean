import Langlands.GroupScheme.Reductive.IsogenyRootDatumStatement
import Langlands.GroupScheme.Reductive.IsogenyRootIndex
import Langlands.GroupScheme.Reductive.IsogenyRootParametrization
import Langlands.GroupScheme.Reductive.IsogenyCorootCompatibility
import Langlands.GroupScheme.Reductive.IsogenyRootDatumKernelComparison

/-! # The actual root-datum comparison for split reductive isogenies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A general isogeny induces the characteristic-power root-datum isogeny
on the actual lattices, with the full centrality and isomorphism comparisons. -/
theorem isogenyRootDatum : IsogenyRootDatumStatement.{u} := by
  classical
  intro k _ G G' hG hG' T T' hT hT'
  let := hT.finite_characterLattice
  let := hT.finite_cocharacterLattice
  let := hT'.finite_characterLattice
  let := hT'.finite_cocharacterLattice
  intro i i' hi hi' φ t hφ hsquare J J' _ _ P P' _ _ hP hP'
  let := hG.isAffineHom
  let := hG'.isAffineHom
  let := hG.smooth
  let := hG'.smooth
  let := hφ.1
  have ht := hφ.isIsogeny_torusRestriction hG hG' hi hi' φ t hsquare
  let e : J ≃ J' := hP.isogenyRootIndexEquiv hP' hG hG' hT hT' hi hi'
    φ hφ t hsquare
  have hfactor (s : J') :
      ∃ n : ℕ, t ≫ P'.root s = ringExpChar k ^ n • P.root (e.symm s) := by
    have h := hP.isogenyRootIndexEquiv_spec hP' hG hG' hT hT' hi hi'
      φ hφ t hsquare (e.symm s)
    change ∃ n : ℕ, t ≫ P'.root (e (e.symm s)) =
      ringExpChar k ^ n • P.root (e.symm s) at h
    simpa only [e.apply_symm_apply] using h
  choose n hn using hfactor
  let q : J' → ℕ := fun s => ringExpChar k ^ n s
  have hq (s : J') : ∃ m : ℕ, q s = ringExpChar k ^ m := ⟨n s, rfl⟩
  have hroot (s : J') : t ≫ P'.root s = (q s : ℤ) • P.root (e.symm s) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hn s
  have hp : ringExpChar k = 1 ∨ Nat.Prime (ringExpChar k) :=
    (expChar_is_prime_or_one k (ringExpChar k)).symm
  let f := hP.rootDatumIsogenyOfRootFactors hP' hT hT' hi'.2.1 ht hsquare
    (ringExpChar k) hp e.symm q hq hroot
  have hmaps := hP.rootDatumIsogenyOfRootFactors_spec hP' hT hT' hi'.2.1 ht hsquare
    (ringExpChar k) hp e.symm q hq hroot
  have hw : ∀ χ : characterLattice T', f.weightMap χ = t ≫ χ := hmaps.1
  have hc : ∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t := hmaps.2
  have hrep : f.IsCentral → ∀ r, ∃ u : LocalSplitCell.Ga k ⟶ G,
      (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy u ∧
      (RelativeRoot.subgroup i' (P'.root (f.indexEquiv.symm r))).IsRepresentedBy
        (u ≫ φ) := by
    intro hf r
    exact hP.exists_rootParametrization_of_exactPullback hP'
      hG hG' hT hT' hi hi' φ t ht hsquare r (f.indexEquiv.symm r)
      (root_pullback_eq_of_central_rootDatumIsogeny f hw hf r)
  exact ⟨ht, f, hw, hc,
    isCentralIsogeny_iff_isCentral_rootDatumIsogeny_of_root_representations
      hG hG' hT hT' hi hi' hP hP' hφ ht hsquare f hw hrep,
    isIso_iff_central_bijective_rootDatumIsogeny_of_root_representations
      hG hG' hT hT' hi hi' hP hP' hφ ht hsquare f hw hrep⟩

end Langlands.GroupScheme
