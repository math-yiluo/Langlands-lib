import Langlands.GroupScheme.Reductive.DominantMultiplePinning
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness

/-! # Positive multiples of dominant characters are realized -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.DominantMultiple

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (p : SplitPinning G)
  {H U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- Every dominant character of a split pinning has a positive multiple realized by a
normalized coordinate, left covariant for the negative dynamic parabolic of a strictly
dominant cocharacter and right invariant under a unipotent group inside its contracting
subgroup. -/
theorem exists_pos_nsmul_mem_realizedSet (nu : cocharacterLattice p.torus)
    (hnu : ∀ a ∈ p.base.support, 0 < latticePairing p.torus (p.rootDatum.root a) nu)
    (i : H ⟶ G) (hi : (Dynamic.parabolic (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom nu ≫ p.inclusion))).IsRepresentedBy i)
    (tH : p.torus.toGrp ⟶ H) (htH : tH ≫ i = p.inclusion)
    (j : U ⟶ G) (hj : SubgroupFunctor.range j ≤
      Dynamic.unipotent (CommGroupScheme.groupHom nu ≫ p.inclusion)) (hU : IsUnipotent U)
    (lam : characterLattice p.torus)
    (hlam : ∀ a ∈ p.base.support,
      0 ≤ latticePairing p.torus lam (p.rootDatum.coroot a)) :
    ∃ n : ℕ, 0 < n ∧ n • lam ∈ realizedSet tH i j := by
  classical
  have : Module.Finite ℤ (characterLattice p.torus) := p.isSplitTorus.finite_characterLattice
  let P := p.rootDatum
  let b := p.base
  let S := realizedSet tH i j
  -- Simple directions.
  have hsimple : ∀ c ∈ b.support, ∃ x ∈ S,
      (∀ a ∈ b.support, a ≠ c → P.toLinearMap x (P.coroot a) = 0) ∧
        0 < P.toLinearMap x (P.coroot c) := by
    intro c hc
    obtain ⟨ν, hνs, d, hd, hνc, hν0⟩ :=
      Langlands.RootDatum.DominantMultiple.exists_simple_dual P b ⟨c, hc⟩
    have hdom : ∀ a ∈ b.support, 0 ≤ latticePairing p.torus (P.root a) ν := by
      intro a ha
      rw [← pairing_eq]
      by_cases hac : a = c
      · subst hac
        rw [hνc]
        exact hd.le
      · rw [hν0 a ha hac]
    have hne : ∃ y : characterLattice p.torus, latticePairing p.torus y ν ≠ 0 :=
      ⟨P.root c, by rw [← pairing_eq]; change P.toLinearMap (P.root c) ν ≠ 0; rw [hνc]; omega⟩
    obtain ⟨x, hxS, hxpos, horth⟩ :=
      exists_mem_realizedSet_pos p nu hnu i hi tH htH j hj hU ν hdom hne
    have hxo : ∀ a ∈ b.support, a ≠ c → P.toLinearMap x (P.coroot a) = 0 := by
      intro a ha hac
      rw [pairing_eq]
      exact horth a (by rw [← pairing_eq]; exact hν0 a ha hac)
    refine ⟨x, hxS, hxo, ?_⟩
    exact Langlands.RootDatum.DominantMultiple.pairing_simple_coroot_pos P b c hc ν hνs hν0
      (by rw [hνc]; exact hd) x hxo
      (by rw [pairing_eq]; exact hxpos)
  choose! σ hσS hσ0 hσpos using hsimple
  -- The central directions.
  let A : AddSubgroup (characterLattice p.torus) :=
    { carrier := {y | y ∈ S ∧ -y ∈ S ∧ ∀ r, P.toLinearMap y (P.coroot r) = 0}
      zero_mem' := ⟨S.zero_mem, by rw [neg_zero]; exact S.zero_mem, fun r => by simp⟩
      add_mem' := by
        rintro y z ⟨hy, hy', hyo⟩ ⟨hz, hz', hzo⟩
        refine ⟨S.add_mem hy hz, ?_, fun r => by simp [hyo r, hzo r]⟩
        rw [neg_add]
        exact S.add_mem hy' hz'
      neg_mem' := by
        rintro y ⟨hy, hy', hyo⟩
        exact ⟨hy', by rw [neg_neg]; exact hy, fun r => by simp [hyo r]⟩ }
  let L : Submodule ℤ (characterLattice p.torus) := A.toIntSubmodule ⊔ P.rootSpan ℤ
  have hL : ∀ n : cocharacterLattice p.torus, (∀ l ∈ L, P.toLinearMap l n = 0) → n = 0 := by
    intro n hn
    by_contra hn0
    have hcent : ∀ r, latticePairing p.torus (P.root r) n = 0 := by
      intro r
      rw [← pairing_eq]
      exact hn _ (Submodule.mem_sup_right (Submodule.subset_span ⟨r, rfl⟩))
    have hne : ∃ y : characterLattice p.torus, latticePairing p.torus y n ≠ 0 := by
      by_contra h
      push Not at h
      apply hn0
      apply P.toLinearMap.flip.toPerfPair.injective
      apply LinearMap.ext
      intro y
      rw [map_zero, LinearMap.zero_apply, LinearMap.toPerfPair_apply, LinearMap.flip_apply,
        pairing_eq, h y]
    obtain ⟨x, hxS, hxS', hxpos, hxo⟩ :=
      exists_neg_mem_realizedSet_of_central p i tH htH j hU n hcent hne
    have hxA : x ∈ A := ⟨hxS, hxS', fun r => by rw [pairing_eq]; exact hxo r⟩
    have h0 := hn x (Submodule.mem_sup_left hxA)
    rw [pairing_eq] at h0
    exact (ne_of_gt hxpos) h0
  have hX0 : ∀ x : characterLattice p.torus,
      (∀ a ∈ b.support, P.toLinearMap x (P.coroot a) = 0) → ∃ m : ℕ, 0 < m ∧ m • x ∈ S := by
    intro x hx
    obtain ⟨m, hm, hmL⟩ :=
      Langlands.RootDatum.DominantMultiple.exists_pos_nsmul_mem_of_orthogonal P L hL x
    obtain ⟨a, haA, r, hr, hsum⟩ := Submodule.mem_sup.mp hmL
    have haA' : a ∈ A := haA
    have hr0 : r = 0 := by
      apply Langlands.RootDatum.DominantMultiple.eq_zero_of_mem_rootSpan P b r hr
      intro c hc
      have hrx : r = m • x - a := by rw [← hsum]; abel
      rw [hrx, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, hx c hc,
        smul_zero, haA'.2.2 c, sub_zero]
    refine ⟨m, hm, ?_⟩
    rw [← hsum, hr0, add_zero]
    exact haA'.1
  exact Langlands.RootDatum.DominantMultiple.exists_pos_nsmul_mem_of_dominant P b S σ hσS
    hσ0 hσpos hX0 lam (fun a ha => by rw [pairing_eq]; exact hlam a ha)

end Langlands.GroupScheme.DominantMultiple
