import Langlands.Geometry.Building.GenericChamberNormalizerExchange

/-! # Rank-one multiplication in the sharp chamber normalizer cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The sharp chamber fixer times the actual normalizer times the sharp
chamber fixer, as a subset of the original rational-point group. -/
def sharpChamberNormalizerCover (C : Set D.Apartment) : Set (rationalPoints G) :=
  {g | ∃ p ∈ D.sharpFixer C, ∃ n : normalizerPoints i,
    ∃ q ∈ D.sharpFixer C, g = p * (n : rationalPoints G) * q}

theorem mem_sharpChamberNormalizerCover {C : Set D.Apartment}
    {g : rationalPoints G} :
    g ∈ D.sharpChamberNormalizerCover C ↔
      ∃ p ∈ D.sharpFixer C, ∃ n : normalizerPoints i,
        ∃ q ∈ D.sharpFixer C, g = p * (n : rationalPoints G) * q := Iff.rfl

theorem normalizer_mem_sharpChamberNormalizerCover (C : Set D.Apartment)
    (n : normalizerPoints i) :
    (n : rationalPoints G) ∈ D.sharpChamberNormalizerCover C :=
  ⟨1, one_mem _, n, 1, one_mem _, by simp⟩

theorem mul_mem_sharpChamberNormalizerCover_of_mem_sharpFixer
    {C : Set D.Apartment} {p g : rationalPoints G}
    (hp : p ∈ D.sharpFixer C) (hg : g ∈ D.sharpChamberNormalizerCover C) :
    p * g ∈ D.sharpChamberNormalizerCover C := by
  obtain ⟨a, ha, n, b, hb, rfl⟩ := hg
  exact ⟨p * a, mul_mem hp ha, n, b, hb, by group⟩

theorem mul_mem_sharpChamberNormalizerCover_of_mem_sharpFixer_right
    {C : Set D.Apartment} {p g : rationalPoints G}
    (hg : g ∈ D.sharpChamberNormalizerCover C) (hp : p ∈ D.sharpFixer C) :
    g * p ∈ D.sharpChamberNormalizerCover C := by
  obtain ⟨a, ha, n, b, hb, rfl⟩ := hg
  exact ⟨a, ha, n, b * p, mul_mem hb hp, by group⟩

/-- A nonnegative affine-root group lies in the sharp fixer of the subset. -/
theorem affineRootGroup_le_sharpFixer_of_nonneg
    {C : Set D.Apartment} {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {psi : D.Apartment →ᵃ[ℝ] ℝ} (hpos : ∀ x ∈ C, 0 ≤ psi x) :
    D.affineRootGroup a psi ≤ D.sharpFixer C := by
  intro u hu
  apply D.rootFixer_le_sharpFixer ⟨a, ha⟩ C
  refine D.mem_rootFixer.mpr ⟨D.affineRootGroup_le_rootGroupPoints a psi hu, ?_⟩
  intro x hx
  exact ⟨D.affineRootGroup_le_rootGroupPoints a psi hu,
    le_trans (WithTop.coe_le_coe.mpr (hpos x hx))
      ((Subgroup.mem_iInf.mp hu) x).2⟩

/-- Outside the strict affine-root group every valuation has exactly the
specified affine value. -/
theorem val_eq_of_mem_affineRootGroup_diff
    {a : relativeRoots i} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hwall : psi.linear = rootForm i a)
    {u : rationalPoints G} (hu : u ∈ D.affineRootGroup a psi)
    (hplus : u ∉ D.affineRootGroupPlus a psi) (x : D.Apartment) :
    x.val a u = (psi x : WithTop ℝ) := by
  have hx := (mem_affineRootGroup_iff hwall x).mp hu
  exact le_antisymm (not_lt.mp fun h =>
    hplus ((mem_affineRootGroupPlus_iff hwall x).mpr ⟨hx.1, h⟩)) hx.2

/-- Opposite factors of a wall-depth element lie at the opposite affine depth. -/
theorem oppositeFactors_mem_neg_affineRootGroup_of_mem_diff
    {a : relativeRoots i} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hwall : psi.linear = rootForm i a)
    {u : rationalPoints G} (hu : u ∈ D.affineRootGroup a psi)
    (hplus : u ∉ D.affineRootGroupPlus a psi) (hu1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (a : characterLattice S) u p) :
    p.1 ∈ D.affineRootGroup (-(a : characterLattice S)) (-psi) ∧
      p.2 ∈ D.affineRootGroup (-(a : characterLattice S)) (-psi) := by
  have hu0 := D.affineRootGroup_le_rootGroupPoints a psi hu
  constructor
  · apply Subgroup.mem_iInf.mpr
    intro x
    have h5 := x.isValuation.opposite a a.property u hu0 hu1
      p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [D.val_eq_of_mem_affineRootGroup_diff hwall hu hplus x] at h5
    exact ⟨hp.1, (withTop_eq_neg_of_add_eq_zero h5).ge⟩
  · apply Subgroup.mem_iInf.mpr
    intro x
    have h5 := x.isValuation.opposite_snd a.property hu0 hu1 hp.1 hp.2.1 hp.2.2
    rw [D.val_eq_of_mem_affineRootGroup_diff hwall hu hplus x] at h5
    exact ⟨hp.2.1, (withTop_eq_neg_of_add_eq_zero h5).ge⟩

/-- A simple reflection, followed by its wall root group and any normalizer
point, lies in the original sharp chamber normalizer cover. -/
theorem reflection_wall_mul_normalizer_mem_cover
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {a : relativeRoots i} (hwall : psi.linear = rootForm i a)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v)
    (r : normalizerPoints i)
    (hr : D.normalizerAffineEquiv r = AffineRootSystem.affineReflection psi hv.1)
    (hra : weylAction i r a = -(a : characterLattice S))
    {u : rationalPoints G} (hu : u ∈ D.affineRootGroup a psi)
    (m : normalizerPoints i) :
    (r : rationalPoints G) * u * (m : rationalPoints G) ∈
      D.sharpChamberNormalizerCover C := by
  let hC := hpsi.2.2.1
  have hconj := D.conjugateAffineFunctional_eq_neg_of_reflection r psi hv.1 hr
  have hna : -(a : characterLattice S) ∈ relativeRoots i :=
    hra ▸ weylAction_mapsTo_relativeRoots i r a.property
  have hnegwall := D.conjugateAffineFunctional_linear_eq_rootForm r hwall
  rw [hconj] at hnegwall
  have hnegroot :
      rootForm i ⟨weylAction i r a,
        weylAction_mapsTo_relativeRoots i r a.property⟩ =
        rootForm i ⟨-(a : characterLattice S), hna⟩ :=
    congrArg (rootForm i) (Subtype.ext hra)
  rw [hnegroot] at hnegwall
  rcases hC.mem_positiveRoots_or_mem_negativeRoots
      (D.conjugateAffineFunctional_mem_affineRoots m⁻¹ hpsi.1.1) with hpos | hneg
  · have hq := D.conj_mem_affineRootGroup m⁻¹ hu
    simp only [Subgroup.coe_inv, inv_inv] at hq
    have hqC : (m : rationalPoints G)⁻¹ * u * (m : rationalPoints G) ∈
        D.sharpFixer C := by
      exact D.affineRootGroup_le_sharpFixer_of_nonneg
        (weylAction_mapsTo_relativeRoots i m⁻¹ a.property)
        (fun x hx => (hpos.2 x hx).le) hq
    exact ⟨1, one_mem _, r * m,
      (m : rationalPoints G)⁻¹ * u * (m : rationalPoints G), hqC, by
        simp only [Subgroup.coe_mul]
        group⟩
  · by_cases hplus : u ∈ D.affineRootGroupPlus a psi
    · have hru := D.conj_mem_affineRootGroupPlus r hplus
      rw [hra, hconj] at hru
      have hroot :
          D.rootFixer (-(a : characterLattice S)) C =
            D.affineRootGroupPlus (-(a : characterLattice S)) (-psi) := by
        simpa only [neg_one_smul] using
          D.rootFixer_eq_affineRootGroupPlus_of_neg_smul_simpleAffineRoot hAS4 hpsi
            (by norm_num : (-1 : ℝ) < 0)
            (b := ⟨-(a : characterLattice S), hna⟩)
            (by simpa only [neg_one_smul] using hnegwall)
      have hpC := D.rootFixer_le_sharpFixer ⟨-(a : characterLattice S), hna⟩ C
        (hroot.symm ▸ hru)
      exact ⟨(r : rationalPoints G) * u * (r : rationalPoints G)⁻¹, hpC,
        r * m, 1, one_mem _, by simp only [Subgroup.coe_mul]; group⟩
    · have hu0 := D.affineRootGroup_le_rootGroupPoints a psi hu
      have hu1 : u ≠ 1 := by
        intro h
        subst u
        exact hplus (one_mem _)
      obtain ⟨p, hp⟩ :=
        ((rootRankOneFactorization k G hG S i hi a a.property u hu0 hu1).1).exists
      obtain ⟨hp1, hp2⟩ :=
        D.oppositeFactors_mem_neg_affineRootGroup_of_mem_diff hwall hu hplus hu1 hp
      have hleft := D.conj_mem_affineRootGroup r (inv_mem hp1)
      rw [map_neg, hra, neg_neg, D.conjugateAffineFunctional_neg, hconj, neg_neg]
        at hleft
      have hpC := D.affineRootGroup_le_sharpFixer_of_nonneg a.property
        (fun x hx => (hpsi.1.2 x hx).le) hleft
      have hright := D.conj_mem_affineRootGroup m⁻¹ (inv_mem hp2)
      simp only [Subgroup.coe_inv, inv_inv] at hright
      have hqC : (m : rationalPoints G)⁻¹ * p.2⁻¹ * (m : rationalPoints G) ∈
          D.sharpFixer C := by
        apply D.affineRootGroup_le_sharpFixer_of_nonneg
          (weylAction_mapsTo_relativeRoots i m⁻¹ hna) ?_ hright
        intro x hx
        change 0 ≤ -D.conjugateAffineFunctional m⁻¹ psi x
        exact (neg_pos.mpr (hneg.2 x hx)).le
      refine ⟨(r : rationalPoints G) * p.1⁻¹ * (r : rationalPoints G)⁻¹, hpC,
        r * ⟨p.1 * u * p.2, hp.2.2⟩ * m,
        (m : rationalPoints G)⁻¹ * p.2⁻¹ * (m : rationalPoints G), hqC, ?_⟩
      simp only [Subgroup.coe_mul]
      group

end Langlands.Geometry.Building.KPApartmentData
