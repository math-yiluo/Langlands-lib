import Langlands.Geometry.Building.IntegerRootConjugation

/-! # Integer-valued mixed doubled-opposite conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- The negative coordinate of an ordinary/doubled-opposite exchange
belongs to the original block at the doubled input depth. -/
theorem mul_double_opposite_mem_block_centralizer_root
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints G}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x (-(2 • a)) r) :
    u * v ∈ B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) *
      (centralizerPoints B.i : Set (rationalPoints G)) * rootGroupPoints B.i a := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization k G B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus
  have hneg : ∀ c ∈ relativeRoots B.i, -c ∈ relativeRoots B.i := fun c hc =>
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x hc
  have hna := hneg a ha
  have h2na : 2 • (-a) ∈ relativeRoots B.i := by
    simpa only [smul_neg] using hneg _ h2a
  have hvInv : v⁻¹ ∈ B.filtration x (2 • (-a)) r := by
    simpa only [smul_neg] using (B.filtration x (-(2 • a)) r).inv_mem hv
  have huInv : u⁻¹ ∈ B.filtration x (-(-a)) 0 := by
    simpa only [neg_neg] using (B.filtration x a 0).inv_mem hu
  obtain ⟨w, hw, z, hz, d, hd, heq, -⟩ :=
    B.exists_double_real_depth_factorization hunit x hna h2na (r : ℝ) 0
      (by positivity) hvInv huInv
  have hdBlock : d ∈ B.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) := by
    obtain ⟨d1, hd1, d2, hd2, he⟩ := hd
    refine ⟨d1, ?_, d2, ?_, he⟩
    · simpa only [add_zero] using hd1
    · rw [B.apartment.doubleFiltration_of_mem x (-a) r h2na]
      exact hd2
  have heInv : u * v = d⁻¹ * z⁻¹ * w⁻¹ := by
    calc u * v = (v⁻¹ * u⁻¹)⁻¹ := by group
      _ = (w * z * d)⁻¹ := congrArg Inv.inv heq
      _ = d⁻¹ * z⁻¹ * w⁻¹ := by group
  rw [heInv]
  exact Set.mul_mem_mul (Set.mul_mem_mul
    ((B.filtrationBlockSubgroup hunit x r hna).inv_mem hdBlock)
    ((centralizerPoints B.i).inv_mem hz))
    (by
      change w⁻¹ ∈ rootGroupPoints B.i a
      simpa only [neg_neg] using ((B.filtration x (-(-a)) 0).inv_mem hw).1)

/-- For a pure doubled opposite input the positive conjugation coordinate
has the full original depth. -/
theorem conjugate_double_opposite_mem_root_centralizer_block
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) (x : B.Apartment)
    {a : characterLattice B.S} (ha : a ∈ relativeRoots B.i)
    (h2a : 2 • a ∈ relativeRoots B.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints G}
    (hu : u ∈ B.filtration x a 0) (hv : v ∈ B.filtration x (-(2 • a)) r) :
    u * v * u⁻¹ ∈
      (rootGroupPoints B.i (-a) : Set (rationalPoints G)) * centralizerPoints B.i *
        B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  have hblock1 : (1 : rationalPoints G) ∈
      B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a :=
    ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one _⟩
  have hvA : v ∈ rootGroupPoints B.i (-a) := by
    apply RelativeRoot.double_subgroup_le B.i (-a) (Over.mk (𝟙 _))
    change v ∈ rootGroupPoints B.i (2 • (-a))
    simpa only [smul_neg] using hv.1
  by_cases hu1 : u = 1
  · subst u
    simpa only [one_mul, inv_one, mul_one] using
      (Set.mul_mem_mul (Set.mul_mem_mul hvA (Subgroup.one_mem (centralizerPoints B.i)))
        hblock1)
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization k G B.isConnectedReductive
    B.S B.i B.isMaximalSplitTorus
  have hna : -a ∈ relativeRoots B.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x ha
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hu.1 hu1
  have ht0 : 0 ≤ t := by
    have h := hu.2
    rwa [ht, WithTop.coe_le_coe] at h
  obtain ⟨p, hp⟩ := ((hrank a ha u hu.1 hu1).1).exists
  have hp1val : x.val (-a) p.1 = ((-t : ℝ) : WithTop ℝ) := by
    have h := x.isValuation.opposite a ha u hu.1 hu1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [ht] at h
    exact withTop_eq_neg_of_add_eq_zero h
  have hp1F : p.1 ∈ B.filtration x (-a) (-t) := ⟨hp.1, hp1val.ge⟩
  let n : normalizerPoints B.i := ⟨p.1 * u * p.2, hp.2.2⟩
  have hnflip : weylAction B.i n a = -a :=
    hp.weylAction_eq_neg B.i hT ha.1 hu.1 hu1
  have : AddMonoidHomClass (characterLattice B.S ≃ₗ[ℤ] characterLattice B.S) _ _ :=
    SemilinearMapClass.instAddMonoidHomClass _
  have hnflipNeg : weylAction B.i n (-a) = a := by
    rw [map_neg, hnflip, neg_neg]
  obtain ⟨W, hW⟩ := KPApartmentData.exists_smul_val_eq_vadd n x
  have hWa : eval B.S a W = -2 * t :=
    KPApartmentData.eval_translation_eq_of_factor x ha hna hu.1 hu1 hp.1 hp.2.1
      hp.2.2 hnflip ht hW
  let w : rationalPoints G := (n : rationalPoints G) * v * (n : rationalPoints G)⁻¹
  have hwF : w ∈ B.filtration x (2 • a) ((r : ℝ) + 4 * t) := by
    have h := B.conj_mem_filtration_of_translation x n W hW (-(2 • a)) r hv
    have hn2 : weylAction B.i n (-(2 • a)) = 2 • a := by
      rw [← smul_neg, map_nsmul, hnflipNeg]
    rw [hn2, eval_nsmul_char, hWa] at h
    have he : (r : ℝ) - (2 : ℕ) * (-2 * t) = (r : ℝ) + 4 * t := by
      push_cast
      ring
    rw [he] at h
    exact h
  obtain ⟨b, hb, z, hz, d, hd, heq, -⟩ :=
    B.exists_double_real_depth_factorization hunit x ha h2a
      ((r : ℝ) + 4 * t) (-t) (by have : 0 < (r : ℝ) := hr; linarith) hwF hp1F
  have hdBlock : d ∈ B.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    obtain ⟨d1, hd1, d2, hd2, he⟩ := hd
    refine ⟨d1, B.apartment.filtration_antitone x a (by linarith) hd1, d2, ?_, he⟩
    rw [B.apartment.doubleFiltration_of_mem x a r h2a]
    exact B.apartment.filtration_antitone x (2 • a) (by linarith) hd2
  have hconj : p.2⁻¹ * v * p.2 = v := by
    have hcomm := B.doubleRootGroupPoints_commute hunit hna
      (by simpa only [smul_neg] using hv.1) hp.2.1
    calc p.2⁻¹ * v * p.2 = p.2⁻¹ * (v * p.2) := by group
      _ = p.2⁻¹ * (p.2 * v) := by rw [hcomm.eq]
      _ = v := inv_mul_cancel_left _ _
  have hcompare : u * v * u⁻¹ = (p.1⁻¹ * b) * z * d := by
    calc u * v * u⁻¹ = p.1⁻¹ * (n : rationalPoints G) * (p.2⁻¹ * v * p.2) *
          (n : rationalPoints G)⁻¹ * p.1 := by dsimp only [n]; group
      _ = p.1⁻¹ * w * p.1 := by rw [hconj]; dsimp only [w]; group
      _ = p.1⁻¹ * (w * p.1) := by group
      _ = p.1⁻¹ * (b * z * d) := by rw [heq]
      _ = (p.1⁻¹ * b) * z * d := by group
  rw [hcompare]
  exact Set.mul_mem_mul (Set.mul_mem_mul
    ((rootGroupPoints B.i (-a)).mul_mem ((rootGroupPoints B.i (-a)).inv_mem hp.1) hb.1)
    hz) hdBlock


end Langlands.Geometry.Building.IntegerValuationBuildingData
