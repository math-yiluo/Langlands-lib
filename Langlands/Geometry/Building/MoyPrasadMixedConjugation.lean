import Langlands.Geometry.Building.MoyPrasadRootConjugation

/-! # Root coordinates of mixed doubled-opposite conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- The negative coordinate of an ordinary/doubled-opposite exchange
belongs to the original block at the doubled input depth. -/
theorem mul_double_opposite_mem_block_centralizer_root
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-(2 • a)) r) :
    u * v ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) *
      (centralizerPoints P.i : Set (rationalPoints G)) * rootGroupPoints P.i a := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hneg : ∀ c ∈ relativeRoots P.i, -c ∈ relativeRoots P.i := fun c hc =>
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x hc
  have hna := hneg a ha
  have h2na : 2 • (-a) ∈ relativeRoots P.i := by
    simpa only [smul_neg] using hneg _ h2a
  have hvInv : v⁻¹ ∈ P.filtration x (2 • (-a)) r := by
    simpa only [smul_neg] using (P.filtration x (-(2 • a)) r).inv_mem hv
  have huInv : u⁻¹ ∈ P.filtration x (-(-a)) 0 := by
    simpa only [neg_neg] using (P.filtration x a 0).inv_mem hu
  obtain ⟨w, hw, z, hz, d, hd, heq, -⟩ :=
    P.exists_double_real_depth_factorization hP x hna h2na (r : ℝ) 0
      (by positivity) hvInv huInv
  have hdBlock : d ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) := by
    obtain ⟨d1, hd1, d2, hd2, he⟩ := hd
    refine ⟨d1, ?_, d2, ?_, he⟩
    · simpa only [add_zero] using hd1
    · rw [P.apartment.doubleFiltration_of_mem x (-a) r h2na]
      exact hd2
  have heInv : u * v = d⁻¹ * z⁻¹ * w⁻¹ := by
    calc u * v = (v⁻¹ * u⁻¹)⁻¹ := by group
      _ = (w * z * d)⁻¹ := congrArg Inv.inv heq
      _ = d⁻¹ * z⁻¹ * w⁻¹ := by group
  rw [heInv]
  exact Set.mul_mem_mul (Set.mul_mem_mul
    ((P.filtrationBlockSubgroup hP x r hna).inv_mem hdBlock)
    ((centralizerPoints P.i).inv_mem hz))
    (by
      change w⁻¹ ∈ rootGroupPoints P.i a
      simpa only [neg_neg] using ((P.filtration x (-(-a)) 0).inv_mem hw).1)

/-- For a pure doubled opposite input the positive conjugation coordinate
has the full original depth. -/
theorem conjugate_double_opposite_mem_root_centralizer_block
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-(2 • a)) r) :
    u * v * u⁻¹ ∈
      (rootGroupPoints P.i (-a) : Set (rationalPoints G)) * centralizerPoints P.i *
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  have hblock1 : (1 : rationalPoints G) ∈
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a :=
    ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one _⟩
  have hvA : v ∈ rootGroupPoints P.i (-a) := by
    apply RelativeRoot.double_subgroup_le P.i (-a) (Over.mk (𝟙 _))
    change v ∈ rootGroupPoints P.i (2 • (-a))
    simpa only [smul_neg] using hv.1
  by_cases hu1 : u = 1
  · subst u
    simpa only [one_mul, inv_one, mul_one] using
      (Set.mul_mem_mul (Set.mul_mem_mul hvA (Subgroup.one_mem (centralizerPoints P.i)))
        hblock1)
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hna : -a ∈ relativeRoots P.i :=
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
  have hp1F : p.1 ∈ P.filtration x (-a) (-t) := ⟨hp.1, hp1val.ge⟩
  let n : normalizerPoints P.i := ⟨p.1 * u * p.2, hp.2.2⟩
  have hnflip : weylAction P.i n a = -a :=
    hp.weylAction_eq_neg P.i hT ha.1 hu.1 hu1
  have hnflipNeg : weylAction P.i n (-a) = a := by
    rw [map_neg, hnflip, neg_neg]
  obtain ⟨W, hW⟩ := KPApartmentData.exists_smul_val_eq_vadd n x
  have hWa : eval P.S a W = -2 * t :=
    KPApartmentData.eval_translation_eq_of_factor x ha hna hu.1 hu1 hp.1 hp.2.1
      hp.2.2 hnflip ht hW
  let w : rationalPoints G := (n : rationalPoints G) * v * (n : rationalPoints G)⁻¹
  have hwF : w ∈ P.filtration x (2 • a) ((r : ℝ) + 4 * t) := by
    have h := P.conj_mem_filtration_of_translation x n W hW (-(2 • a)) r hv
    have hn2 : weylAction P.i n (-(2 • a)) = 2 • a := by
      rw [← smul_neg, map_nsmul, hnflipNeg]
    rw [hn2, eval_nsmul_char, hWa] at h
    have he : (r : ℝ) - (2 : ℕ) * (-2 * t) = (r : ℝ) + 4 * t := by
      push_cast
      ring
    rw [he] at h
    exact h
  obtain ⟨b, hb, z, hz, d, hd, heq, -⟩ :=
    P.exists_double_real_depth_factorization hP x ha h2a
      ((r : ℝ) + 4 * t) (-t) (by have : 0 < (r : ℝ) := hr; linarith) hwF hp1F
  have hdBlock : d ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
    obtain ⟨d1, hd1, d2, hd2, he⟩ := hd
    refine ⟨d1, P.apartment.filtration_antitone x a (by linarith) hd1, d2, ?_, he⟩
    rw [P.apartment.doubleFiltration_of_mem x a r h2a]
    exact P.apartment.filtration_antitone x (2 • a) (by linarith) hd2
  have hconj : p.2⁻¹ * v * p.2 = v := by
    have hcomm := P.doubleRootGroupPoints_commute hP hna
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
    ((rootGroupPoints P.i (-a)).mul_mem ((rootGroupPoints P.i (-a)).inv_mem hp.1) hb.1)
    hz) hdBlock

namespace CentralizerFiltration

variable {P} (Zf : P.CentralizerFiltration)

/-- Mixed opposite conjugation has the original full-depth coordinates
once its actual middle coordinate has that depth. -/
def doubleOppositeConjugationCoordinatesOfCentralBound
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i) (r : NNReal) (hr : 0 < r)
    (u : P.filtration x a 0) (v : P.filtration x (-(2 • a)) r)
    (hcentral : ∀ (v' : rationalPoints G), v' ∈ rootGroupPoints P.i (-a) →
      ∀ (z : rationalPoints P.centralizer.Z) (u' : rationalPoints G),
      u' ∈ rootGroupPoints P.i a →
      v' * rationalPoints.map P.centralizer.j z * u' =
        (u : rationalPoints G) * (v : rationalPoints G) → z ∈ Zf.filtration r) :
    {p : P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) ×
        Zf.filtration r × P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints G) *
        rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        (p.2.2 : rationalPoints G) =
          (u : rationalPoints G) * (v : rationalPoints G) * (u : rationalPoints G)⁻¹} := by
  apply Classical.choice
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hna : -a ∈ relativeRoots P.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  have h2na : 2 • (-a) ∈ relativeRoots P.i := by
    have hn := KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x h2a
    simpa only [smul_neg] using hn
  have hvHalf : (v : rationalPoints G) ∈ P.filtration x (-a) (r / 2 : NNReal) := by
    have h := P.apartment.filtration_double_le_half x hna h2na (r : ℝ)
      (by simpa only [smul_neg] using v.property)
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h
  obtain ⟨v', hv', z, -, u', hu', heq⟩ :=
    Zf.exists_rankOne_depth_factorization hZ x ha 0 (r / 2)
      (by simpa only [zero_add] using div_pos hr (by norm_num : (0 : NNReal) < 2))
      u.property hvHalf
  have hz := hcentral v' hv'.1 z u' hu'.1 heq
  have hnegBlock := P.mul_double_opposite_mem_block_centralizer_root hP x ha h2a
    r hr u.property v.property
  obtain ⟨_, ⟨d, hd, c, hc, rfl⟩, w, hw, hnegEq⟩ := hnegBlock
  have huniqueNeg := P.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'.1⟩,
      ⟨rationalPoints.map P.centralizer.j z,
        map_mem_centralizerPoints P.centralizer.isRepresentedBy z⟩, ⟨u', hu'.1⟩))
    (a₂ := (⟨d, P.apartment.filtrationBlock_subset_rootGroupPoints x
      (fun _ => (r : ℝ)) (-a) hd⟩, ⟨c, hc⟩, ⟨w, hw⟩))
    (heq.trans hnegEq.symm)
  have hv'd : v' = d :=
    congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
      rootGroupPoints P.i a => (p.1 : rationalPoints G)) huniqueNeg
  have hposBlock := P.conjugate_double_opposite_mem_root_centralizer_block hP x ha h2a
    r hr u.property v.property
  obtain ⟨_, ⟨n, hn, c', hc', rfl⟩, q, hq, hposEq⟩ := hposBlock
  have hcompare : v' * rationalPoints.map P.centralizer.j z *
      (u' * (u : rationalPoints G)⁻¹) = n * c' * q := by
    rw [← mul_assoc, heq]
    exact hposEq.symm
  have huniquePos := P.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'.1⟩,
      ⟨rationalPoints.map P.centralizer.j z,
        map_mem_centralizerPoints P.centralizer.isRepresentedBy z⟩,
      ⟨u' * (u : rationalPoints G)⁻¹,
        (rootGroupPoints P.i a).mul_mem hu'.1 ((rootGroupPoints P.i a).inv_mem u.property.1)⟩))
    (a₂ := (⟨n, hn⟩, ⟨c', hc'⟩,
      ⟨q, P.apartment.filtrationBlock_subset_rootGroupPoints x (fun _ => (r : ℝ)) a hq⟩))
    hcompare
  have hu'q : u' * (u : rationalPoints G)⁻¹ = q :=
    congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
      rootGroupPoints P.i a => (p.2.2 : rationalPoints G)) huniquePos
  refine ⟨⟨(⟨v', hv'd ▸ hd⟩, ⟨z, hz⟩,
    ⟨u' * (u : rationalPoints G)⁻¹, hu'q ▸ hq⟩), ?_⟩⟩
  change v' * rationalPoints.map P.centralizer.j z * (u' * (u : rationalPoints G)⁻¹) =
    (u : rationalPoints G) * (v : rationalPoints G) * (u : rationalPoints G)⁻¹
  rw [← mul_assoc, heq]

/-- Only the actual middle-coordinate estimate remains for mixed
doubled-opposite conjugation in the original Moy–Prasad subgroup. -/
theorem conjugate_double_opposite_mem_moyPrasad_of_central_bound
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i) (r : NNReal) (hr : 0 < r)
    {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-(2 • a)) r)
    (hcentral : ∀ (v' : rationalPoints G), v' ∈ rootGroupPoints P.i (-a) →
      ∀ (z : rationalPoints P.centralizer.Z) (u' : rationalPoints G),
      u' ∈ rootGroupPoints P.i a →
      v' * rationalPoints.map P.centralizer.j z * u' = u * v → z ∈ Zf.filtration r) :
    u * v * u⁻¹ ∈ Zf.moyPrasad x r := by
  let p := Zf.doubleOppositeConjugationCoordinatesOfCentralBound hP hZ x ha h2a r hr
    ⟨u, hu⟩ ⟨v, hv⟩ hcentral
  rw [← p.property]
  have hna : -a ∈ relativeRoots P.i := by
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  exact (Zf.moyPrasad x r).mul_mem ((Zf.moyPrasad x r).mul_mem
    (Zf.block_subset_moyPrasad x r hna p.val.1.property)
    (Zf.image_le_moyPrasad x r ⟨p.val.2.1, p.val.2.1.property, rfl⟩))
    (Zf.block_subset_moyPrasad x r ha p.val.2.2.property)

end CentralizerFiltration

end Langlands.Geometry.Building.ParahoricBuildingData
