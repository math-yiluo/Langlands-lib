import Langlands.Geometry.Building.MoyPrasadBlockExchange
import Langlands.Geometry.Building.MoyPrasadOrderedEmbedding

/-! # Root conjugation of the original positive-depth subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise TensorProduct commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- V3 on one root direction has only the actual doubled-root output. -/
theorem filtration_same_commutator_le_double
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) (r s : ℝ) :
    ⁅P.filtration x a r, P.filtration x a s⁆ ≤
      P.apartment.doubleFiltration x a (r + s) := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨nu, hnu⟩ := P.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter P.i
  have hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a : Vstar P.S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a) := by
    rcases lt_or_gt_of_ne (hnu a ha) with hn | hp
    · exact KPApartmentData.positiveRoots_nonopposite (-nu)
        ⟨ha, by simpa using neg_pos.mpr hn⟩ ⟨ha, by simpa using neg_pos.mpr hn⟩
    · exact KPApartmentData.positiveRoots_nonopposite nu ⟨ha, hp⟩ ⟨ha, hp⟩
  refine (P.apartment.filtration_commutator_le x ha ha hnon r s).trans ?_
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp => iSup_le fun hq =>
    iSup_le fun hroot => ?_
  have heq : p • a + q • a = (p + q) • a := (add_nsmul a p q).symm
  have hmult := P.apartment.root_multiple_eq_one_or_two
    hP.isAffineRootSystem_extendedAffineRoots hP.derivativeRoots_extendedAffineRoots
    ha (by omega : 0 < p + q) (heq ▸ hroot)
  have hp1 : p = 1 := by omega
  have hq1 : q = 1 := by omega
  subst p; subst q
  simp only [one_smul, Nat.cast_one, one_mul] at hroot ⊢
  have h2a : 2 • a ∈ relativeRoots P.i := by simpa only [two_nsmul] using hroot
  rw [P.apartment.doubleFiltration_of_mem x a (r + s) h2a, two_nsmul]

/-- Ordinary rank-one exchange at arbitrary real depths, keeping its
valuation-preserving central factor. -/
theorem exists_rankOne_real_depth_factorization
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r s : ℝ) (hpos : 0 < r + s) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a r) (hv : v ∈ P.filtration x (-a) s) :
    ∃ v' ∈ P.filtration x (-a) s, ∃ z ∈ centralizerPoints P.i,
      ∃ u' ∈ P.filtration x a r,
        u * v = v' * z * u' ∧ ∀ g, x.val a (z * g * z⁻¹) = x.val a g := by
  by_cases hu1 : u = 1
  · subst u
    exact ⟨v, hv, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp, by simp⟩
  by_cases hv1 : v = 1
  · subst v
    exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, u, hu, by simp, by simp⟩
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hneg : -a ∈ relativeRoots P.i :=
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x ha
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hu.1 hu1
  obtain ⟨t', ht'⟩ := KPApartmentData.exists_val_eq_coe x hneg hv.1 hv1
  have hrt : r ≤ t := by
    have h := hu.2
    rwa [ht, WithTop.coe_le_coe] at h
  have hst : s ≤ t' := by
    have h := hv.2
    rwa [ht', WithTop.coe_le_coe] at h
  obtain ⟨v', hv', z, hz, u', hu', heq, hvt, hut, hzc⟩ :=
    P.apartment.exists_rankOne_factorization hT (hT.finite_relativeRoots P.i)
      (relativeRootsRestrictedCharactersSpan F G P.isConnectedReductive
        P.S P.i P.isMaximalSplitTorus) hrank x ha hneg hu.1 hu1 hv.1 hv1 ht ht'
        (by linarith)
  exact ⟨v', ⟨hv', (WithTop.coe_le_coe.mpr hst).trans hvt⟩,
    z, hz, u', ⟨hu', (WithTop.coe_le_coe.mpr hrt).trans hut⟩, heq, hzc⟩

/-- Real-depth mixed exchange keeps the doubled coordinate at its original
depth and puts the ordinary difference at the sum of the two input depths. -/
theorem exists_double_real_depth_factorization
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (h2a : 2 • a ∈ relativeRoots P.i)
    (r s : ℝ) (hpos : 0 < r / 2 + s) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x (2 • a) r) (hv : v ∈ P.filtration x (-a) s) :
    ∃ v' ∈ P.filtration x (-a) s, ∃ z ∈ centralizerPoints P.i,
      ∃ u' ∈ (P.filtration x a (r + s) : Set (rationalPoints G)) *
          P.filtration x (2 • a) r,
        u * v = v' * z * u' ∧ ∀ g, x.val a (z * g * z⁻¹) = x.val a g := by
  have huA := P.apartment.filtration_double_le_half x ha h2a r hu
  obtain ⟨v', hv', z, hz, u', hu', heq, hzc⟩ :=
    P.exists_rankOne_real_depth_factorization x ha (r / 2) s hpos huA hv
  refine ⟨v', hv', z, hz, u', ?_, heq, hzc⟩
  by_cases hu1 : u = 1
  · have huniq := P.oppositeRootTripleProduct_injective ha
      (a₁ := (⟨v', hv'.1⟩, ⟨z, hz⟩, ⟨u', hu'.1⟩))
      (a₂ := (⟨v, hv.1⟩, 1, 1)) (by simpa [hu1] using heq.symm)
    have hu'1 : u' = 1 :=
      congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
        rootGroupPoints P.i a => (p.2.2 : rationalPoints G)) huniq
    rw [hu'1]
    exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one _⟩
  by_cases hv1 : v = 1
  · have huniq := P.oppositeRootTripleProduct_injective ha
      (a₁ := (⟨v', hv'.1⟩, ⟨z, hz⟩, ⟨u', hu'.1⟩))
      (a₂ := (1, 1, ⟨u, huA.1⟩)) (by simpa [hv1] using heq.symm)
    have hu'u : u' = u :=
      congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
        rootGroupPoints P.i a => (p.2.2 : rationalPoints G)) huniq
    rw [hu'u]
    exact ⟨1, Subgroup.one_mem _, u, hu, one_mul _⟩
  have hneg : -a ∈ relativeRoots P.i := by
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha huA.1 hu1
  obtain ⟨t', ht'⟩ := KPApartmentData.exists_val_eq_coe x hneg hv.1 hv1
  have hrt : r / 2 ≤ t := by
    have h := huA.2
    rwa [ht, WithTop.coe_le_coe] at h
  have hst : s ≤ t' := by
    have h := hv.2
    rwa [ht', WithTop.coe_le_coe] at h
  have hdelta := P.rankOne_double_positive_difference hP x ha h2a hu.1 hu1 hv.1 hv1
    hv'.1 hz hu'.1 heq ht ht' (by linarith)
  have hdeltaF : u' * u⁻¹ ∈ P.filtration x a (r + s) :=
    ⟨(rootGroupPoints P.i a).mul_mem hu'.1 ((rootGroupPoints P.i a).inv_mem huA.1),
      (WithTop.coe_le_coe.mpr (by linarith : r + s ≤ 2 * t + t')).trans hdelta⟩
  exact ⟨u' * u⁻¹, hdeltaF, u, hu, inv_mul_cancel_right _ _⟩

/-- Normalizer conjugation shifts the depth by its actual translation
evaluation in the output direction. -/
theorem conj_mem_filtration_of_translation
    (x : P.Apartment) (n : normalizerPoints P.i) (W : V P.S)
    (hW : n • x.val = W +ᵥ x.val) (a : characterLattice P.S) (s : ℝ)
    {g : rationalPoints G} (hg : g ∈ P.filtration x a s) :
    (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈
      P.filtration x (weylAction P.i n a) (s - eval P.S (weylAction P.i n a) W) := by
  refine ⟨conj_mem_rootGroupPoints n hg.1, ?_⟩
  have hev := congrArg (fun phi : RootFunctionFamily P.S G =>
    phi (weylAction P.i n a) ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹)) hW
  simp only [RootFunctionFamily.smul_apply, weylAction_inv_apply_apply,
    RootFunctionFamily.vadd_apply] at hev
  have hcancel : (n : rationalPoints G)⁻¹ *
      ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) *
        (n : rationalPoints G) = g := by group
  rw [hcancel] at hev
  induction he : x.val (weylAction P.i n a)
      ((n : rationalPoints G) * g * (n : rationalPoints G)⁻¹) using WithTop.recTopCoe with
  | top => exact le_top
  | coe q =>
    have h := hg.2
    rw [hev, he, ← WithTop.coe_add, WithTop.coe_le_coe] at h
    exact WithTop.coe_le_coe.mpr (by linarith)

/-- A centralizer factor preserving the root valuation also preserves its
filtration when conjugating in the inverse direction. -/
theorem inv_conj_mem_filtration_of_preserves
    (x : P.Apartment) (a : characterLattice P.S) {z : rationalPoints G}
    (hz : z ∈ centralizerPoints P.i)
    (hzc : ∀ g, x.val a (z * g * z⁻¹) = x.val a g)
    (r : ℝ) {g : rationalPoints G} (hg : g ∈ P.filtration x a r) :
    z⁻¹ * g * z ∈ P.filtration x a r := by
  let n : normalizerPoints P.i :=
    ⟨z⁻¹, centralizerPoints_le_normalizerPoints P.i ((centralizerPoints P.i).inv_mem hz)⟩
  have hn : weylAction P.i n = 1 :=
    (P.isMaximalSplitTorus.isSplitSubtorus.1.weylAction_eq_one_iff P.i n).mpr
      ((centralizerPoints P.i).inv_mem hz)
  have hroot := conj_mem_rootGroupPoints n hg.1
  rw [hn] at hroot
  change z⁻¹ * g * (z⁻¹)⁻¹ ∈ rootGroupPoints P.i a at hroot
  rw [inv_inv] at hroot
  have hval := hzc (z⁻¹ * g * z)
  have hcancel : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
  rw [hcancel] at hval
  exact ⟨hroot, hval ▸ hg.2⟩

/-- The positive coordinate of conjugating an opposite positive-depth
root element by a depth-zero root element remains in its original block. -/
theorem conjugate_opposite_mem_root_centralizer_block
    (hP : P.SatisfiesApartmentAxioms) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-a) r) :
    u * v * u⁻¹ ∈
      (rootGroupPoints P.i (-a) : Set (rationalPoints G)) * centralizerPoints P.i *
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  have hblock1 : (1 : rationalPoints G) ∈
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a :=
    ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one _⟩
  by_cases hu1 : u = 1
  · subst u
    simpa only [one_mul, inv_one, mul_one] using
      (Set.mul_mem_mul (Set.mul_mem_mul hv.1 (Subgroup.one_mem (centralizerPoints P.i)))
        hblock1)
  by_cases hv1 : v = 1
  · subst v
    simpa only [mul_one, mul_inv_cancel] using
      (show (1 : rationalPoints G) ∈
        (rootGroupPoints P.i (-a) : Set (rationalPoints G)) * centralizerPoints P.i *
          P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a from
        ⟨1, ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one _⟩,
          1, hblock1, mul_one _⟩)
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hT := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hrank := rootRankOneFactorization F G P.isConnectedReductive
    P.S P.i P.isMaximalSplitTorus
  have hneg : ∀ c ∈ relativeRoots P.i, -c ∈ relativeRoots P.i := fun c hc =>
    KPApartmentData.neg_mem_relativeRoots_of_rankOne hT hrank x hc
  have hna := hneg a ha
  obtain ⟨t, ht⟩ := KPApartmentData.exists_val_eq_coe x ha hu.1 hu1
  obtain ⟨t', ht'⟩ := KPApartmentData.exists_val_eq_coe x hna hv.1 hv1
  have ht0 : 0 ≤ t := by
    have h := hu.2
    rwa [ht, WithTop.coe_le_coe] at h
  have hrt' : (r : ℝ) ≤ t' := by
    have h := hv.2
    rwa [ht', WithTop.coe_le_coe] at h
  have hr0 : 0 < (r : ℝ) := hr
  have hsum : 0 < t + t' := by linarith
  obtain ⟨p, hp⟩ := ((hrank a ha u hu.1 hu1).1).exists
  have hp1val : x.val (-a) p.1 = ((-t : ℝ) : WithTop ℝ) := by
    have h := x.isValuation.opposite a ha u hu.1 hu1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rw [ht] at h
    exact withTop_eq_neg_of_add_eq_zero h
  have hp2val : x.val (-a) p.2 = ((-t : ℝ) : WithTop ℝ) := by
    have h := x.isValuation.opposite_snd ha hu.1 hu1 hp.1 hp.2.1 hp.2.2
    rw [ht] at h
    exact withTop_eq_neg_of_add_eq_zero h
  have hp1F : p.1 ∈ P.filtration x (-a) (-t) := ⟨hp.1, hp1val.ge⟩
  have hp2F : p.2⁻¹ ∈ P.filtration x (-a) (-t) :=
    Subgroup.inv_mem _ ⟨hp.2.1, hp2val.ge⟩
  have hvF : v ∈ P.filtration x (-a) t' := ⟨hv.1, ht'.ge⟩
  let n : normalizerPoints P.i := ⟨p.1 * u * p.2, hp.2.2⟩
  have hnflip : weylAction P.i n a = -a :=
    hp.weylAction_eq_neg P.i hT ha.1 hu.1 hu1
  have hnflipNeg : weylAction P.i n (-a) = a := by
    rw [map_neg, hnflip, neg_neg]
  obtain ⟨W, hW⟩ := KPApartmentData.exists_smul_val_eq_vadd n x
  have hWa : eval P.S a W = -2 * t :=
    KPApartmentData.eval_translation_eq_of_factor x ha hna hu.1 hu1 hp.1 hp.2.1
      hp.2.2 hnflip ht hW
  let c : rationalPoints G := v⁻¹ * p.2⁻¹ * v * p.2
  have hc : c ∈ P.apartment.doubleFiltration x (-a) (-t + t') := by
    have h := P.filtration_same_commutator_le_double hP x hna t' (-t)
      (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hvF) hp2F)
    simpa only [commutatorElement_def, inv_inv, add_comm] using h
  let w : rationalPoints G := (n : rationalPoints G) * v * (n : rationalPoints G)⁻¹
  let e : rationalPoints G := (n : rationalPoints G) * c * (n : rationalPoints G)⁻¹
  have hwF : w ∈ P.filtration x a (2 * t + t') := by
    have h := P.conj_mem_filtration_of_translation x n W hW (-a) t' hvF
    rw [hnflipNeg, hWa, show t' - -2 * t = 2 * t + t' by ring] at h
    exact h
  have hexE : ∃ b ∈ P.filtration x (-a) (-t), ∃ z ∈ centralizerPoints P.i,
      ∃ d ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a,
        e * p.1 = b * z * d ∧ ∀ g, x.val a (z * g * z⁻¹) = x.val a g := by
    by_cases h2na : 2 • (-a) ∈ relativeRoots P.i
    · have h2a : 2 • a ∈ relativeRoots P.i := by
        simpa only [smul_neg, neg_neg] using hneg _ h2na
      rw [P.apartment.doubleFiltration_of_mem x (-a) (-t + t') h2na] at hc
      have heF : e ∈ P.filtration x (2 • a) (3 * t + t') := by
        have h := P.conj_mem_filtration_of_translation x n W hW (2 • (-a)) (-t + t') hc
        have hn2 : weylAction P.i n (2 • (-a)) = 2 • a := by
          rw [map_nsmul, hnflipNeg]
        rw [hn2, eval_nsmul_char, hWa] at h
        have heq : (-t + t') - (2 : ℕ) * (-2 * t) = 3 * t + t' := by
          push_cast
          ring
        rw [heq] at h
        exact h
      obtain ⟨b, hb, z, hz, d, hd, heq, hzc⟩ :=
        P.exists_double_real_depth_factorization hP x ha h2a
          (3 * t + t') (-t) (by linarith) heF hp1F
      obtain ⟨d1, hd1, d2, hd2, hdd⟩ := hd
      have hdblock : d ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
        refine ⟨d1, P.apartment.filtration_antitone x a (by linarith) hd1, d2, ?_, hdd⟩
        rw [P.apartment.doubleFiltration_of_mem x a r h2a]
        exact P.apartment.filtration_antitone x (2 • a) (by linarith) hd2
      exact ⟨b, hb, z, hz, d, hdblock, heq, hzc⟩
    · rw [P.apartment.doubleFiltration_of_not_mem x (-a) (-t + t') h2na] at hc
      have hc1 : c = 1 := Subgroup.mem_bot.mp hc
      have he1 : e = 1 := by simp only [e, hc1, mul_one, mul_inv_cancel]
      refine ⟨p.1, hp1F, 1, Subgroup.one_mem _, 1, hblock1, ?_, by simp⟩
      simp only [he1, one_mul, mul_one]
  obtain ⟨b, hb, z1, hz1, d, hd, heE, hzc1⟩ := hexE
  obtain ⟨b', hb', z2, hz2, d', hd', heB, -⟩ :=
    P.exists_rankOne_real_depth_factorization x ha (2 * t + t') (-t)
      (by linarith) hwF hb
  have hdconj : z1⁻¹ * d' * z1 ∈ P.filtration x a r :=
    P.apartment.filtration_antitone x a (by linarith)
      (P.inv_conj_mem_filtration_of_preserves x a hz1 hzc1 (2 * t + t') hd')
  have hlast : z1⁻¹ * d' * z1 * d ∈
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a :=
    (P.filtrationBlockSubgroup hP x r ha).mul_mem
      (P.filtration_le_filtrationBlockSubgroup hP x r ha hdconj) hd
  have heq : u * v * u⁻¹ = (p.1⁻¹ * b') * (z2 * z1) * (z1⁻¹ * d' * z1 * d) := by
    calc u * v * u⁻¹ = p.1⁻¹ * (w * e) * p.1 := by
          dsimp only [w, e, c, n]
          group
      _ = p.1⁻¹ * (w * (e * p.1)) := by group
      _ = p.1⁻¹ * (w * (b * z1 * d)) := by rw [heE]
      _ = p.1⁻¹ * ((w * b) * z1 * d) := by group
      _ = p.1⁻¹ * ((b' * z2 * d') * z1 * d) := by rw [heB]
      _ = (p.1⁻¹ * b') * (z2 * z1) * (z1⁻¹ * d' * z1 * d) := by group
  rw [heq]
  exact Set.mul_mem_mul (Set.mul_mem_mul
    ((rootGroupPoints P.i (-a)).mul_mem ((rootGroupPoints P.i (-a)).inv_mem hp.1) hb'.1)
    ((centralizerPoints P.i).mul_mem hz2 hz1)) hlast

namespace CentralizerFiltration

variable {P} (Zf : P.CentralizerFiltration)

/-- Actual original coordinates for the conjugate of an opposite
positive-depth root element by a depth-zero root element. -/
def rootConjugationMoyPrasadCoordinates
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r)
    (u : P.filtration x a 0) (v : P.filtration x (-a) r) :
    {p : P.filtration x (-a) r × Zf.filtration r ×
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a //
      (p.1 : rationalPoints G) *
        rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        (p.2.2 : rationalPoints G) =
          (u : rationalPoints G) * (v : rationalPoints G) * (u : rationalPoints G)⁻¹} := by
  apply Classical.choice
  obtain ⟨v', hv', z, hz, u', hu', heq⟩ :=
    Zf.exists_rankOne_depth_factorization hZ x ha 0 r (by simpa only [zero_add] using hr)
      u.property v.property
  rw [zero_add] at hz
  have halt := P.conjugate_opposite_mem_root_centralizer_block hP x ha r hr u.property v.property
  obtain ⟨_, ⟨n, hn, c, hc, rfl⟩, q, hq, halt⟩ := halt
  have hcomp : v' * rationalPoints.map P.centralizer.j z *
      (u' * (u : rationalPoints G)⁻¹) = n * c * q := by
    rw [← mul_assoc, heq]
    exact halt.symm
  have hunique := P.oppositeRootTripleProduct_injective ha
    (a₁ := (⟨v', hv'.1⟩,
      ⟨rationalPoints.map P.centralizer.j z,
        map_mem_centralizerPoints P.centralizer.isRepresentedBy z⟩,
      ⟨u' * (u : rationalPoints G)⁻¹,
        (rootGroupPoints P.i a).mul_mem hu'.1 ((rootGroupPoints P.i a).inv_mem u.property.1)⟩))
    (a₂ := (⟨n, hn⟩, ⟨c, hc⟩,
      ⟨q, P.apartment.filtrationBlock_subset_rootGroupPoints x (fun _ => (r : ℝ)) a hq⟩))
    hcomp
  have hlast : u' * (u : rationalPoints G)⁻¹ = q :=
    congrArg (fun p : rootGroupPoints P.i (-a) × centralizerPoints P.i ×
      rootGroupPoints P.i a => (p.2.2 : rationalPoints G)) hunique
  refine ⟨⟨(⟨v', hv'⟩, ⟨z, hz⟩,
    ⟨u' * (u : rationalPoints G)⁻¹, hlast ▸ hq⟩), ?_⟩⟩
  change v' * rationalPoints.map P.centralizer.j z *
      (u' * (u : rationalPoints G)⁻¹) =
    (u : rationalPoints G) * (v : rationalPoints G) * (u : rationalPoints G)⁻¹
  rw [← mul_assoc, heq]

/-- Every retained original block belongs to the defining original
Moy–Prasad subgroup. -/
theorem block_subset_moyPrasad (x : P.Apartment) (r : NNReal)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆ Zf.moyPrasad x r := by
  intro g hg
  have hle : P.apartment.sharpFiltration x (fun _ => (r : ℝ)) ≤ Zf.moyPrasad x r :=
    le_sup_right
  apply hle
  exact le_iSup (fun b : relativeRoots P.i =>
    Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (r : ℝ)) b)) ⟨a, ha⟩
      (Subgroup.subset_closure hg)

/-- Opposite-root conjugation preserves the original positive-depth
Moy–Prasad subgroup, including the required doubled-root factor. -/
theorem conjugate_opposite_mem_moyPrasad
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) {u v : rationalPoints G}
    (hu : u ∈ P.filtration x a 0) (hv : v ∈ P.filtration x (-a) r) :
    u * v * u⁻¹ ∈ Zf.moyPrasad x r := by
  let p := Zf.rootConjugationMoyPrasadCoordinates hP hZ x ha r hr ⟨u, hu⟩ ⟨v, hv⟩
  rw [← p.property]
  have hneg : -a ∈ relativeRoots P.i := by
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  exact (Zf.moyPrasad x r).mul_mem ((Zf.moyPrasad x r).mul_mem
    (Zf.filtration_le_moyPrasad x ⟨-a, hneg⟩ r p.val.1.property)
    (Zf.image_le_moyPrasad x r ⟨p.val.2.1, p.val.2.1.property, rfl⟩))
    (Zf.block_subset_moyPrasad x r ha p.val.2.2.property)

end CentralizerFiltration

end Langlands.Geometry.Building.ParahoricBuildingData
