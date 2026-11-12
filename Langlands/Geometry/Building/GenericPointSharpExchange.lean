import Langlands.Geometry.Building.RootGroupZeroFixer
import Langlands.Geometry.Building.RootFixerExchange
import Langlands.GroupScheme.Rational.RootRayFromFactorPairs
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan

/-!
# Point exchange and unipotent stabilizers for apartment data over any field

The published `PointSharpExchange` and `RootGroupZeroFixer` work with building data over a
nonarchimedean local field satisfying the apartment axioms. Their arguments only use the
valuation axioms of the root-function family, opposite factor pairs, and the ray property of
proportional roots. This module repeats them for arbitrary apartment data
`D : KPApartmentData i ω` over any field, for a maximal split torus `i` of a connected
reductive group, without apartment axioms.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}

open RootReflectionProof in
/-- AS 1 for apartment data over any field (KP Proposition 6.2.1, fixed-point form): the
element `m(u) = p₁ u p₂` of an opposite factor pair fixes every point at which `u` has
value zero. -/
theorem smul_eq_self_of_val_eq_zero [Smooth G.X.hom] (D : KPApartmentData i ω)
    (hS : IsSplitTorus S.toGrp) {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints i a) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G} (hp : RelativeRoot.IsOppositeFactorPair i a u p)
    {x : D.Apartment} (hx : x.val a u = 0) :
    (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x = x := by
  have hfin := hS.finite_relativeRoots i
  have ha0 : a ≠ 0 := ha.1
  set m : normalizerPoints i := ⟨p.1 * u * p.2, hp.2.2⟩ with hm_def
  have hmG : (m : rationalPoints G) = p.1 * u * p.2 := rfl
  have hφ := x.isValuation
  obtain ⟨v, hv⟩ := D.equipollent_of_mem x.mem (m • x).mem
  rw [KPApartmentData.val_smul] at hv
  obtain ⟨hν, hr⟩ := hp.coroot_spec i hS ha0 hu h1
  set ν := hp.coroot i hS ha0 hu h1 with hν_def
  have hr' : ∀ χ, weylAction i m χ = χ - latticePairing S χ ν • a := hr
  have h2 : ∀ χ, weylAction i m (weylAction i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction i m⁻¹ χ = χ - latticePairing S χ ν • a := by
    intro χ
    calc weylAction i m⁻¹ χ = weylAction i m⁻¹ (weylAction i m (weylAction i m χ)) := by
          rw [h2]
      _ = weylAction i m χ := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one,
            id]
      _ = _ := hr' χ
  have hma : weylAction i m a = -a := by
    rw [hr', hν, show a - (2 : ℤ) • a = -a by module]
  have hmna : weylAction i m⁻¹ (-a) = a := by
    rw [hinv, map_neg, LinearMap.neg_apply, hν, show -a - (-2 : ℤ) • a = a by module]
  have hna : -a ∈ relativeRoots i := hma ▸ weylAction_mapsTo_relativeRoots i m ha
  have hu0 : x.val a u = 0 := hx
  have hp1 : x.val (-a) p.1 = 0 := by
    have := hφ.opposite a ha u hu h1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rwa [hu0, add_zero] at this
  have hminv : p.2⁻¹ * u⁻¹ * p.1⁻¹ ∈ normalizerPoints i := by
    have : p.2⁻¹ * u⁻¹ * p.1⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2 : x.val (-a) p.2 = 0 := by
    have := hφ.opposite a ha u⁻¹ (inv_mem hu) (inv_ne_one.2 h1) p.2⁻¹ (inv_mem hp.2.1)
      p.1⁻¹ (inv_mem hp.1) hminv
    rwa [apply_inv hφ, apply_inv hφ, hu0, add_zero] at this
  have hmc : (m : rationalPoints G) ∈
      Subgroup.closure (rootFiltration i x.val a 0 ∪ rootFiltration i x.val (-a) 0) := by
    rw [hmG]
    refine mul_mem (mul_mem (Subgroup.subset_closure (Or.inr ⟨hp.1, ?_⟩))
      (Subgroup.subset_closure (Or.inl ⟨hu, ?_⟩)))
      (Subgroup.subset_closure (Or.inr ⟨hp.2.1, ?_⟩))
    · rw [hp1, WithTop.coe_zero]
    · rw [hu0, WithTop.coe_zero]
    · rw [hp2, WithTop.coe_zero]
  obtain ⟨y, hy_def⟩ : ∃ y, y = (m : rationalPoints G)⁻¹ * p.1 * m := ⟨_, rfl⟩
  have hy : y ∈ rootGroupPoints i a := by
    have := conj_mem_rootGroupPoints m⁻¹ (a := -a) hp.1
    rwa [hmna, InvMemClass.coe_inv, inv_inv, ← hy_def] at this
  have hminv' : y⁻¹ * p.2⁻¹ * u⁻¹ ∈ normalizerPoints i := by
    have : y⁻¹ * p.2⁻¹ * u⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hy_def, hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2ne := (hp.factors_ne_one i hS ha0 hu h1).2
  have hy0 : x.val a y = 0 := by
    have := hφ.opposite (-a) hna p.2⁻¹ (inv_mem hp.2.1) (inv_ne_one.2 hp2ne) y⁻¹
      (by rw [neg_neg]; exact inv_mem hy) u⁻¹ (by rw [neg_neg]; exact inv_mem hu) hminv'
    rwa [neg_neg, apply_inv hφ, apply_inv hφ, hp2, add_zero] at this
  have hav : eval S a v = 0 := by
    have hval := congrArg (fun ψ : RootFunctionFamily S G => ψ (-a) p.1) hv
    simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hmna, ← hy_def,
      hy0, hp1, zero_add, eval_neg_char] at hval
    have := (WithTop.coe_eq_zero.1 hval.symm)
    linarith
  have hall : ∀ d ∈ relativeRoots i, eval S d v = 0 := by
    intro d hd
    rcases lt_trichotomy (eval S d v) 0 with hlt | heq | hgt
    · exact (not_eval_neg hS hφ hfin ha hν hinv hmc hv hav hd hlt).elim
    · exact heq
    · exfalso
      have hv' : m⁻¹ • x.val = (-(m⁻¹ • v)) +ᵥ x.val := by
        have h := congrArg (m⁻¹ • ·) hv
        simp only [inv_smul_smul, RootFunctionFamily.smul_vadd] at h
        calc m⁻¹ • x.val = -(m⁻¹ • v) +ᵥ ((m⁻¹ • v) +ᵥ m⁻¹ • x.val) := by
              rw [neg_vadd_vadd]
          _ = _ := by rw [← h]
      refine not_eval_neg (n := m⁻¹) hS hφ hfin ha hν (fun χ => by rw [inv_inv]; exact hr' χ)
        ?_ hv' ?_ (weylAction_mapsTo_relativeRoots i m hd) ?_
      · rw [InvMemClass.coe_inv]
        exact inv_mem hmc
      · rw [map_neg, eval_normalizer_smul, inv_inv, hma, eval_neg_char, hav, neg_zero, neg_zero]
      · rw [map_neg, eval_normalizer_smul, inv_inv, h2]
        linarith
  refine KPApartmentData.Apartment.ext ?_
  rw [KPApartmentData.val_smul, hv]
  exact hφ.vadd_eq_self_iff.2 (mem_rootAnnihilator.2 hall)

/-- Proportional relative roots with a positive ratio are equal or differ by a factor two,
from the coroots of opposite factor pairs (no apartment axiom). -/
theorem hasRayProperty_of_rankOne [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (hrank : RelativeRoot.HasRankOneFactorization i) : RootGroupFamily.HasRayProperty i := by
  intro c d hc hd t ht h
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha g hg hg1 => (hrank a ha g hg hg1).1.exists
  have hcc := hE.rootCoroot_pairing i hS ⟨c, hc⟩
  have hcd := hE.rootCoroot_pairing i hS ⟨d, hd⟩
  set cc := hE.rootCoroot i hS ⟨c, hc⟩
  set cd := hE.rootCoroot i hS ⟨d, hd⟩
  have e1 : (latticePairing S d cc : ℝ) = t * 2 := by
    have h' := congrArg (fun f : V S →ₗ[ℝ] ℝ => f ((1 : ℝ) ⊗ₜ[ℤ] cc)) h
    simp only [eval_tmul, one_mul, LinearMap.smul_apply, smul_eq_mul] at h'
    rw [h', hcc]
    push_cast
    ring
  have e2 : (2 : ℝ) = t * latticePairing S c cd := by
    have h' := congrArg (fun f : V S →ₗ[ℝ] ℝ => f ((1 : ℝ) ⊗ₜ[ℤ] cd)) h
    simp only [eval_tmul, one_mul, LinearMap.smul_apply, smul_eq_mul] at h'
    rw [← h', hcd]
    push_cast
    ring
  have hz : latticePairing S d cc * latticePairing S c cd = 4 := by
    have : (latticePairing S d cc : ℝ) * latticePairing S c cd = 4 := by
      rw [e1]
      linear_combination (-2 : ℝ) * e2
    exact_mod_cast this
  have hz₁pos : 0 < latticePairing S d cc := by
    have : (0 : ℝ) < latticePairing S d cc := by rw [e1]; positivity
    exact_mod_cast this
  have hz₂pos : 0 < latticePairing S c cd := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hz₁le : latticePairing S d cc ≤ 4 := by nlinarith
  have hsmul : ∀ (s : ℝ) (a : characterLattice S), eval S a = s • eval S c →
      eval S (2 • a) = (2 * s) • eval S c := by
    intro s a ha
    refine LinearMap.ext fun v => ?_
    rw [eval_nsmul_char, ha, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul]
    push_cast
    ring
  interval_cases hz₁ : latticePairing S d cc
  · -- `t = 1 / 2`
    have ht2 : t = 1 / 2 := by push_cast at e1; linarith
    right; right
    apply eval_injective hS
    rw [hsmul t d h, ht2]
    norm_num
  · -- `t = 1`
    have ht1 : t = 1 := by push_cast at e1; linarith
    left
    apply eval_injective hS
    rw [h, ht1, one_smul]
  · omega
  · -- `t = 2`
    have ht2 : t = 2 := by push_cast at e1; linarith
    right; left
    apply eval_injective hS
    rw [h, hsmul 1 c (one_smul _ _).symm, ht2]
    norm_num

variable (D : KPApartmentData i ω)

/-- The rank-one factorization of `ChamberRankOne` with a central factor fixing `x`, for
apartment data over any field. This is the published
`ValuationBuildingData.exists_rankOne_factorization_fixing` with the same proof. -/
theorem exists_rankOne_factorization_fixing (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hrank : RelativeRoot.HasRankOneFactorization i)
    (x : D.Apartment) {c : characterLattice S} (hc : c ∈ relativeRoots i)
    (hc' : -c ∈ relativeRoots i)
    {v v' : rationalPoints G} (hv : v ∈ rootGroupPoints i c) (hv1 : v ≠ 1)
    (hv' : v' ∈ rootGroupPoints i (-c)) (hv'1 : v' ≠ 1) {t t' : ℝ}
    (ht : x.val c v = t) (ht' : x.val (-c) v' = t') (hpos : 0 < t + t') :
    ∃ x' ∈ rootGroupPoints i (-c), ∃ z ∈ centralizerPoints i,
      ∃ y ∈ rootGroupPoints i c,
        v * v' = x' * z * y ∧ (t' : WithTop ℝ) ≤ x.val (-c) x' ∧
          (t : WithTop ℝ) ≤ x.val c y ∧
            ∃ hz : z ∈ normalizerPoints i, (⟨z, hz⟩ : normalizerPoints i) • x = x := by
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  have hfinite : (relativeRoots i).Finite := hT.finite_relativeRoots i
  have hspan := relativeRootsRestrictedCharactersSpan k G hG S i hi
  have h := x.isValuation
  have hc0 : c ≠ 0 := hc.1
  have hc'' : -(-c) ∈ relativeRoots i := by rwa [neg_neg]
  obtain ⟨p, hp⟩ := ((hrank (-c) hc' v' hv' hv'1).1).exists
  have hp1 : p.1 ∈ rootGroupPoints i (-(-c)) := hp.1
  have hp2 : p.2 ∈ rootGroupPoints i (-(-c)) := hp.2.1
  rw [neg_neg] at hp1 hp2
  have h5p := h.opposite (-c) hc' v' hv' hv'1 p.1 hp.1 p.2 hp.2.1 hp.2.2
  rw [ht', neg_neg] at h5p
  have hp1t := withTop_eq_neg_of_add_eq_zero h5p
  have hp1i : x.val c p.1⁻¹ = ((-t' : ℝ) : WithTop ℝ) := by rw [h.apply_inv]; exact hp1t
  have hlt : x.val c p.1⁻¹ < x.val c v := by
    rw [hp1i, ht, WithTop.coe_lt_coe]
    linarith
  have hw : v * p.1⁻¹ ∈ rootGroupPoints i c :=
    Subgroup.mul_mem _ hv (Subgroup.inv_mem _ hp1)
  have hwt : x.val c (v * p.1⁻¹) = ((-t' : ℝ) : WithTop ℝ) := by
    rw [h.apply_mul_eq_right_of_lt hc hv (Subgroup.inv_mem _ hp1) hlt, hp1i]
  have hw1 : v * p.1⁻¹ ≠ 1 := by
    intro h1
    rw [h1, (h.eq_top_iff c hc 1 (Subgroup.one_mem _)).2 rfl] at hwt
    exact WithTop.top_ne_coe hwt
  obtain ⟨q, hq⟩ := ((hrank c hc (v * p.1⁻¹) hw hw1).1).exists
  have h5q := h.opposite c hc _ hw hw1 q.1 hq.1 q.2 hq.2.1 hq.2.2
  rw [hwt] at h5q
  have hq1t := withTop_eq_neg_of_add_eq_zero h5q
  rw [neg_neg] at hq1t
  have hmflip := hp.weylAction_eq_neg i hT (neg_ne_zero.2 hc0) hv' hv'1
  have hminv : weylAction i (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i)⁻¹ (-c) = c := by
    have := weylAction_inv_apply_apply (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i) (-c)
    rw [hmflip, map_neg] at this
    exact neg_inj.1 this
  have hZ := weylAction_mul_factorPairs_eq_one hT hfinite hspan hc hw hw1 hv' hv'1 hp hq
  have hzC := (hT.weylAction_eq_one_iff i _).1 hZ
  have hy : (p.1 * v' * p.2)⁻¹ * q.2⁻¹ * (p.1 * v' * p.2) * p.2⁻¹ ∈ rootGroupPoints i c := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hp2)
    have := conj_mem_rootGroupPoints (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i)⁻¹
      (Subgroup.inv_mem _ (hq.2.1 : q.2 ∈ rootGroupPoints i (-c)))
    rw [hminv] at this
    simpa only [Subgroup.coe_inv, inv_inv] using this
  have heq : v * v' = q.1⁻¹ * (q.1 * (v * p.1⁻¹) * q.2 * (p.1 * v' * p.2)) *
      ((p.1 * v' * p.2)⁻¹ * q.2⁻¹ * (p.1 * v' * p.2) * p.2⁻¹) := by group
  have hx' : q.1⁻¹ ∈ rootGroupPoints i (-c) := Subgroup.inv_mem _ hq.1
  refine ⟨q.1⁻¹, hx', _, hzC, _, hy, heq, ?_, ?_, centralizerPoints_le_normalizerPoints i hzC,
    ?_⟩
  · rw [h.apply_inv, hq1t]
  · refine le_val_of_mul_eq hT hrank x hc hc' hv hv1 hv' hx' hzC hy heq ht ?_ hpos
    rw [ht']
  · obtain ⟨wm, hwm⟩ := exists_smul_val_eq_vadd
      (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i) x
    have hevm := eval_translation_eq_of_factor x hc' hc'' hv' hv'1 hp.1 hp.2.1 hp.2.2
      hmflip ht' hwm
    set y₀ : D.Apartment :=
      (Submodule.Quotient.mk ((1 / 2 : ℝ) • wm) : TranslationSpace i) +ᵥ x with hy₀
    have hy₀m : y₀.val (-c) v' = 0 := by
      rw [hy₀, val_mk_vadd, RootFunctionFamily.vadd_apply, ht', map_smul, hevm, smul_eq_mul,
        ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj]
      ring
    have hy₀n : y₀.val c (v * p.1⁻¹) = 0 := by
      rw [hy₀, val_mk_vadd, RootFunctionFamily.vadd_apply, hwt, map_smul, smul_eq_mul]
      rw [eval_neg_char] at hevm
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_inj]
      linarith
    have hfixm : (⟨p.1 * v' * p.2, hp.2.2⟩ : normalizerPoints i) • y₀ = y₀ :=
      D.smul_eq_self_of_val_eq_zero hT hc' hv' hv'1 hp hy₀m
    have hfixn : (⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i) • y₀ = y₀ :=
      D.smul_eq_self_of_val_eq_zero hT hc hw hw1 hq hy₀n
    have hfix : ((⟨q.1 * (v * p.1⁻¹) * q.2, hq.2.2⟩ : normalizerPoints i) *
        ⟨p.1 * v' * p.2, hp.2.2⟩) • y₀ = y₀ := by
      rw [mul_smul, hfixm, hfixn]
    exact smul_eq_self_of_mem_centralizerPoints hzC hfix

/-- **Rank-one exchange at an arbitrary point**, for apartment data over any field:
`U_{-a,x,0} U_{a,x,0} ⊆ U_{a,x,0} U_{-a,x,0} H_x`. -/
theorem filtration_neg_mul_filtration_subset_sharpNormalizerStabilizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (x : D.Apartment) {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    (D.filtration x (-a) 0 : Set (rationalPoints G)) * D.filtration x a 0 ⊆
      (D.filtration x a 0 : Set (rationalPoints G)) * D.filtration x (-a) 0 *
        D.sharpNormalizerStabilizer x := by
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  have h := x.isValuation
  have ha' : -a ∈ relativeRoots i := neg_mem_relativeRoots_of_rankOne hT hrank x ha
  rintro _ ⟨v, hv, v', hv', rfl⟩
  beta_reduce
  by_cases hv1 : v = 1
  · subst hv1
    rw [show (1 : rationalPoints G) * v' = v' * 1 * 1 by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul hv' (one_mem _)) (one_mem _)
  by_cases hv'1 : v' = 1
  · subst hv'1
    rw [show v * (1 : rationalPoints G) = 1 * v * 1 by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul (one_mem _) hv) (one_mem _)
  obtain ⟨t, ht⟩ := exists_val_eq_coe x ha' hv.1 hv1
  obtain ⟨t', ht'⟩ := exists_val_eq_coe x ha hv'.1 hv'1
  have ht0 : 0 ≤ t := by
    have := hv.2
    rw [ht] at this
    exact WithTop.coe_le_coe.1 this
  have ht'0 : 0 ≤ t' := by
    have := hv'.2
    rw [ht'] at this
    exact WithTop.coe_le_coe.1 this
  rcases ht0.lt_or_eq with htpos | ht0
  · have ha'' : -(-a) ∈ relativeRoots i := by rwa [neg_neg]
    have hv'a : v' ∈ rootGroupPoints i (-(-a)) := by rw [neg_neg]; exact hv'.1
    have ht'a : x.val (-(-a)) v' = t' := by rw [neg_neg]; exact ht'
    obtain ⟨x', hx', z, hz, y, hy, heq, hx't, hyt, hzN, hzx⟩ :=
      D.exists_rankOne_factorization_fixing hG hi hrank x ha' ha'' hv.1 hv1 hv'a hv'1 ht ht'a
        (by linarith)
    rw [neg_neg] at hx' hx't
    have hzW : weylAction i ⟨z, hzN⟩ = 1 := (hT.weylAction_eq_one_iff i ⟨z, hzN⟩).2 hz
    have hx'F : x' ∈ D.filtration x a 0 :=
      ⟨hx', le_trans (WithTop.coe_le_coe.2 ht'0) hx't⟩
    have hyF : y ∈ D.filtration x (-a) 0 :=
      ⟨hy, le_trans (WithTop.coe_le_coe.2 htpos.le) hyt⟩
    have hzy : z * y * z⁻¹ ∈ D.filtration x (-a) 0 := by
      have := D.conj_mem_filtration ⟨z, hzN⟩ hyF
      rw [hzx, hzW] at this
      exact this
    have hzS : z ∈ D.sharpFixer {x} := by
      have hz' : z = x'⁻¹ * (v * v') * y⁻¹ := by rw [heq]; group
      rw [hz']
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_)
        (Subgroup.mul_mem _ ?_ ?_)) (Subgroup.inv_mem _ ?_)
      · exact filtration_le_sharpFixer x ha hx'F
      · exact filtration_le_sharpFixer x ha' hv
      · exact filtration_le_sharpFixer x ha hv'
      · exact filtration_le_sharpFixer x ha' hyF
    rw [heq, show x' * z * y = x' * (z * y * z⁻¹) * z by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul hx'F hzy)
      (mem_sharpNormalizerStabilizer.2 ⟨hzS, hzN, hzx⟩)
  · subst ht0
    obtain ⟨q, hq⟩ := ((hrank (-a) ha' v hv.1 hv1).1).exists
    have hq1 : q.1 ∈ rootGroupPoints i (-(-a)) := hq.1
    have hq2 : q.2 ∈ rootGroupPoints i (-(-a)) := hq.2.1
    rw [neg_neg] at hq1 hq2
    have h5 := h.opposite (-a) ha' v hv.1 hv1 q.1 hq.1 q.2 hq.2.1 hq.2.2
    rw [ht, neg_neg] at h5
    have hq1t := withTop_eq_neg_of_add_eq_zero h5
    have h5' := h.opposite_snd ha' hv.1 hv1 hq.1 hq.2.1 hq.2.2
    rw [ht, neg_neg] at h5'
    have hq2t := withTop_eq_neg_of_add_eq_zero h5'
    have hq1F : q.1 ∈ D.filtration x a 0 := ⟨hq1, by rw [hq1t]; simp⟩
    have hq2F : q.2 ∈ D.filtration x a 0 := ⟨hq2, by rw [hq2t]; simp⟩
    set n : normalizerPoints i := ⟨q.1 * v * q.2, hq.2.2⟩ with hn
    have hnx : n • x = x := by
      refine D.smul_eq_self_of_val_eq_zero hT ha' hv.1 hv1 hq ?_
      rw [ht]
      rfl
    have hnflip : weylAction i n a = -a := by
      have hflip := hq.weylAction_eq_neg i hT (neg_ne_zero.2 ha.1) hv.1 hv1
      rw [map_neg] at hflip
      exact neg_inj.1 hflip
    have hnS : (n : rationalPoints G) ∈ D.sharpFixer {x} :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (filtration_le_sharpFixer x ha hq1F)
        (filtration_le_sharpFixer x ha' hv)) (filtration_le_sharpFixer x ha hq2F)
    have hconj : (n : rationalPoints G) * (q.2⁻¹ * v') * (n : rationalPoints G)⁻¹ ∈
        D.filtration x (-a) 0 := by
      have := D.conj_mem_filtration n
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq2F) hv')
      rw [hnx, hnflip] at this
      exact this
    have heq : v * v' = q.1⁻¹ *
        ((n : rationalPoints G) * (q.2⁻¹ * v') * (n : rationalPoints G)⁻¹) *
          (n : rationalPoints G) := by
      rw [hn]
      group
    rw [heq]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Subgroup.inv_mem _ hq1F) hconj)
      (mem_sharpNormalizerStabilizer.2 ⟨hnS, n.2, hnx⟩)

/-- **The sharp fixer of an arbitrary point**, for apartment data over any field and without
apartment axioms: `G(k)^♯_x ⊆ X_x(Φ_{-mu}) X_x(Φ_mu) H_x` for every generic cocharacter
`mu`. -/
theorem sharpFixer_subset_mul_sharpNormalizerStabilizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (mu : cocharacterLattice S) (hmu : IsGenericCocharacter i mu) :
    (D.sharpFixer {x} : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-mu), D.chamberRootGroup x false b :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        ((⨆ b : positiveRelativeRoots i mu, D.chamberRootGroup x false b :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        (D.sharpNormalizerStabilizer x : Set (rationalPoints G)) := by
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  have hfam := RootGroupFamily.iSup_subset_mul_of_exchange
    (U := fun b => D.rootFixer b {x})
    (D.rootFixer_hasCommutatorRelations (Set.finite_singleton x) (Set.singleton_nonempty x))
    (IsSplitTorus.finite_relativeRoots (i := i) hT)
    (hasRayProperty_of_rankOne hT hrank)
    (fun c hc => neg_mem_relativeRoots_of_rankOne hT hrank x hc)
    (fun c hc h2c => D.rootFixer_double_le {x} hc h2c)
    (H := D.sharpNormalizerStabilizer x)
    (fun c hc => by
      simp only [rootFixer_singleton]
      exact D.filtration_neg_mul_filtration_subset_sharpNormalizerStabilizer hG hi hrank x hc)
    mu hmu
  simpa only [sharpFixer, rootFixer_singleton, chamberRootGroup, Bool.false_eq_true,
    ↓reduceIte] using hfam

/-- **Unipotent stabilizers of apartment points** (KP Axiom 4.1.8 (3) input), for apartment
data over any field and without apartment axioms: an element of the positive unipotent group
of a generic cocharacter that fixes the image of `x` in the reduced building lies in the
subgroup generated by the positive depth-zero root groups at `x`. -/
theorem mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {g : rationalPoints G}
    (hgU : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hgx : g • D.apartmentMap x = D.apartmentMap x) :
    g ∈ ⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x false b := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have hsharp := D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨m, -, s, hs, hgsm⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff D.sharpFixerFamily x g).1
      (MulAction.mem_stabilizer_iff.2 hgx)
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, n, hn, hvwn⟩ := hsharp hs
  change v * w * n = s at hvwn
  have hnN : n ∈ normalizerPoints i :=
    (KPApartmentData.mem_sharpNormalizerStabilizer.mp hn).2.1
  let n' : normalizerPoints i := ⟨n * m, (normalizerPoints i).mul_mem hnN m.property⟩
  have hfactor : v * w * (n' : rationalPoints G) = g := by
    change v * w * (n * m) = g
    rw [← mul_assoc, hvwn, hgsm]
  have hvU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hv).1
  have hwU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hw).1
  have hpos : v⁻¹ * g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hvU) hgU
  have hopp : w⁻¹ ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact Subgroup.inv_mem _ hwU
  have heq : (n' : rationalPoints G) = w⁻¹ * (v⁻¹ * g) := by
    rw [← hfactor]
    group
  have hn' : n' = 1 :=
    normalizer_eq_one_of_unipotent_product i ν n' ⟨_, hopp⟩ ⟨_, hpos⟩ heq
  have hfactor' : v * w = g := by simpa only [hn', OneMemClass.coe_one, mul_one] using hfactor
  have hwpos : w ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    have hwg : w = v⁻¹ * g := by rw [← hfactor']; group
    rw [hwg]
    exact hpos
  have hwopp : w ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact hwU
  have hw1 : w = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
      (CommGroupScheme.groupHom ν ≫ i) hwopp
      (Dynamic.unipotent_le_parabolic _ _ hwpos)
  have hvg : v = g := by simpa only [hw1, mul_one] using hfactor'
  exact hvg ▸ hv

end KPApartmentData

end Langlands.Geometry.Building
