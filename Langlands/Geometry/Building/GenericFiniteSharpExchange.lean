import Langlands.Geometry.Building.GenericPointSharpExchange

/-! # Finite sharp-fixer exchange over any field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- **Rank-one exchange over a set.** Under opposite factor pairs, for every non-empty set `Ω`
of apartment points and every relative root `a`,
`U_{-a,Ω,0} U_{a,Ω,0} ⊆ U_{a,Ω,0} U_{-a,Ω,0} H_Ω`. -/
theorem rootFixer_neg_mul_rootFixer_subset_sharpNormalizerFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hrank : RelativeRoot.HasRankOneFactorization i)
    {Ω : Set D.Apartment} (hne : Ω.Nonempty) {a : characterLattice S}
    (ha : a ∈ relativeRoots i) :
    (D.rootFixer (-a) Ω : Set (rationalPoints G)) * D.rootFixer a Ω ⊆
      (D.rootFixer a Ω : Set (rationalPoints G)) * D.rootFixer (-a) Ω *
        D.sharpNormalizerFixer Ω := by
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨x₀, hx₀⟩ := hne
  have h := x₀.isValuation
  have ha' : -a ∈ relativeRoots i := neg_mem_relativeRoots_of_rankOne hT hrank x₀ ha
  rintro _ ⟨v, hv, v', hv', rfl⟩
  beta_reduce
  obtain ⟨hvU, hvΩ⟩ := D.mem_rootFixer.1 hv
  obtain ⟨hv'U, hv'Ω⟩ := D.mem_rootFixer.1 hv'
  by_cases hv1 : v = 1
  · subst hv1
    rw [show (1 : rationalPoints G) * v' = v' * 1 * 1 by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul hv' (one_mem _)) (one_mem _)
  by_cases hv'1 : v' = 1
  · subst hv'1
    rw [show v * (1 : rationalPoints G) = 1 * v * 1 by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul (one_mem _) hv) (one_mem _)
  obtain ⟨t, ht⟩ := exists_val_eq_coe x₀ ha' hvU hv1
  obtain ⟨t', ht'⟩ := exists_val_eq_coe x₀ ha hv'U hv'1
  have ht0 : 0 ≤ t := by
    have := (hvΩ x₀ hx₀).2
    rw [ht] at this
    exact WithTop.coe_le_coe.1 this
  have ht'0 : 0 ≤ t' := by
    have := (hv'Ω x₀ hx₀).2
    rw [ht'] at this
    exact WithTop.coe_le_coe.1 this
  have haR : D.rootFixer a Ω ≤ D.sharpFixer Ω :=
    D.rootFixer_le_sharpFixer ⟨a, ha⟩ Ω
  have ha'R : D.rootFixer (-a) Ω ≤ D.sharpFixer Ω :=
    D.rootFixer_le_sharpFixer ⟨-a, ha'⟩ Ω
  rcases (add_nonneg ht0 ht'0).lt_or_eq with hpos | hzero
  · -- `x_{-a}(v) + x_a(v′) > 0` at `x₀`: the factorization with a central factor
    have ha'' : -(-a) ∈ relativeRoots i := by rwa [neg_neg]
    have hv'a : v' ∈ rootGroupPoints i (-(-a)) := by rw [neg_neg]; exact hv'U
    have ht'a : x₀.val (-(-a)) v' = t' := by rw [neg_neg]; exact ht'
    obtain ⟨x', hx', z, hz, y, hy, heq, hx't, hyt, hzN, hzx⟩ :=
      D.exists_rankOne_factorization_fixing hG hi hrank x₀ ha' ha'' hvU hv1 hv'a hv'1 ht ht'a hpos
    rw [neg_neg] at hx' hx't
    have hzW : weylAction i ⟨z, hzN⟩ = 1 := (hT.weylAction_eq_one_iff i ⟨z, hzN⟩).2 hz
    have hx'F : x' ∈ D.rootFixer a Ω :=
      D.mem_rootFixer.2 ⟨hx', fun y₀ hy₀ =>
        mem_filtration_of_val_le (hv'Ω y₀ hy₀) hx' (by rw [ht']; exact hx't)⟩
    have hyF : ∀ y₀ ∈ Ω, y ∈ D.filtration y₀ (-a) 0 := fun y₀ hy₀ =>
      mem_filtration_of_val_le (hvΩ y₀ hy₀) hy (by rw [ht]; exact hyt)
    have hzfix : ∀ y₀ ∈ Ω, (⟨z, hzN⟩ : normalizerPoints i) • y₀ = y₀ := fun y₀ _ =>
      KPApartmentData.smul_eq_self_of_mem_centralizerPoints (D := D)
        (n := ⟨z, hzN⟩) (x := y₀) (y := x₀) hz hzx
    have hzyF : ∀ y₀ ∈ Ω, z * y * z⁻¹ ∈ D.filtration y₀ (-a) 0 := by
      intro y₀ hy₀
      have := D.conj_mem_filtration ⟨z, hzN⟩ (hyF y₀ hy₀)
      rw [hzfix y₀ hy₀, hzW] at this
      exact this
    have hzy : z * y * z⁻¹ ∈ D.rootFixer (-a) Ω :=
      D.mem_rootFixer.2 ⟨(hzyF x₀ hx₀).1, hzyF⟩
    have hyR : y ∈ D.rootFixer (-a) Ω := D.mem_rootFixer.2 ⟨hy, hyF⟩
    have hzS : z ∈ D.sharpFixer Ω := by
      have hz' : z = x'⁻¹ * (v * v') * y⁻¹ := by rw [heq]; group
      rw [hz']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (haR hx'F))
        (Subgroup.mul_mem _ (ha'R hv) (haR hv'))) (Subgroup.inv_mem _ (ha'R hyR))
    rw [heq, show x' * z * y = x' * (z * y * z⁻¹) * z by group]
    exact Set.mul_mem_mul (Set.mul_mem_mul hx'F hzy)
      (mem_sharpNormalizerFixer.2 ⟨hzS, hzN, hzfix⟩)
  · -- `x_{-a}(v) = 0 = x_a(v′)` at `x₀`: `n = m(v)` fixes every point of `Ω`
    have ht00 : t = 0 := by linarith
    have ht'00 : t' = 0 := by linarith
    subst ht00 ht'00
    obtain ⟨q, hq⟩ := ((hrank (-a) ha' v hvU hv1).1).exists
    have hq1 : q.1 ∈ rootGroupPoints i (-(-a)) := hq.1
    have hq2 : q.2 ∈ rootGroupPoints i (-(-a)) := hq.2.1
    rw [neg_neg] at hq1 hq2
    have h5 := h.opposite (-a) ha' v hvU hv1 q.1 hq.1 q.2 hq.2.1 hq.2.2
    rw [ht, neg_neg] at h5
    have hq1t := withTop_eq_neg_of_add_eq_zero h5
    have h5' := h.opposite_snd ha' hvU hv1 hq.1 hq.2.1 hq.2.2
    rw [ht, neg_neg] at h5'
    have hq2t := withTop_eq_neg_of_add_eq_zero h5'
    have hq1F : q.1 ∈ D.rootFixer a Ω :=
      D.mem_rootFixer.2 ⟨hq1, fun y₀ hy₀ =>
        mem_filtration_of_val_le (hv'Ω y₀ hy₀) hq1 (by rw [ht', hq1t]; simp)⟩
    have hq2F : q.2 ∈ D.rootFixer a Ω :=
      D.mem_rootFixer.2 ⟨hq2, fun y₀ hy₀ =>
        mem_filtration_of_val_le (hv'Ω y₀ hy₀) hq2 (by rw [ht', hq2t]; simp)⟩
    set n : normalizerPoints i := ⟨q.1 * v * q.2, hq.2.2⟩ with hn
    have hval : ∀ y₀ ∈ Ω, y₀.val (-a) v = 0 := by
      intro y₀ hy₀
      obtain ⟨w, rfl⟩ := exists_mk_vadd_eq x₀ y₀
      have e1 := (hvΩ _ hy₀).2
      have e2 := (hv'Ω _ hy₀).2
      rw [val_mk_vadd_apply, ht, ← WithTop.coe_add, WithTop.coe_le_coe] at e1
      rw [val_mk_vadd_apply, ht', ← WithTop.coe_add, WithTop.coe_le_coe] at e2
      rw [eval_neg_char] at e1
      rw [val_mk_vadd_apply, ht, ← WithTop.coe_add, eval_neg_char]
      have he : eval S a w = 0 := by linarith
      rw [he, neg_zero, add_zero]
      rfl
    have hnx : ∀ y₀ ∈ Ω, n • y₀ = y₀ := by
      intro y₀ hy₀
      refine D.smul_eq_self_of_val_eq_zero hT ha' hvU hv1 hq ?_
      exact hval y₀ hy₀
    have hnflip : weylAction i n a = -a := by
      have hflip := hq.weylAction_eq_neg i hT (neg_ne_zero.2 ha.1) hvU hv1
      rw [map_neg] at hflip
      exact neg_inj.1 hflip
    have hnS : (n : rationalPoints G) ∈ D.sharpFixer Ω :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (haR hq1F) (ha'R hv)) (haR hq2F)
    have hconjF : ∀ y₀ ∈ Ω, (n : rationalPoints G) * (q.2⁻¹ * v') *
        (n : rationalPoints G)⁻¹ ∈ D.filtration y₀ (-a) 0 := by
      intro y₀ hy₀
      have := D.conj_mem_filtration n
        (Subgroup.mul_mem _ (Subgroup.inv_mem _
          ((D.mem_rootFixer.1 hq2F).2 y₀ hy₀)) (hv'Ω y₀ hy₀))
      rw [hnx y₀ hy₀, hnflip] at this
      exact this
    have hconj : (n : rationalPoints G) * (q.2⁻¹ * v') * (n : rationalPoints G)⁻¹ ∈
        D.rootFixer (-a) Ω :=
      D.mem_rootFixer.2 ⟨(hconjF x₀ hx₀).1, hconjF⟩
    have heq : v * v' = q.1⁻¹ *
        ((n : rationalPoints G) * (q.2⁻¹ * v') * (n : rationalPoints G)⁻¹) *
          (n : rationalPoints G) := by
      rw [hn]
      group
    rw [heq]
    exact Set.mul_mem_mul (Set.mul_mem_mul (Subgroup.inv_mem _ hq1F) hconj)
      (mem_sharpNormalizerFixer.2 ⟨hnS, n.2, hnx⟩)

/-- **The sharp fixer of a finite set.** For arbitrary-field apartment data,
for every finite non-empty set `Ω` of apartment points and every generic cocharacter `mu`,
`G(k)^♯_Ω ⊆ X_Ω(Φ_{-mu}) X_Ω(Φ_mu) H_Ω`, where `X_Ω(P) = ⨆_{b ∈ P} U_{b,Ω,0}` and `H_Ω` is the
subgroup of elements of `N(k) ∩ G(k)^♯_Ω` fixing every point of `Ω`. -/
theorem sharpFixer_subset_mul_sharpNormalizerFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {Ω : Set D.Apartment} (hΩ : Ω.Finite) (hne : Ω.Nonempty)
    (mu : cocharacterLattice S) (hmu : IsGenericCocharacter i mu) :
    (D.sharpFixer Ω : Set (rationalPoints G)) ⊆
      ((⨆ b : positiveRelativeRoots i (-mu), D.rootFixer b Ω :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        ((⨆ b : positiveRelativeRoots i mu, D.rootFixer b Ω :
          Subgroup (rationalPoints G)) : Set (rationalPoints G)) *
        (D.sharpNormalizerFixer Ω : Set (rationalPoints G)) := by
  have hT : IsSplitTorus S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  have hrank := rootRankOneFactorization k G hG S i hi
  obtain ⟨x₀, hx₀⟩ := hne
  exact RootGroupFamily.iSup_subset_mul_of_exchange (U := fun b => D.rootFixer b Ω)
    (D.rootFixer_hasCommutatorRelations hΩ ⟨x₀, hx₀⟩)
    (IsSplitTorus.finite_relativeRoots (i := i) hT)
    (hasRayProperty_of_rankOne hT hrank)
    (fun c hc => neg_mem_relativeRoots_of_rankOne hT hrank x₀ hc)
    (fun c hc h2c => D.rootFixer_double_le Ω hc h2c)
    (fun c hc => D.rootFixer_neg_mul_rootFixer_subset_sharpNormalizerFixer hG hi hrank ⟨x₀, hx₀⟩ hc)
    mu hmu

end Langlands.Geometry.Building.KPApartmentData
