import Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
import Langlands.Representation.CuspidalSupport.DualAveraging
import Langlands.Group.GL.CartanStatement

noncomputable section

open Filter Topology

namespace Langlands.CuspidalSupport.HarishChandra

open GeneralLinear LeviAdmissibility

universe uF uV

/-- The Cartan and gap-vanishing argument gives compact support of averaged
orbits on the actual determinant-unit subgroup. -/
theorem hasCompactSupport_average_determinantUnit_of_cartan
    (hCartan : CartanDecompositionStatement.{uF, uF})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (hρ : IsSmooth ρ),
      IsLeviQuasicuspidal B ρ →
      ∀ (H : OpenSubgroup (B.Levi F.Carrier)) (hH : IsCompact (H : Set (B.Levi F.Carrier))) (v : V),
        HasCompactSupport (fun g : determinantUnitSubgroup T B =>
          Compact.averageMap ρ hρ H hH (ρ g.val v)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro V _ _ ρ hρ hq H hH v
  classical
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F.Carrier
  let K₀ := integralLevi (K := F.Carrier) B
  have hK₀ : IsCompact (K₀ : Set (B.Levi F.Carrier)) := isCompact_integralLevi B
  let W := Compact.orbit (ρ.comp K₀.toSubgroup.subtype) v
  have : Finite W := Compact.finite_orbit_of_smooth ρ hρ K₀ hK₀ v
  obtain ⟨C, hC⟩ := hK₀.elim_finite_subcover
    (fun c : B.Levi F.Carrier => (· * c⁻¹) ⁻¹' (H : Set (B.Levi F.Carrier)))
    (fun c => H.isOpen.preimage (continuous_id.mul continuous_const))
    (fun k _ => Set.mem_iUnion.mpr ⟨k, by
      change k * k⁻¹ ∈ H
      rw [mul_inv_cancel]
      exact H.one_mem⟩)
  obtain ⟨N, hN⟩ := exists_uniform_gap_bound B ρ hρ hq hϖ H hH
    (ι := C × W) (fun x => x.1.1) (fun x => x.2.1)
  let Λ : Set (∀ j : Fin B.length, Fin (B.size j) → ℤ) :=
    {lam | (∀ j, Antitone (lam j)) ∧
      (∀ j (b : Fin (B.size j)) (h : b.val + 1 < B.size j),
        lam j b - lam j ⟨b.val + 1, h⟩ < N) ∧
      (∀ j, ∑ b, lam j b = 0)}
  have hΛ : Λ.Finite := finite_zeroSum_boundedGap B N
  let S : Set (B.Levi F.Carrier) :=
    ⋃ lam ∈ Λ, (fun x : B.Levi F.Carrier × B.Levi F.Carrier =>
      x.1 * leviTorus B ϖ lam * x.2) '' ((K₀ : Set _) ×ˢ (K₀ : Set _))
  have hS : IsCompact S := hΛ.isCompact_biUnion fun lam _ =>
    (hK₀.prod hK₀).image (by fun_prop)
  have hclosed : IsClosed (determinantUnitSubgroup T B : Set (B.Levi F.Carrier)) :=
    (determinantUnitOpenSubgroup T B).isClosed
  apply HasCompactSupport.of_support_subset_isCompact
    (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hS)
  intro g hnonzero
  have hcartan := fun j => (hCartan F.Carrier (ValuativeRel.ValueGroupWithZero F.Carrier)
    (ValuativeRel.valuation F.Carrier) ϖ hϖ (B.size j) (g.val j)).exists
  choose lam hlam k₁ hk₁ k₂ hk₂ hfact using hcartan
  have hk₁' : k₁ ∈ integralLevi B := (mem_integralLevi B).mpr hk₁
  have hk₂' : k₂ ∈ integralLevi B := (mem_integralLevi B).mpr hk₂
  have hfact' : g.val = k₁ * leviTorus B ϖ lam * k₂ := funext hfact
  have hsum := block_sums_eq_zero_of_determinantUnit_cartan B T hϖ
    g.property hk₁' hk₂' hfact'
  obtain ⟨c, hc, hkc⟩ := Set.mem_iUnion₂.mp (hC hk₁')
  have hw : ρ k₂ v ∈ W := ⟨⟨k₂, hk₂'⟩, rfl⟩
  have heq : Compact.averageMap ρ hρ H hH (ρ g.val v) =
      Compact.averageMap ρ hρ H hH (ρ (c * leviTorus B ϖ lam) (ρ k₂ v)) := by
    have hk : g.val = (k₁ * c⁻¹) * (c * leviTorus B ϖ lam) * k₂ := by
      rw [hfact']
      group
    rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact Compact.orbitMean_apply (ρ.comp H.toSubgroup.subtype) ⟨_, hkc⟩ _
  have hgap : ∀ j (b : Fin (B.size j)) (h : b.val + 1 < B.size j),
      lam j b - lam j ⟨b.val + 1, h⟩ < N := by
    intro j b h
    by_contra hlarge
    have hz := hN (⟨c, hc⟩, ⟨_, hw⟩) lam hlam j b.val h (le_of_not_gt hlarge)
    exact hnonzero (heq.trans hz)
  change g.val ∈ S
  exact Set.mem_iUnion₂.mpr ⟨lam, ⟨hlam, hgap, hsum⟩,
    ⟨(k₁, k₂), ⟨hk₁', hk₂'⟩, hfact'.symm⟩⟩

/-- Smooth-dual coefficients inherit compact support from averaged orbits.
The Cartan hypothesis is discharged by the actual Cartan theorem at assembly. -/
theorem hasCompactSmoothDualCoefficients_of_isLeviQuasicuspidal_of_cartan
    (hCartan : CartanDecompositionStatement.{uF, uF})
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V) (_hρ : IsSmooth ρ),
      IsLeviQuasicuspidal B ρ →
        HasCompactSmoothDualCoefficients (determinantUnitRestriction T B ρ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro V _ _ ρ hρ hq v ℓ hℓ
  have hℓ' : IsSmoothVector ρ.dual ℓ :=
    (determinantUnitSmoothDual p F T n B V ρ ℓ).mp hℓ
  obtain ⟨H, hH, -, havg⟩ := Compact.exists_dual_averageMap_eq ρ hρ
    (levi_exists_compact_openSubgroup_subset T B) ℓ hℓ'
    (U := Set.univ) Filter.univ_mem
  have hc := hasCompactSupport_average_determinantUnit_of_cartan
    hCartan T B ρ hρ hq H hH v
  have heq : matrixCoefficient (determinantUnitRestriction T B ρ) ℓ v =
      ℓ ∘ (fun g : determinantUnitSubgroup T B =>
        Compact.averageMap ρ hρ H hH (ρ g.val v)) := by
    funext g
    exact (havg (ρ g.val v)).symm
  rw [heq]
  exact hc.comp_left ℓ.map_zero

end Langlands.CuspidalSupport.HarishChandra
