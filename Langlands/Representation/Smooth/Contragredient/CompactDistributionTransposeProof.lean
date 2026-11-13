import Langlands.Representation.Smooth.Contragredient.CompactDistributionTransposeStatements
import Langlands.HarmonicAnalysis.Distribution.RenardHeckeProof
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.Representation.Compact.CharZeroAverage

/-! # Renard III.1.6: compact-distribution transpose and compact fixed-dual restriction -/

noncomputable section

namespace Langlands

open HarmonicAnalysis MeasureTheory
open Distribution.RenardHecke
open scoped BigOperators

universe u v

/-- The compactly supported distribution identity at the full published universes. -/
theorem compactDistributionContragredientTranspose :
    CompactDistributionContragredientTransposeStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ ρ hρ act act' hact hact' T Tinv hinv ℓ x
  let φ : LocallyConstant G ℂ :=
    ⟨fun g => ℓ.val (ρ g x), (Hecke.orbitMap_locallyConstant ρ (hρ x)).comp ℓ.val⟩
  let ev : Module.Dual ℂ (SmoothDual ρ) :=
    (Module.Dual.eval ℂ V x).comp (smoothDualPairing ρ)
  have hTi : Tinv = compactInversion T := Subtype.ext hinv
  have hp := hact' Tinv ℓ ev (invFunction φ) (fun _ => rfl)
  change smoothDualPairing ρ (act' Tinv ℓ) x =
    Distribution.compactSupportFunctional Tinv (invFunction φ) at hp
  rw [hp, hTi]
  change Distribution.compactSupportPairing (compactInversion T) (invFunction φ) = _
  rw [compactSupportPairing_compactInversion]
  have hinvinv : invFunction (invFunction φ) = φ := by
    ext g
    exact congrArg φ (inv_inv g)
  rw [hinvinv]
  exact (hact T x ℓ.val φ (fun _ => rfl)).symm

private theorem compactHaar_pairing
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (φ : LocallyConstant G ℂ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    Distribution.compactSupportFunctional (Distribution.compactSubgroupHaar K hK) φ =
      ∫ k : K, φ k.val ∂(Measure.haarMeasure ⊤) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨f, hf⟩ := Distribution.exists_testFunction_agrees_on_compact hK φ
  have hs : Distribution.support
      (Distribution.compactSubgroupHaar K hK : Distribution G) ⊆ (K : Set G) :=
    Distribution.support_subset_of_mem_supportedOn hK.isClosed
      (Distribution.compactSubgroupDistribution_mem_supportedOn K hK)
  rw [Distribution.compactSupportFunctional_eq_of_agrees _ φ f
    (fun x hx => hf x (hs hx)), Distribution.compactSubgroupHaar_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun k => hf k.val k.property))

/-- Transposition of normalized compact Haar and preservation of invariant forms. -/
theorem compactSubgroupHaarTranspose : CompactSubgroupHaarTransposeStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ ρ hρ act act' hact hact' K hK
  constructor
  · exact compactDistributionContragredientTranspose G V ρ hρ act act' hact hact'
      (Distribution.compactSubgroupHaar K hK) (Distribution.compactSubgroupHaar K hK)
      (inversionDistributions_compactSubgroupHaar K hK).symm
  · intro m hm x
    let φ : LocallyConstant G ℂ :=
      ⟨fun g => m (ρ g x), (Hecke.orbitMap_locallyConstant ρ (hρ x)).comp m⟩
    rw [hact _ x m φ (fun _ => rfl), compactHaar_pairing]
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let : MeasurableSpace K := borel K
    let : BorelSpace K := ⟨rfl⟩
    let : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) :=
      isProbabilityMeasure_haarMeasure_top
    have hc : (fun k : K => φ k.val) = fun _ => m x := by
      funext k
      exact hm k.val k.property x
    rw [hc]
    simp

private theorem dual_orbitMean_of_constant
    {H : Type u} [Group H] {V : Type v} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ H V) (x : V) [Finite (Compact.CharZero.orbit τ x)]
    (m : Module.Dual ℂ V) (hm : ∀ h, m (τ h x) = m x) :
    m (Compact.CharZero.orbitMean τ x) = m x := by
  classical
  let := Fintype.ofFinite (Compact.CharZero.orbit τ x)
  have hx (y : Compact.CharZero.orbit τ x) : m y.val = m x := by
    obtain ⟨h, hh⟩ := y.property
    exact (congrArg m hh).symm.trans (hm h)
  have hc : (Fintype.card (Compact.CharZero.orbit τ x) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Compact.CharZero.orbitMean_eq_finiteMean]
  unfold Compact.CharZero.finiteMean
  rw [map_smul, map_sum]
  simp only [hx, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Restriction is bijective for the full algebraic dual and every compact subgroup. -/
theorem compactFixedDualRestriction : CompactFixedDualRestrictionStatement.{u, v} := by
  intro G _ _ _ _ _ _ V _ _ ρ hρ K hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let τ := ρ.comp K.subtype
  let (x : V) : Finite (Compact.CharZero.orbit τ x) :=
    ((Hecke.orbitMap_locallyConstant ρ (hρ x)).comp_continuous
      continuous_subtype_val).range_finite.to_subtype
  let A : V →ₗ[ℂ] V :=
    { toFun := Compact.CharZero.orbitMean τ
      map_add' := fun x y => Compact.CharZero.orbitMean_add τ x y
      map_smul' := fun c x => Compact.CharZero.orbitMean_smul τ c x }
  let P : V →ₗ[ℂ] fixedVectors ρ K :=
    A.codRestrict (fixedVectors ρ K) (fun x => Compact.CharZero.orbitMean_invariant τ x)
  have hPid (x : fixedVectors ρ K) : P x.val = x := by
    apply Subtype.ext
    exact Compact.CharZero.orbitMean_id τ x.val x.property
  have hPk (k : K) (x : V) : P (ρ k.val x) = P x := by
    apply Subtype.ext
    exact Compact.CharZero.orbitMean_apply τ k x
  have hfunctional (m : fixedVectors ρ.dual K) (x : V) :
      m.val (P x).val = m.val x := by
    apply dual_orbitMean_of_constant τ x m.val
    intro k
    have hk := congrArg (fun f : Module.Dual ℂ V => f x) (m.property k⁻¹)
    change m.val (ρ ((k⁻¹ : K).val)⁻¹ x) = m.val x at hk
    simpa only [τ, MonoidHom.comp_apply, Subgroup.subtype_apply,
      InvMemClass.coe_inv, inv_inv] using hk
  constructor
  · intro m n heq
    apply Subtype.ext
    ext x
    calc
      m.val x = m.val (P x).val := (hfunctional m x).symm
      _ = n.val (P x).val := congrArg (fun f => f (P x)) heq
      _ = n.val x := hfunctional n x
  · intro μ
    let m : Module.Dual ℂ V := μ.comp P
    have hfix (k : K) : ρ.dual k.val m = m := by
      ext x
      change μ (P (ρ k.val⁻¹ x)) = μ (P x)
      exact congrArg μ (hPk k⁻¹ x)
    refine ⟨⟨m, hfix⟩, ?_⟩
    ext x
    exact congrArg μ (hPid x)

/-- Renard III.1.6, Lemma, at the exact published aggregate type. -/
theorem contragredientDistributionLemma : ContragredientDistributionLemmaStatement.{u, v} :=
  ⟨compactDistributionContragredientTranspose, compactSubgroupHaarTranspose,
    compactFixedDualRestriction⟩

end Langlands
