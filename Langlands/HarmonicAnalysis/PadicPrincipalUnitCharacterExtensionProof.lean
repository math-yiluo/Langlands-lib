import Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionStatement
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Topology.LocallyProfiniteProof
import Langlands.Topology.FiniteQuotientCharacterExtension

/-! Extend through a finite compact-unit quotient and remove the valuation. -/

noncomputable section

open Topology Filter
open Langlands.LocalFactor.PadicAbelian

namespace Langlands.HarmonicAnalysis

universe u

private theorem principalUnits_open {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    IsOpen (T.principalUnits n : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hval : IsOpen {x : F.Carrier | T.discreteValuation x = 1} := by
    convert (Valuation.isOpen_sphere (v := ValuativeRel.valuation F.Carrier)
      one_ne_zero) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_eq_one_iff]
    change e (ValuativeRel.valuation F.Carrier x) = 1 ↔
      ValuativeRel.valuation F.Carrier x = 1
    constructor
    · intro h
      exact e.strictMono.injective (h.trans (map_one e).symm)
    · intro h
      rw [h, map_one]
  have hint : IsOpen (T.Integers : Set F.Carrier) := Valuation.isOpen_integer
  convert (hval.preimage Units.continuous_val).inter
    (hint.preimage ((Units.continuous_val.sub continuous_const).div_const
      (T.uniformizer ^ (n : ℤ)))) using 1
  ext z
  exact T.mem_principalUnits_iff_div_mem_integers n z

private theorem continuous_unit_ord {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) :
    letI := T.topology
    Continuous (fun a : F.Carrierˣ => T.ord (a : F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply IsLocallyConstant.continuous
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  have h := Units.continuous_val.continuousAt.preimage_mem_nhds
    ((ValuativeRel.valuation F.Carrier).locally_const
      ((ValuativeRel.valuation F.Carrier).ne_zero_iff.mpr a.ne_zero))
  filter_upwards [h] with b hb
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  change -WithZero.log (e (ValuativeRel.valuation F.Carrier b.val)) =
    -WithZero.log (e (ValuativeRel.valuation F.Carrier a.val))
  rw [hb]

/-- A continuous character on actual principal units has a normalized finite-order extension. -/
theorem padicPrincipalUnitCharacterExtension :
    PadicPrincipalUnitCharacterExtensionStatement.{u} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro n η
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact (ValuativeRel.valuation F.Carrier).toTopologicalSpace_eq
  let normHom : F.Carrierˣ →* ℝ :=
    { toFun a := T.normalizedAbs (a : F.Carrier)
      map_one' := T.normalizedAbs_one
      map_mul' := fun a b => T.normalizedAbs_mul _ _ }
  let K : Subgroup F.Carrierˣ := normHom.ker
  let : CompactSpace K :=
    isCompact_iff_compactSpace.mp T.isCompact_normalizedAbs_eq_one_units
  have hnorm (z : T.principalUnits n) : z.val ∈ K := by
    change T.normalizedAbs ((z : F.Carrierˣ) : F.Carrier) = 1
    rw [T.normalizedAbs_of_ne_zero (Units.ne_zero _)]
    have hord : T.ord ((z : F.Carrierˣ) : F.Carrier) = 0 := by
      simp only [PadicField.TopologicalData.ord, z.property.1, WithZero.log_one, neg_zero]
    simp [hord]
  let f : T.principalUnits n →ₜ* K :=
    { toFun z := ⟨z.val, hnorm z⟩
      map_one' := by apply Subtype.ext; rfl
      map_mul' := fun a b => by apply Subtype.ext; rfl
      continuous_toFun := continuous_subtype_val.subtype_mk _ }
  have hf : Function.Injective f := by
    intro a b h
    exact Subtype.ext (congrArg (fun z : K => z.val) h)
  have hfopen : IsOpenMap f :=
    (principalUnits_open T n).isOpenMap_subtype_val.subtype_mk hnorm
  let : LocallyCompactSpace (T.principalUnits n) :=
    (principalUnits_open T n).locallyCompactSpace
  let : TotallyDisconnectedSpace (T.principalUnits n) :=
    ⟨isTotallyDisconnected_of_image
      (Units.continuous_val.comp continuous_subtype_val).continuousOn
      (Units.val_injective.comp Subtype.val_injective)
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : NonarchimedeanGroup (T.principalUnits n) := by
    refine { is_nonarchimedean := ?_ }
    intro U hU
    obtain ⟨H, _, hH⟩ :=
      ((Langlands.Topology.LocallyProfiniteProof.vanDantzig _).mp
        Langlands.Topology.isLocallyProfinite_of_mathlib).2 U hU
    exact ⟨H, hH⟩
  have hηopen : IsOpen (η.toMonoidHom.ker : Set (T.principalUnits n)) :=
    Langlands.isOpen_ker_of_continuous_complex_character η.toMonoidHom η.continuous
  let N : Subgroup K := η.toMonoidHom.ker.map f.toMonoidHom
  have hN : IsOpen (N : Set K) := hfopen _ hηopen
  let : Finite (K ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  let : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hker : N.comap f.toMonoidHom ≤ η.toMonoidHom.ker := by
    change (η.toMonoidHom.ker.map f.toMonoidHom).comap f.toMonoidHom ≤ _
    rw [Subgroup.comap_map_eq_self_of_injective hf]
  obtain ⟨ρ, hρpow, hρ⟩ := Langlands.Topology.exists_character_of_open_finite_quotient
    f η N hN N.index N.pow_index_mem hker
  let P : F.Carrierˣ →ₜ* F.Carrierˣ :=
    { toFun a := a * uniformizerUnit T ^ (-T.ord (a : F.Carrier))
      map_one' := by simp [T.ord_one]
      map_mul' := by
        intro a b
        simp only [Units.val_mul, T.ord_mul a.ne_zero b.ne_zero, neg_add, zpow_add]
        ac_rfl
      continuous_toFun := continuous_id.mul
        ((continuous_of_discreteTopology
          (f := fun k : ℤ => uniformizerUnit T ^ (-k))).comp (continuous_unit_ord T)) }
  have hPord (a : F.Carrierˣ) : T.ord ((P a : F.Carrierˣ) : F.Carrier) = 0 := by
    change T.ord ((a * uniformizerUnit T ^ (-T.ord (a : F.Carrier)) : F.Carrierˣ) :
      F.Carrier) = 0
    rw [Units.val_mul, T.ord_mul a.ne_zero (Units.ne_zero _),
      Units.val_zpow_eq_zpow_val, T.ord_zpow, uniformizerUnit_ord]
    ring
  have hPnorm (a : F.Carrierˣ) : P a ∈ K := by
    change T.normalizedAbs ((P a : F.Carrierˣ) : F.Carrier) = 1
    rw [T.normalizedAbs_of_ne_zero (P a).ne_zero, hPord]
    simp
  let Q : F.Carrierˣ →ₜ* K :=
    { toFun a := ⟨P a, hPnorm a⟩
      map_one' := by apply Subtype.ext; exact P.map_one
      map_mul' := fun a b => by apply Subtype.ext; exact P.map_mul a b
      continuous_toFun := P.continuous.subtype_mk _ }
  refine ⟨ρ.comp Q, ⟨N.index, Nat.pos_of_ne_zero N.index_ne_zero_of_finite, ?_⟩, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro a
    have h := congrArg (fun τ : K →ₜ* ℂˣ => τ (Q a)) hρpow
    simp only [ContinuousMonoidHom.pow_apply]
    change ρ (Q a) ^ N.index = 1
    simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.coe_one, Pi.one_apply] using h
  · intro z
    have hord : T.ord ((z : F.Carrierˣ) : F.Carrier) = 0 := by
      simp only [PadicField.TopologicalData.ord, z.property.1, WithZero.log_one, neg_zero]
    have hQ : Q z.val = f z := by
      apply Subtype.ext
      change z.val * uniformizerUnit T ^ (-T.ord ((z : F.Carrierˣ) : F.Carrier)) = z.val
      simp only [hord, neg_zero, zpow_zero, mul_one]
    change ρ (Q z.val) = η z
    rw [hQ]
    exact congrArg (fun τ : T.principalUnits n →ₜ* ℂˣ => τ z) hρ
  · have hQ : Q (uniformizerUnit T) = 1 := by
      apply Subtype.ext
      change uniformizerUnit T * uniformizerUnit T ^
        (-T.ord ((uniformizerUnit T : F.Carrierˣ) : F.Carrier)) = 1
      rw [uniformizerUnit_ord]
      simp
    change ρ (Q (uniformizerUnit T)) = 1
    rw [hQ, map_one]

end Langlands.HarmonicAnalysis
