import Langlands.Representation.Whittaker.JPSCoordinateUnitInvarianceStatement
import Langlands.Representation.Smooth.FiniteOperatorExpansionProof
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.LocalField.Topology
import Langlands.Topology.BaireFiniteDimensionalGermConstancyProof
import Langlands.Topology.CompactGroupClosedSubgroupCoverProof
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Topology.Baire.LocallyCompactRegular

noncomputable section

namespace Langlands.Whittaker

open JPSFunctionSpace

universe uF

private def coordinateThreshold (m : ℕ) : ℝ := 1 / (m + 1 : ℝ)

private theorem coordinateThreshold_pos (m : ℕ) : 0 < coordinateThreshold m :=
  one_div_pos.mpr (by positivity)

private theorem coordinateThreshold_antitone : Antitone coordinateThreshold := by
  intro m k hmk
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hmk 1

private theorem exists_coordinateThreshold_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, coordinateThreshold m < ε := exists_nat_one_div_lt hε

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private def normOneUnits (T : F.TopologicalData) : Subgroup F.Carrierˣ :=
  (show F.Carrierˣ →* ℝ from
    { toFun := fun u => T.normalizedAbs (u : F.Carrier)
      map_one' := by simp only [Units.val_one, T.normalizedAbs_one]
      map_mul' := fun u v => by simp only [Units.val_mul, T.normalizedAbs_mul] }).ker

private theorem normOneUnits_mem (T : F.TopologicalData) (u : F.Carrierˣ) :
    u ∈ normOneUnits T ↔ T.normalizedAbs (u : F.Carrier) = 1 := Iff.rfl

private theorem isCompact_normOneUnits (T : F.TopologicalData) :
    letI := T.topology
    IsCompact (normOneUnits T : Set F.Carrierˣ) :=
  T.isCompact_normalizedAbs_eq_one_units

private theorem isOpen_normOneUnits (T : F.TopologicalData) :
    letI := T.topology
    IsOpen (normOneUnits T : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have ho : IsOpen {x : F.Carrier | ValuativeRel.valuation F.Carrier x = 1} := by
    simpa only [Valuation.restrict_eq_one_iff] using
      (ValuativeRel.valuation F.Carrier).isOpen_sphere (r := 1) one_ne_zero
  have he : (normOneUnits T : Set F.Carrierˣ) =
      Units.val ⁻¹' {x : F.Carrier | ValuativeRel.valuation F.Carrier x = 1} := by
    ext u
    exact T.normalizedAbs_eq_one_iff_valuation_eq_one u
  rw [he]
  exact ho.preimage Units.continuous_val

private theorem germMap_exists_linear_section {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) :
    ∃ L : CoordinateGerm W T i →ₗ[ℂ] W.toSubmodule,
      ∀ q, germMap W T i (L q) = q := by
  let π : W.toSubmodule →ₗ[ℂ] CoordinateGerm W T i := (germMap W T i).toLinearMap
  obtain ⟨L, hL⟩ := π.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (germMap_surjective W T i))
  exact ⟨L, fun q => LinearMap.congr_fun hL q⟩

private def detectorLift {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n)
    (S : Submodule ℂ (Module.End ℂ (CoordinateGerm W T i)))
    (t : Finset (CoordinateGerm W T i))
    (L : CoordinateGerm W T i →ₗ[ℂ] W.toSubmodule) :
    S →ₗ[ℂ] ((t × Torus F n) → ℂ) where
  toFun A x := (L (A.val x.1)).val x.2
  map_add' A B := by
    funext x
    simp
  map_smul' c A := by
    funext x
    simp

private theorem detectorLift_restrict_injective {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n)
    (S : Submodule ℂ (Module.End ℂ (CoordinateGerm W T i)))
    (t : Finset (CoordinateGerm W T i))
    (ht : ∀ A ∈ S, (∀ q ∈ t, A q = 0) → A = 0)
    (L : CoordinateGerm W T i →ₗ[ℂ] W.toSubmodule)
    (hL : ∀ q, germMap W T i (L q) = q) (m : ℕ) :
    Function.Injective (fun A : S =>
      fun x : {x : t × Torus F n |
        T.normalizedAbs (x.2 i : F.Carrier) < coordinateThreshold m} =>
        detectorLift W T i S t L A x.val) := by
  intro A B hAB
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply ht _ (S.sub_mem A.property B.property)
  intro q hq
  have hzero : germMap W T i (L ((A.val - B.val) q)) = 0 := by
    apply (germMap_eq_zero_iff W T i _).mpr
    refine ⟨coordinateThreshold m, coordinateThreshold_pos m, ?_⟩
    intro a ha
    have h := congrFun hAB ⟨(⟨q, hq⟩, a), ha⟩
    change (L (A.val q)).val a = (L (B.val q)).val a at h
    simpa only [LinearMap.sub_apply, map_sub, Submodule.coe_sub, Pi.sub_apply] using
      sub_eq_zero.mpr h
  rw [hL] at hzero
  exact hzero

private theorem detectorLift_injective {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n)
    (S : Submodule ℂ (Module.End ℂ (CoordinateGerm W T i)))
    (t : Finset (CoordinateGerm W T i))
    (ht : ∀ A ∈ S, (∀ q ∈ t, A q = 0) → A = 0)
    (L : CoordinateGerm W T i →ₗ[ℂ] W.toSubmodule)
    (hL : ∀ q, germMap W T i (L q) = q) :
    Function.Injective (detectorLift W T i S t L) := by
  intro A B h
  apply detectorLift_restrict_injective W T i S t ht L hL 0
  funext x
  exact congrFun h x.val

private theorem continuous_coordinateEmbedding (T : F.TopologicalData)
    {n : ℕ} (i : Fin n) :
    letI := T.topology
    Continuous (coordinateEmbedding (F := F) i) := by
  let := T.topology
  apply continuous_pi
  intro j
  change Continuous (fun u : F.Carrierˣ => if j = i then u else 1)
  split_ifs
  · exact continuous_id
  · exact continuous_const

private theorem detectorTranslate_locallyConstant {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) (hloc : IsLocallyConstantSpace W T)
    (t : Finset (CoordinateGerm W T i))
    (L : CoordinateGerm W T i →ₗ[ℂ] W.toSubmodule)
    (K : Subgroup F.Carrierˣ) (x : t × Torus F n) :
    letI := T.topology
    IsLocallyConstant (fun u : K =>
      (L x.1).val (x.2 * coordinateEmbedding i (u : F.Carrierˣ))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (hloc (L x.1)).comp_continuous
    (continuous_const.mul ((continuous_coordinateEmbedding T i).comp continuous_subtype_val))

private theorem detectorTranslate_eventually {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n)
    (t : Finset (CoordinateGerm W T i))
    (L : CoordinateGerm W T i →ₗ[ℂ] W.toSubmodule)
    (hL : ∀ q, germMap W T i (L q) = q) (u : F.Carrierˣ) :
    ∃ m : ℕ, ∀ x : t × Torus F n,
      T.normalizedAbs (x.2 i : F.Carrier) < coordinateThreshold m →
        (L x.1).val (x.2 * coordinateEmbedding i u) =
          (L (sigma W T i u x.1)).val x.2 := by
  classical
  have hq (q : t) : ∃ m : ℕ, ∀ a : Torus F n,
      T.normalizedAbs (a i : F.Carrier) < coordinateThreshold m →
        (L q).val (a * coordinateEmbedding i u) =
          (L (sigma W T i u q)).val a := by
    have hzero : germMap W T i
        (coordinateRepresentation W i u (L q) - L (sigma W T i u q)) = 0 := by
      rw [map_sub, ← sigma_apply_mk, hL, hL, sub_self]
    obtain ⟨ε, hε, hvan⟩ := (germMap_eq_zero_iff W T i _).mp hzero
    obtain ⟨m, hm⟩ := exists_coordinateThreshold_lt hε
    refine ⟨m, ?_⟩
    intro a ha
    have h := hvan a (ha.trans hm)
    change (L q).val (a * coordinateEmbedding i u) -
      (L (sigma W T i u q)).val a = 0 at h
    exact sub_eq_zero.mp h
  choose k hk using hq
  refine ⟨Finset.univ.sup k, ?_⟩
  intro x hx
  exact hk x.1 x.2 (lt_of_lt_of_le hx
    (coordinateThreshold_antitone (Finset.le_sup (Finset.mem_univ x.1))))

private theorem exists_detectorBaireData {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) (hloc : IsLocallyConstantSpace W T)
    (hfinite : HasFiniteCoordinateOperatorSpan W T i) :
    letI := T.topology
    ∃ (t : Finset (CoordinateGerm W T i))
      (V : Submodule ℂ ((t × Torus F n) → ℂ))
      (f : normOneUnits T → (t × Torus F n) → ℂ)
      (v : normOneUnits T → V),
      FiniteDimensional ℂ V ∧
      (∀ m : ℕ, Function.Injective (fun z : V =>
        fun x : {x : t × Torus F n |
          T.normalizedAbs (x.2 i : F.Carrier) < coordinateThreshold m} =>
            (z : (t × Torus F n) → ℂ) x)) ∧
      (∀ x, IsLocallyConstant (fun u => f u x)) ∧
      (∀ u, ∃ m : ℕ, ∀ x,
        T.normalizedAbs (x.2 i : F.Carrier) < coordinateThreshold m →
          f u x = (v u : (t × Torus F n) → ℂ) x) ∧
      (∀ u w, v u = v w →
        sigma W T i (u : F.Carrierˣ) = sigma W T i (w : F.Carrierˣ)) := by
  classical
  let := T.topology
  let S := Submodule.span ℂ (Set.range (sigma W T i))
  let : FiniteDimensional ℂ S := hfinite
  obtain ⟨t, ht⟩ := Langlands.exists_finset_eq_zero_of_apply_eq_zero S
  obtain ⟨L, hL⟩ := germMap_exists_linear_section W T i
  let lift := detectorLift W T i S t L
  let V := lift.range
  let s (u : normOneUnits T) : S :=
    ⟨sigma W T i (u : F.Carrierˣ), Submodule.subset_span ⟨_, rfl⟩⟩
  let v (u : normOneUnits T) : V := ⟨lift (s u), ⟨s u, rfl⟩⟩
  let f (u : normOneUnits T) (x : t × Torus F n) : ℂ :=
    (L x.1).val (x.2 * coordinateEmbedding i (u : F.Carrierˣ))
  refine ⟨t, V, f, v, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro m a b hab
    obtain ⟨A, hA⟩ := a.property
    obtain ⟨B, hB⟩ := b.property
    have hAB : A = B := by
      apply detectorLift_restrict_injective W T i S t ht L hL m
      funext x
      change lift A x.val = lift B x.val
      rw [hA, hB]
      exact congrFun hab x
    exact Subtype.ext (hA.symm.trans ((congrArg lift hAB).trans hB))
  · exact detectorTranslate_locallyConstant W T i hloc t L (normOneUnits T)
  · intro u
    exact detectorTranslate_eventually W T i t L hL u
  · intro u w huw
    have h := detectorLift_injective W T i S t ht L hL (congrArg Subtype.val huw)
    exact congrArg Subtype.val h

private theorem compactOpen_kernel_of_constancy {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n)
    (hconst : letI := T.topology
      ∃ O : Set (normOneUnits T), IsOpen O ∧ O.Nonempty ∧
        ∀ u ∈ O, ∀ v ∈ O,
          sigma W T i (u : F.Carrierˣ) = sigma W T i (v : F.Carrierˣ)) :
    letI := T.topology
    ∃ U : Subgroup F.Carrierˣ, IsOpen (U : Set F.Carrierˣ) ∧
      IsCompact (U : Set F.Carrierˣ) ∧ U ≤ normOneUnits T ∧
      ∀ u ∈ U, ∀ q : CoordinateGerm W T i, sigma W T i u q = q := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let K := normOneUnits T
  let ρ := (sigma W T i).comp K.subtype
  let H := ρ.ker
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_normOneUnits T)
  obtain ⟨O, hO, ⟨u₀, hu₀⟩, hval⟩ := hconst
  have hH : IsOpen (H : Set K) := by
    apply Subgroup.isOpen_of_mem_nhds H
    have hN : IsOpen ((fun u : K => u₀ * u) ⁻¹' O) :=
      hO.preimage (continuous_const.mul continuous_id)
    have hN1 : (1 : K) ∈ (fun u : K => u₀ * u) ⁻¹' O := by
      change u₀ * 1 ∈ O
      simpa only [mul_one] using hu₀
    apply Filter.mem_of_superset (hN.mem_nhds hN1)
    intro u hu
    have heq : ρ (u₀ * u) = ρ u₀ := hval _ hu _ hu₀
    change ρ u = 1
    have h := MonoidHom.mem_ker.mp ((MonoidHom.eq_iff ρ).mp heq)
    simpa only [inv_mul_cancel_left] using h
  let U := H.map K.subtype
  have hUopen : IsOpen (U : Set F.Carrierˣ) :=
    (isOpen_normOneUnits T).isOpenMap_subtype_val _ hH
  have hUcompact : IsCompact (U : Set F.Carrierˣ) :=
    (H.isClosed_of_isOpen hH).isCompact.image continuous_subtype_val
  refine ⟨U, hUopen, hUcompact, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact v.property
  · intro u hu q
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
    exact LinearMap.congr_fun hv q

private def coordinateThresholdStabilizer {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) (f : W.toSubmodule)
    (U : Subgroup F.Carrierˣ) (hU : U ≤ normOneUnits T) (m : ℕ) : Subgroup U where
  carrier := {u | ∀ a : Torus F n,
    T.normalizedAbs (a i : F.Carrier) < coordinateThreshold m →
      f.val (a * coordinateEmbedding i (u : F.Carrierˣ)) = f.val a}
  one_mem' := by
    intro a ha
    simp
  mul_mem' := by
    intro u v hu hv a ha
    have hau : T.normalizedAbs ((a * coordinateEmbedding i (u : F.Carrierˣ)) i :
        F.Carrier) < coordinateThreshold m := by
      simpa only [Pi.mul_apply, coordinateEmbedding_same, Units.val_mul,
        T.normalizedAbs_mul, (normOneUnits_mem T u).mp (hU u.property), mul_one] using ha
    calc
      f.val (a * coordinateEmbedding i ((u * v : U) : F.Carrierˣ)) =
          f.val ((a * coordinateEmbedding i (u : F.Carrierˣ)) *
            coordinateEmbedding i (v : F.Carrierˣ)) := by
        rw [Subgroup.coe_mul, map_mul, mul_assoc]
      _ = f.val (a * coordinateEmbedding i (u : F.Carrierˣ)) := hv _ hau
      _ = f.val a := hu a ha
  inv_mem' := by
    intro u hu a ha
    have hau : T.normalizedAbs ((a * coordinateEmbedding i ((u⁻¹ : U) : F.Carrierˣ)) i :
        F.Carrier) < coordinateThreshold m := by
      simpa only [Pi.mul_apply, coordinateEmbedding_same, Units.val_mul,
        T.normalizedAbs_mul, (normOneUnits_mem T (u⁻¹ : U)).mp (hU (u⁻¹).property),
        mul_one] using ha
    have h := hu (a * coordinateEmbedding i ((u⁻¹ : U) : F.Carrierˣ)) hau
    simpa only [Subgroup.coe_inv, mul_assoc, ← map_mul, inv_mul_cancel, map_one,
      mul_one] using h.symm

private theorem coordinateThresholdStabilizer_monotone {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) (f : W.toSubmodule)
    (U : Subgroup F.Carrierˣ) (hU : U ≤ normOneUnits T) :
    Monotone (coordinateThresholdStabilizer W T i f U hU) := by
  intro m k hmk u hu a ha
  exact hu a (lt_of_lt_of_le ha (coordinateThreshold_antitone hmk))

private theorem coordinateThresholdStabilizer_closed {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) (f : W.toSubmodule)
    (hloc : IsLocallyConstantSpace W T)
    (U : Subgroup F.Carrierˣ) (hU : U ≤ normOneUnits T) (m : ℕ) :
    letI := T.topology
    IsClosed (coordinateThresholdStabilizer W T i f U hU m : Set U) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hcont (a : Torus F n) :
      Continuous (fun u : U => f.val (a * coordinateEmbedding i (u : F.Carrierˣ))) :=
    (hloc f).continuous.comp (continuous_const.mul
      ((continuous_coordinateEmbedding T i).comp continuous_subtype_val))
  change IsClosed {u : U | ∀ a : Torus F n,
    T.normalizedAbs (a i : F.Carrier) < coordinateThreshold m →
      f.val (a * coordinateEmbedding i (u : F.Carrierˣ)) = f.val a}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_eq (hcont a) continuous_const

private theorem coordinateThresholdStabilizer_cover {n : ℕ} (W : FunctionSpace F n)
    (T : F.TopologicalData) (i : Fin n) (f : W.toSubmodule)
    (U : Subgroup F.Carrierˣ) (hU : U ≤ normOneUnits T)
    (hker : ∀ u ∈ U, ∀ q : CoordinateGerm W T i, sigma W T i u q = q) :
    ∀ u : U, ∃ m : ℕ, u ∈ coordinateThresholdStabilizer W T i f U hU m := by
  intro u
  have hzero : germMap W T i (coordinateRepresentation W i (u : F.Carrierˣ) f - f) = 0 := by
    rw [map_sub, ← sigma_apply_mk, hker u u.property, sub_self]
  obtain ⟨ε, hε, hvan⟩ := (germMap_eq_zero_iff W T i _).mp hzero
  obtain ⟨m, hm⟩ := exists_coordinateThreshold_lt hε
  refine ⟨m, ?_⟩
  intro a ha
  have h := hvan a (ha.trans hm)
  change f.val (a * coordinateEmbedding i (u : F.Carrierˣ)) - f.val a = 0 at h
  exact sub_eq_zero.mp h

/-- One compact open norm-one subgroup fixes all actual coordinate germs and,
for each representative, fixes its values below one threshold uniform in all
torus tuples and all members of that subgroup. -/
theorem jpsCoordinateUnitInvariance :
    JPSCoordinateUnitInvarianceStatement.{uF} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro n W i hloc hfinite
  obtain ⟨t, V, fdet, v, hV, hinj, hlocdet, hevent, hfaith⟩ :=
    exists_detectorBaireData W T i hloc hfinite
  let : FiniteDimensional ℂ V := hV
  let : CompactSpace (normOneUnits T) :=
    isCompact_iff_compactSpace.mp (isCompact_normOneUnits T)
  let D (m : ℕ) : Set (t × Torus F n) :=
    {x | T.normalizedAbs (x.2 i : F.Carrier) < coordinateThreshold m}
  have hD : Antitone D := by
    intro m k hmk x hx
    exact lt_of_lt_of_le hx (coordinateThreshold_antitone hmk)
  obtain ⟨O, hO, hOne, hOv⟩ :=
    Langlands.Topology.baireFiniteDimensionalGermConstancy.{uF,uF}
      (t × Torus F n) (normOneUnits T) D hD V hinj fdet v hlocdet hevent
  have hconst : ∃ O : Set (normOneUnits T), IsOpen O ∧ O.Nonempty ∧
      ∀ u ∈ O, ∀ w ∈ O,
        sigma W T i (u : F.Carrierˣ) = sigma W T i (w : F.Carrierˣ) :=
    ⟨O, hO, hOne, fun u hu w hw => hfaith u w (hOv u hu w hw)⟩
  obtain ⟨U, hUopen, hUcompact, hUnorm, hUker⟩ :=
    compactOpen_kernel_of_constancy W T i hconst
  refine ⟨U, hUopen, hUcompact, ?_, hUker, ?_⟩
  · intro u hu
    exact (normOneUnits_mem T u).mp (hUnorm hu)
  · intro f
    let : CompactSpace U := isCompact_iff_compactSpace.mp hUcompact
    obtain ⟨m, hm⟩ := Langlands.Topology.compactGroupClosedSubgroupCover.{uF}
      U (coordinateThresholdStabilizer W T i f U hUnorm)
      (coordinateThresholdStabilizer_monotone W T i f U hUnorm)
      (coordinateThresholdStabilizer_closed W T i f hloc U hUnorm)
      (coordinateThresholdStabilizer_cover W T i f U hUnorm hUker)
    refine ⟨coordinateThreshold m, coordinateThreshold_pos m, ?_⟩
    intro a ha u hu
    have hmem : (⟨u, hu⟩ : U) ∈ coordinateThresholdStabilizer W T i f U hUnorm m := by
      rw [hm]
      trivial
    exact hmem a ha

end Langlands.Whittaker
