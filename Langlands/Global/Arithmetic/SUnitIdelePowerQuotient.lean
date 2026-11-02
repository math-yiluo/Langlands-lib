import Langlands.Global.Arithmetic.SUnitIdeleTopology
import Langlands.ClassField.Global.LocalPowerIndex
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Positive-power quotients of S-unit ideles -/

noncomputable section

universe u v w

namespace Langlands.Global.Arithmetic.SUnitIdelePowerQuotient

open NumberField IsDedekindDomain
open Langlands.ClassField.Global SUnitIdeleTopology

section QuotientTopology

/-- Power quotients commute with arbitrary products in the quotient topology. -/
def piPowerQuotientEquiv {ι : Type v} (A : ι → Type u) [∀ i, CommGroup (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalGroup (A i)] (m : ℕ) :
    (((i : ι) → A i) ⧸ (powMonoidHom m).range) ≃ₜ
      ((i : ι) → A i ⧸ (powMonoidHom m).range) := by
  let e := QuotientGroup.mulEquivPiModRangePowMonoidHom A m
  have hq := QuotientGroup.isOpenQuotientMap_mk
    (G := (i : ι) → A i) (N := (powMonoidHom m).range)
  let q (i : ι) : A i → A i ⧸ (powMonoidHom (α := A i) m).range := QuotientGroup.mk
  have hqi (i : ι) : IsOpenQuotientMap (q i) := QuotientGroup.isOpenQuotientMap_mk
  have hp : IsOpenQuotientMap (Pi.map q) := IsOpenQuotientMap.piMap (f := q) hqi
  have hcomp : (e ∘ (QuotientGroup.mk : ((i : ι) → A i) →
      ((i : ι) → A i) ⧸ (powMonoidHom m).range)) =
      Pi.map (fun i => (QuotientGroup.mk : A i → A i ⧸ (powMonoidHom m).range)) := by
    funext x i
    exact congrFun (QuotientGroup.mulEquivPiModRangePowMonoidHom_apply A m x) i
  have hc : Continuous e := hq.continuous_comp_iff.1 (by rw [hcomp]; exact hp.continuous)
  have ho : IsOpenMap e := hq.isOpenMap_iff.2 (by rw [hcomp]; exact hp.isOpenMap)
  exact e.toEquiv.toHomeomorphOfContinuousOpen hc ho

/-- Transport the quotient topology along a continuous multiplicative equivalence. -/
def powerQuotientCongr {G : Type u} {H : Type v} [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (m : ℕ) :
    (G ⧸ (powMonoidHom m).range) ≃ₜ (H ⧸ (powMonoidHom m).range) := by
  let f := QuotientGroup.congr (powMonoidHom (α := G) m).range
    (powMonoidHom (α := H) m).range e.toMulEquiv (e.toMulEquiv.map_range_powMonoidHom m)
  exact
    { f.toEquiv with
      continuous_toFun := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.1
        (QuotientGroup.continuous_mk.comp e.continuous)
      continuous_invFun := QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.1
        (QuotientGroup.continuous_mk.comp e.symm.continuous) }

/-- Power quotients commute with binary products in the quotient topology. -/
def prodPowerQuotientEquiv (G : Type u) (H : Type v) [CommGroup G] [CommGroup H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (m : ℕ) : ((G × H) ⧸ (powMonoidHom m).range) ≃ₜ
      (G ⧸ (powMonoidHom m).range) × (H ⧸ (powMonoidHom m).range) := by
  have heq : (powMonoidHom (α := G × H) m).range =
      (powMonoidHom (α := G) m).range.prod (powMonoidHom (α := H) m).range := by
    ext x
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  rw [heq]
  let e := QuotientGroup.prodMulEquiv (powMonoidHom (α := G) m).range
    (powMonoidHom (α := H) m).range
  have hq := QuotientGroup.isOpenQuotientMap_mk (G := G × H)
    (N := (powMonoidHom (α := G) m).range.prod (powMonoidHom (α := H) m).range)
  have hp := (QuotientGroup.isOpenQuotientMap_mk
    (G := G) (N := (powMonoidHom m).range)).prodMap
    (QuotientGroup.isOpenQuotientMap_mk (G := H) (N := (powMonoidHom m).range))
  exact e.toEquiv.toHomeomorphOfContinuousOpen
    (hq.continuous_comp_iff.1 hp.continuous) (hq.isOpenMap_iff.2 hp.isOpenMap)

/-- Transport the three profinite-space properties along a homeomorphism. -/
theorem profinite_of_homeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y)
    (h : T2Space X ∧ CompactSpace X ∧ TotallyDisconnectedSpace X) :
    T2Space Y ∧ CompactSpace Y ∧ TotallyDisconnectedSpace Y := by
  let := h.1
  let := h.2.1
  let := h.2.2
  exact ⟨e.t2Space, e.compactSpace, e.totallyDisconnectedSpace⟩

/-- An arbitrary product of profinite power quotients is a profinite power quotient. -/
theorem pi_powerQuotient_profinite {ι : Type v} (A : ι → Type u)
    [∀ i, CommGroup (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalGroup (A i)] (m : ℕ)
    (h : ∀ i, T2Space (A i ⧸ (powMonoidHom m).range) ∧
      CompactSpace (A i ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (A i ⧸ (powMonoidHom m).range)) :
    T2Space (((i : ι) → A i) ⧸ (powMonoidHom m).range) ∧
      CompactSpace (((i : ι) → A i) ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (((i : ι) → A i) ⧸ (powMonoidHom m).range) := by
  let (i : ι) : T2Space (A i ⧸ (powMonoidHom m).range) := (h i).1
  let (i : ι) : CompactSpace (A i ⧸ (powMonoidHom m).range) := (h i).2.1
  let (i : ι) : TotallyDisconnectedSpace (A i ⧸ (powMonoidHom m).range) := (h i).2.2
  exact profinite_of_homeomorph (piPowerQuotientEquiv A m).symm
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- Binary products preserve profinite power quotients. -/
theorem prod_powerQuotient_profinite (G : Type u) (H : Type v)
    [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] (m : ℕ)
    (hG : T2Space (G ⧸ (powMonoidHom m).range) ∧
      CompactSpace (G ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (G ⧸ (powMonoidHom m).range))
    (hH : T2Space (H ⧸ (powMonoidHom m).range) ∧
      CompactSpace (H ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (H ⧸ (powMonoidHom m).range)) :
    T2Space ((G × H) ⧸ (powMonoidHom m).range) ∧
      CompactSpace ((G × H) ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace ((G × H) ⧸ (powMonoidHom m).range) := by
  let := hG.1
  let := hG.2.1
  let := hG.2.2
  let := hH.1
  let := hH.2.1
  let := hH.2.2
  exact profinite_of_homeomorph (prodPowerQuotientEquiv G H m).symm
    ⟨inferInstance, inferInstance, inferInstance⟩

/-- In the top subgroup, the power range is the preimage of the ambient power range. -/
theorem top_powers_eq_comap (G : Type u) [CommGroup G] (m : ℕ) :
    (powMonoidHom (α := (⊤ : Subgroup G)) m).range =
      (powMonoidHom (α := G) m).range.comap (⊤ : Subgroup G).subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y, Subgroup.mem_top y⟩, Subtype.ext hy⟩

end QuotientTopology

section Local

variable {K : Type u} [Field K] [NumberField K]

/-- Positive powers form an open subgroup in every finite completion. -/
theorem isOpen_finite_powers (v : FinitePlace K) (m : ℕ) (hm : m ≠ 0) :
    IsOpen ((powMonoidHom (α := (FiniteCompletion K v)ˣ) m).range :
      Set (FiniteCompletion K v)ˣ) := by
  let _ : NontriviallyNormedField (v.adicCompletion K) :=
    Valued.toNontriviallyNormedField (v.adicCompletion K) (WithZero (Multiplicative ℤ))
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  exact (powMonoidHom (α := (FiniteCompletion K v)ˣ) m).range.isOpen_of_mem_nhds
    (Langlands.Global.AdelicFunctoriality.range_pow_mem_nhds_one hm)

/-- A root of a valuation unit is a valuation unit for a nonzero natural exponent. -/
theorem localUnitPowers_eq_comap (v : FinitePlace K) (m : ℕ) (hm : m ≠ 0) :
    localUnitPowers v m = ((powMonoidHom (α := (FiniteCompletion K v)ˣ) m).range).comap
      (localUnits v).subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, rfl⟩
  · rintro ⟨y, hy⟩
    have hyval : Valued.v (y : FiniteCompletion K v) = 1 := by
      have hp : Valued.v (y : FiniteCompletion K v) ^ m = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val]
        change Valued.v ((y ^ m : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) = 1
        rw [show y ^ m = x.1 from hy]
        exact (mem_localUnits_iff v _).1 x.2
      exact (pow_eq_one_iff.1 hp).resolve_right hm
    exact ⟨⟨y, (mem_localUnits_iff v _).2 hyval⟩, Subtype.ext hy⟩

/-- Positive powers are open within the valuation-unit group. -/
theorem isOpen_localUnitPowers (v : FinitePlace K) (m : ℕ) (hm : m ≠ 0) :
    IsOpen (localUnitPowers v m : Set (localUnits v)) := by
  rw [localUnitPowers_eq_comap v m hm]
  exact (isOpen_finite_powers v m hm).preimage continuous_subtype_val

/-- Positive powers are open in every infinite completion unit group. -/
theorem isOpen_infinite_powers (v : InfinitePlace K) (m : ℕ) (hm : m ≠ 0) :
    IsOpen ((powMonoidHom (α := v.Completionˣ) m).range : Set v.Completionˣ) := by
  let _ : NontriviallyNormedField v.Completion :=
    { (inferInstance : NormedField v.Completion) with
      non_trivial := by
        refine ⟨2, ?_⟩
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.extensionEmbedding v)) (2 : v.Completion)
        rw [← h]
        norm_num only [map_ofNat, Complex.norm_ofNat] }
  have : CharZero v.Completion :=
    charZero_of_injective_algebraMap (algebraMap K v.Completion).injective
  exact (powMonoidHom (α := v.Completionˣ) m).range.isOpen_of_mem_nhds
    (Langlands.Global.AdelicFunctoriality.range_pow_mem_nhds_one hm)

/-- Every positive power subgroup in an infinite completion has finite index,
including the sign component at a real place. -/
theorem infinite_power_finiteIndex
    {K : Type u} [Field K] (w : NumberField.InfinitePlace K)
    (d : ℕ) (hd : d ≠ 0) :
    (powMonoidHom (α := w.Completionˣ) d).range.FiniteIndex := by
  classical
  change (infiniteUnitPowers w d).FiniteIndex
  by_cases hw : w.IsReal
  · let φ := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have key : ∀ y : w.Completionˣ,
        0 < φ (y : w.Completion) → y ∈ infiniteUnitPowers w d := by
      intro y hy
      have hs : φ.symm (φ (y : w.Completion) ^ ((d : ℝ)⁻¹)) ≠ 0 := by
        simp [(Real.rpow_pos_of_pos hy _).ne']
      refine ⟨Units.mk0 _ hs, ?_⟩
      apply Units.ext
      apply φ.injective
      simp [powMonoidHom, Real.rpow_inv_natCast_pow hy.le hd]
    have hsign : ∀ x : w.Completionˣ,
        x ∈ infiniteUnitPowers w d ∨ -x ∈ infiniteUnitPowers w d := by
      intro x
      have hx : φ (x : w.Completion) ≠ 0 := by simp
      rcases hx.lt_or_gt with h | h
      · right
        apply key
        simpa using h
      · left
        exact key x h
    let : Finite (w.Completionˣ ⧸ infiniteUnitPowers w d) := by
      refine Finite.of_surjective (fun b : Bool =>
        if b then (QuotientGroup.mk 1 : w.Completionˣ ⧸ infiniteUnitPowers w d)
        else QuotientGroup.mk (-1)) ?_
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rcases hsign x with h | h
        · refine ⟨true, ?_⟩
          simp only [ite_true]
          rw [QuotientGroup.eq]
          simpa using h
        · refine ⟨false, ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          rw [QuotientGroup.eq]
          simpa using h
    exact Subgroup.finiteIndex_of_finite_quotient
  · rw [infiniteUnitPowers_eq_top_of_isComplex w
      (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw) d hd]
    infer_instance

/-- The quotient at an infinite place is finite and discrete, hence profinite. -/
theorem infinite_powerQuotient_profinite (v : InfinitePlace K) (m : ℕ) (hm : m ≠ 0) :
    T2Space (v.Completionˣ ⧸ (powMonoidHom m).range) ∧
      CompactSpace (v.Completionˣ ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (v.Completionˣ ⧸ (powMonoidHom m).range) := by
  let := infinite_power_finiteIndex v m hm
  let := QuotientGroup.discreteTopology (isOpen_infinite_powers v m hm)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Each finite-place factor has an open positive-power subgroup. -/
theorem isOpen_factor_powers (S : Finset (FinitePlace K)) (v : FinitePlace K)
    (m : ℕ) (hm : m ≠ 0) :
    IsOpen ((powMonoidHom (α := localFactor K S v) m).range : Set (localFactor K S v)) := by
  classical
  by_cases hv : v ∈ S
  · rw [show localFactor K S v = ⊤ by simp [localFactor, hv]]
    rw [top_powers_eq_comap]
    exact (isOpen_finite_powers v m hm).preimage continuous_subtype_val
  · rw [show localFactor K S v = localUnits v by simp [localFactor, hv]]
    exact isOpen_localUnitPowers v m hm

/-- Each finite-place factor has finite positive-power index. -/
theorem factor_power_finiteIndex (S : Finset (FinitePlace K)) (v : FinitePlace K)
    (m : ℕ) (hm : m ≠ 0) : (powMonoidHom (α := localFactor K S v) m).range.FiniteIndex := by
  classical
  by_cases hv : v ∈ S
  · rw [show localFactor K S v = ⊤ by simp [localFactor, hv]]
    rw [top_powers_eq_comap]
    let : (powMonoidHom (α := (FiniteCompletion K v)ˣ) m).range.FiniteIndex :=
      localPowers_finiteIndex v m hm
    infer_instance
  · rw [show localFactor K S v = localUnits v by simp [localFactor, hv]]
    exact localUnitPowers_finiteIndex v m hm

/-- Each finite-place factor power quotient is finite discrete, hence profinite. -/
theorem factor_powerQuotient_profinite (S : Finset (FinitePlace K)) (v : FinitePlace K)
    (m : ℕ) (hm : m ≠ 0) :
    T2Space (localFactor K S v ⧸ (powMonoidHom m).range) ∧
      CompactSpace (localFactor K S v ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (localFactor K S v ⧸ (powMonoidHom m).range) := by
  let := factor_power_finiteIndex S v m hm
  let := QuotientGroup.discreteTopology (isOpen_factor_powers S v m hm)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Local

section SUnit

variable (K : Type u) [Field K] [NumberField K]

/-- Power quotients of the whole infinite idele factor are profinite. -/
theorem infiniteAdeles_powerQuotient_profinite (m : ℕ) (hm : m ≠ 0) :
    T2Space ((InfiniteAdeles K)ˣ ⧸ (powMonoidHom m).range) ∧
      CompactSpace ((InfiniteAdeles K)ˣ ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace ((InfiniteAdeles K)ˣ ⧸ (powMonoidHom m).range) := by
  exact profinite_of_homeomorph (powerQuotientCongr ContinuousMulEquiv.piUnits m).symm
    (pi_powerQuotient_profinite (fun v : InfinitePlace K => v.Completionˣ) m
      (fun v => infinite_powerQuotient_profinite v m hm))

/-- The product model's positive-power quotient is profinite. -/
theorem model_powerQuotient_profinite (S : Finset (FinitePlace K)) (m : ℕ) (hm : m ≠ 0) :
    T2Space (model K S ⧸ (powMonoidHom m).range) ∧
      CompactSpace (model K S ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (model K S ⧸ (powMonoidHom m).range) := by
  exact prod_powerQuotient_profinite (InfiniteAdeles K)ˣ (finiteModel K S) m
    (infiniteAdeles_powerQuotient_profinite K m hm)
    (pi_powerQuotient_profinite (fun v => localFactor K S v) m
      (fun v => factor_powerQuotient_profinite S v m hm))

/-- The actual S-unit idele subgroup has profinite positive-power quotients. -/
theorem sUnitIdeles_powerQuotient_profinite (S : Finset (FinitePlace K))
    (m : ℕ) (hm : m ≠ 0) :
    T2Space (IdeleSUnits.sUnitIdeles K S ⧸ (powMonoidHom m).range) ∧
      CompactSpace (IdeleSUnits.sUnitIdeles K S ⧸ (powMonoidHom m).range) ∧
      TotallyDisconnectedSpace (IdeleSUnits.sUnitIdeles K S ⧸ (powMonoidHom m).range) := by
  exact profinite_of_homeomorph (powerQuotientCongr (productEquiv K S) m)
    (model_powerQuotient_profinite K S m hm)

end SUnit

end Langlands.Global.Arithmetic.SUnitIdelePowerQuotient
