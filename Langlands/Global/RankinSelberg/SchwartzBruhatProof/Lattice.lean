import Langlands.Global.RankinSelberg.SchwartzBruhatStatement
import Langlands.Global.Hecke.AdelicLattice
import Langlands.Global.IntegralFiniteAdeles
import Langlands.HarmonicAnalysis.PadicLatticeTopology

/-! # Lattices in the finite adeles

For a finitely supported `m : FinitePlace F →₀ ℤ`, the lattice
`L_m = ∏_v π_v^(-m v) 𝒪_v ⊆ 𝔸_f` is a compact open additive subgroup; these lattices form a
neighbourhood basis of `0`. A locally constant compactly supported function on `𝔸_f^n` is
invariant under some `L_m^n` and is a finite linear combination of indicators of cosets of
`L_m^n`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Topology Filter
open Langlands.Global.CompletionPadic
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

variable {F : Type u} [Field F] [NumberField F]

/-- The finite-adelic lattice `L_m = ∏_v π_v^(-m v) 𝒪_v`. -/
def finiteLattice (m : FinitePlace F →₀ ℤ) : AddSubgroup (FiniteAdeles F) where
  carrier := {b | ∀ v, b v ∈ (topologicalData v).additiveLattice (m v)}
  zero_mem' := fun v => ((topologicalData v).additiveLattice (m v)).zero_mem
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem mem_finiteLattice (m : FinitePlace F →₀ ℤ) (b : FiniteAdeles F) :
    b ∈ finiteLattice m ↔ ∀ v, b v ∈ (topologicalData v).additiveLattice (m v) := Iff.rfl

theorem finiteLattice_mono {m m' : FinitePlace F →₀ ℤ} (h : m ≤ m') :
    finiteLattice m ≤ finiteLattice m' :=
  fun _ hb v => (topologicalData v).additiveLattice_mono (h v) (hb v)

theorem isOpen_finiteLattice (m : FinitePlace F →₀ ℤ) :
    IsOpen (finiteLattice m : Set (FiniteAdeles F)) := by
  classical
  have h1 : IsOpen {b : FiniteAdeles F |
      ∀ v, v ∉ m.support → b v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
  have h2 : IsOpen (⋂ v ∈ m.support, {b : FiniteAdeles F |
      b v ∈ (topologicalData v).additiveLattice (m v)}) :=
    isOpen_biInter_finset fun v _ =>
      ((topologicalData v).isOpen_additiveLattice (m v)).preimage
        (RestrictedProduct.continuous_eval v)
  convert h1.inter h2 using 1
  ext b
  simp only [SetLike.mem_coe, mem_finiteLattice, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_iInter]
  constructor
  · intro hb
    refine ⟨fun v hv => ?_, fun v _ => hb v⟩
    have := hb v
    rwa [Finsupp.notMem_support_iff.mp hv, Hecke.mem_additiveLattice_zero_iff] at this
  · rintro ⟨hb1, hb2⟩ v
    by_cases hv : v ∈ m.support
    · exact hb2 v hv
    · rw [Finsupp.notMem_support_iff.mp hv, Hecke.mem_additiveLattice_zero_iff]
      exact hb1 v hv

theorem isClosed_finiteLattice (m : FinitePlace F →₀ ℤ) :
    IsClosed (finiteLattice m : Set (FiniteAdeles F)) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_finiteLattice m)

theorem isCompact_finiteLattice (m : FinitePlace F →₀ ℤ) :
    IsCompact (finiteLattice m : Set (FiniteAdeles F)) := by
  obtain ⟨x, hx0, hxmem⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger
    (Units.ne_zero (Hecke.latticeIdeal (-m)))
  set δ : F := algebraMap (𝓞 F) F x with hδ
  have hδ0 : δ ≠ 0 := by
    rw [hδ]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hx0
  have hδloc := (Hecke.mem_latticeIdeal_iff_forall_mem (-m) δ).mp hxmem
  set d : FiniteAdeles F := algebraMap F (FiniteAdeles F) δ
  set d' : FiniteAdeles F := algebraMap F (FiniteAdeles F) δ⁻¹
  have hdd : d' * d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ0, map_one]
  have hK : IsCompact ((fun b => d' * b) '' (integralFiniteAdeles F : Set (FiniteAdeles F))) :=
    (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)
  refine hK.of_isClosed_subset (isClosed_finiteLattice m) fun b hb => ?_
  refine ⟨d * b, ?_, show d' * (d * b) = b by rw [← mul_assoc, hdd, one_mul]⟩
  rw [SetLike.mem_coe, mem_integralFiniteAdeles]
  intro v
  have h := Hecke.mul_mem_additiveLattice v (hδloc v) (hb v)
  rw [Finsupp.neg_apply, neg_add_cancel, Hecke.mem_additiveLattice_zero_iff] at h
  exact h


/-- Every neighbourhood of zero in `𝔸_f` contains a lattice `L_m`. -/
theorem exists_finiteLattice_subset {U : Set (FiniteAdeles F)}
    (hU : U ∈ 𝓝 (0 : FiniteAdeles F)) :
    ∃ m : FinitePlace F →₀ ℤ, (finiteLattice m : Set (FiniteAdeles F)) ⊆ U := by
  classical
  have hopen : ∀ v : FinitePlace F,
      IsOpen ((v.adicCompletionIntegers F : ValuationSubring (v.adicCompletion F)) :
        Set (v.adicCompletion F)) :=
    fun v => Valued.isOpen_valuationSubring _
  have h0 := RestrictedProduct.nhds_zero_eq_map_structureMap
    (R := fun v : FinitePlace F => v.adicCompletion F)
    (B := fun v : FinitePlace F => v.adicCompletionIntegers F) hopen
  have hU' : U ∈ 𝓝 (RestrictedProduct.structureMap (fun v : FinitePlace F => v.adicCompletion F)
      (fun v : FinitePlace F => v.adicCompletionIntegers F) Filter.cofinite 0) := hU
  rw [h0] at hU'
  have hU'' : RestrictedProduct.structureMap (fun v : FinitePlace F => v.adicCompletion F)
      (fun v : FinitePlace F => v.adicCompletionIntegers F) Filter.cofinite ⁻¹' U ∈
        𝓝 (0 : (v : FinitePlace F) → v.adicCompletionIntegers F) := hU'
  rw [nhds_pi, Filter.mem_pi'] at hU''
  obtain ⟨I, t, ht, hIt⟩ := hU''
  have hloc : ∀ v : FinitePlace F, ∃ k : ℤ, ∀ x : v.adicCompletion F,
      x ∈ (topologicalData v).additiveLattice k →
        ∀ hx : x ∈ v.adicCompletionIntegers F,
          (⟨x, hx⟩ : v.adicCompletionIntegers F) ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).mp (ht v)
    obtain ⟨k, hk⟩ := (topologicalData v).exists_additiveLattice_subset (s := u) hu
    exact ⟨k, fun x hx hxO => hut (hk hx)⟩
  choose k hk using hloc
  let m : FinitePlace F →₀ ℤ := Finsupp.onFinset I
    (fun v => if v ∈ I then min (k v) 0 else 0) (by
      intro v hv
      by_contra h
      exact hv (by simp [h]))
  refine ⟨m, fun b hb => ?_⟩
  have hbO : ∀ v, b v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [← Hecke.mem_additiveLattice_zero_iff]
    refine (topologicalData v).additiveLattice_mono ?_ (hb v)
    simp only [m, Finsupp.onFinset_apply]
    split_ifs <;> omega
  have hb_eq : b = RestrictedProduct.structureMap _ _ Filter.cofinite
      (fun v => (⟨b v, hbO v⟩ : v.adicCompletionIntegers F)) := rfl
  rw [hb_eq]
  apply hIt
  intro v hv
  refine hk v (b v) ?_ (hbO v)
  refine (topologicalData v).additiveLattice_mono ?_ (hb v)
  simp only [m, Finsupp.onFinset_apply, Finset.mem_coe.mp hv, ↓reduceIte]
  omega

variable (n : ℕ)

/-- The vector lattice `L_m^n ⊆ 𝔸_f^n`. -/
def latticeVec (m : FinitePlace F →₀ ℤ) : AddSubgroup (Fin n → FiniteAdeles F) :=
  AddSubgroup.pi Set.univ fun _ => finiteLattice m

theorem mem_latticeVec {m : FinitePlace F →₀ ℤ} {z : Fin n → FiniteAdeles F} :
    z ∈ latticeVec n m ↔ ∀ j, z j ∈ finiteLattice m := by
  simp [latticeVec, AddSubgroup.mem_pi]

theorem coe_latticeVec (m : FinitePlace F →₀ ℤ) :
    (latticeVec n m : Set (Fin n → FiniteAdeles F)) =
      Set.univ.pi fun _ => (finiteLattice m : Set (FiniteAdeles F)) := by
  ext z
  simp [mem_latticeVec]

theorem isOpen_latticeVec (m : FinitePlace F →₀ ℤ) :
    IsOpen (latticeVec n m : Set (Fin n → FiniteAdeles F)) := by
  rw [coe_latticeVec]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_finiteLattice m

theorem isCompact_latticeVec (m : FinitePlace F →₀ ℤ) :
    IsCompact (latticeVec n m : Set (Fin n → FiniteAdeles F)) := by
  rw [coe_latticeVec]
  exact isCompact_univ_pi fun _ => isCompact_finiteLattice m

theorem isClosed_latticeVec (m : FinitePlace F →₀ ℤ) :
    IsClosed (latticeVec n m : Set (Fin n → FiniteAdeles F)) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_latticeVec n m)

theorem latticeVec_mono {m m' : FinitePlace F →₀ ℤ} (h : m ≤ m') :
    latticeVec n m ≤ latticeVec (F := F) n m' := fun _ hz =>
  (mem_latticeVec n).mpr fun j => finiteLattice_mono h ((mem_latticeVec n).mp hz j)

/-- Every neighbourhood of zero in `𝔸_f^n` contains a vector lattice `L_m^n`. -/
theorem exists_latticeVec_subset {V : Set (Fin n → FiniteAdeles F)}
    (hV : V ∈ 𝓝 (0 : Fin n → FiniteAdeles F)) :
    ∃ m : FinitePlace F →₀ ℤ, (latticeVec n m : Set (Fin n → FiniteAdeles F)) ⊆ V := by
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIt⟩ := hV
  obtain ⟨m, hm⟩ := exists_finiteLattice_subset (F := F)
    (Filter.iInter_mem.mpr ht : (⋂ j, t j) ∈ 𝓝 (0 : FiniteAdeles F))
  refine ⟨m, fun z hz => hIt fun j _ => ?_⟩
  exact Set.mem_iInter.mp (hm ((mem_latticeVec n).mp hz j)) j

/-- Every element of `F_v` lies in some lattice `L_v(k)`. -/
theorem exists_mem_additiveLattice (v : FinitePlace F) (x : FiniteCompletion F v) :
    ∃ k : ℤ, x ∈ (topologicalData v).additiveLattice k := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ ((topologicalData v).additiveLattice 0).zero_mem⟩
  · refine ⟨WithZero.log ((topologicalData v).discreteValuation x), ?_⟩
    rw [PadicField.TopologicalData.mem_additiveLattice,
      WithZero.exp_log (((topologicalData v).discreteValuation.ne_zero_iff).mpr hx)]

/-- A compact subset of `F_v^n` lies in some `L_v(k)^n`. -/
theorem exists_additiveLattice_pi_of_isCompact (v : FinitePlace F)
    {C : Set (Fin n → FiniteCompletion F v)} (hC : IsCompact C) :
    ∃ k : ℤ, ∀ z ∈ C, ∀ j, z j ∈ (topologicalData v).additiveLattice k := by
  obtain ⟨k, hk⟩ := hC.elim_directed_cover
    (fun k : ℤ => {z : Fin n → FiniteCompletion F v |
      ∀ j, z j ∈ (topologicalData v).additiveLattice k})
    (fun k => by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun j =>
        ((topologicalData v).isOpen_additiveLattice k).preimage (continuous_apply j))
    (fun z _ => by
      choose kz hkz using fun j => exists_mem_additiveLattice v (z j)
      obtain ⟨M, hM⟩ := Finset.exists_le (Finset.univ.image kz)
      exact Set.mem_iUnion.mpr ⟨M, fun j => (topologicalData v).additiveLattice_mono
        (hM _ (Finset.mem_image_of_mem kz (Finset.mem_univ j))) (hkz j)⟩)
    (Monotone.directed_le fun a b hab z hz j =>
      (topologicalData v).additiveLattice_mono hab (hz j))
  exact ⟨k, fun z hz => hk hz⟩

/-! ### Coset indicators in a topological additive group -/

section Generic

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

open scoped Classical in
/-- The indicator `1_(a + H)` of a coset. -/
def cosetIndicator (H : AddSubgroup G) (a x : G) : ℂ := if x - a ∈ H then 1 else 0

theorem isLocallyConstant_of_add_invariant {α : Type*} {f : G → α} (H : AddSubgroup G)
    (hH : IsOpen (H : Set G)) (hf : ∀ x, ∀ h ∈ H, f (x + h) = f x) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (H : Set G), hH.preimage (continuous_id.sub continuous_const),
    by simp, fun y hy => ?_⟩
  have := hf x (y - x) hy
  rwa [add_sub_cancel] at this

omit [TopologicalSpace G] [IsTopologicalAddGroup G] in
theorem cosetIndicator_add (H : AddSubgroup G) (a x : G) {h : G} (hh : h ∈ H) :
    cosetIndicator H a (x + h) = cosetIndicator H a x := by
  unfold cosetIndicator
  have : x + h - a ∈ H ↔ x - a ∈ H := by
    rw [show x + h - a = (x - a) + h by abel]
    exact H.add_mem_cancel_right hh
  by_cases hx : x - a ∈ H
  · simp [hx, this.mpr hx]
  · simp [hx, mt this.mp hx]

theorem isLocallyConstant_cosetIndicator (H : AddSubgroup G) (hH : IsOpen (H : Set G))
    (a : G) : IsLocallyConstant (cosetIndicator H a) :=
  isLocallyConstant_of_add_invariant H hH fun x _ hh => cosetIndicator_add H a x hh

theorem hasCompactSupport_cosetIndicator (H : AddSubgroup G) (hHo : IsOpen (H : Set G))
    (hHc : IsCompact (H : Set G)) (a : G) : HasCompactSupport (cosetIndicator H a) := by
  have hK : (fun x => x - a) ⁻¹' (H : Set G) = (fun y => y + a) '' (H : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨x - a, hx, sub_add_cancel x a⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  refine HasCompactSupport.intro' (K := (fun x => x - a) ⁻¹' (H : Set G)) ?_
    ((AddSubgroup.isClosed_of_isOpen H hHo).preimage (continuous_id.sub continuous_const))
    fun x hx => ?_
  · rw [hK]
    exact hHc.image (continuous_id.add continuous_const)
  · have hx' : ¬ (x - a ∈ H) := hx
    simp [cosetIndicator, hx']

/-- A locally constant compactly supported function is invariant under one member of a
neighbourhood basis of zero consisting of open subgroups. -/
theorem exists_invariant_of_basis {ι : Type*} (L : ι → AddSubgroup G)
    (hLo : ∀ i, IsOpen (L i : Set G))
    (hbasis : ∀ V ∈ 𝓝 (0 : G), ∃ i, (L i : Set G) ⊆ V) {α : Type*} [Zero α] {f : G → α}
    (hlc : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ i, ∀ x, ∀ h ∈ L i, f (x + h) = f x := by
  have hV : ∀ x, {d : G | f (x + d) = f x} ∈ 𝓝 (0 : G) := fun x =>
    ((hlc.isOpen_fiber (f x)).preimage (continuous_const.add continuous_id)).mem_nhds
      (by simp)
  choose i hi using fun x => hbasis _ (hV x)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (L (i x) : Set G))
    (fun x _ => ((hLo (i x)).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨j, hj⟩ := hbasis (⋂ x ∈ t, (L (i x) : Set G))
    ((Filter.biInter_finset_mem t).mpr fun x _ => (hLo (i x)).mem_nhds (L (i x)).zero_mem)
  have hsupp : ∀ y ∈ tsupport f, ∀ h ∈ L j, f (y + h) = f y := by
    intro y hy h hh
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    have hyx : y - x ∈ L (i x) := hyx
    have hhx : h ∈ L (i x) := Set.mem_iInter₂.mp (hj hh) x hx
    have e1 : f (x + (y - x + h)) = f x := hi x (add_mem hyx hhx)
    have e2 : f (x + (y - x)) = f x := hi x hyx
    rw [show x + (y - x + h) = y + h by abel] at e1
    rw [show x + (y - x) = y by abel] at e2
    rw [e1, e2]
  refine ⟨j, fun y h hh => ?_⟩
  by_cases hy : y ∈ tsupport f
  · exact hsupp y hy h hh
  · by_cases hyh : y + h ∈ tsupport f
    · have := hsupp (y + h) hyh (-h) (neg_mem hh)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

/-- A compactly supported function invariant under an open subgroup `H` is a finite linear
combination of indicators of cosets of `H`. -/
theorem exists_eq_sum_cosetIndicator (H : AddSubgroup G) (hHo : IsOpen (H : Set G))
    {f : G → ℂ} (hc : HasCompactSupport f) (hinv : ∀ x, ∀ h ∈ H, f (x + h) = f x) :
    ∃ s : Finset G, f = fun x => ∑ a ∈ s, f a * cosetIndicator H a x := by
  classical
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover
    (fun x => (fun y => y - x) ⁻¹' (H : Set G))
    (fun x _ => (hHo.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  let Q : Finset (G ⧸ H) := t.image (QuotientAddGroup.mk)
  refine ⟨Q.image Quotient.out, ?_⟩
  funext x
  rw [Finset.sum_image (fun q _ q' _ hqq => by
    simpa using congrArg (QuotientAddGroup.mk (s := H)) hqq)]
  have hind : ∀ q : G ⧸ H, cosetIndicator H q.out x =
      if (QuotientAddGroup.mk x : G ⧸ H) = q then 1 else 0 := by
    intro q
    unfold cosetIndicator
    congr 1
    apply propext
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq']
  simp only [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hx
  · have hmem : (QuotientAddGroup.mk x : G ⧸ H).out - x ∈ H := by
      rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq']
    have := hinv x _ hmem
    rw [add_sub_cancel] at this
    exact this.symm
  · refine image_eq_zero_of_notMem_tsupport fun hxs => hx ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hxs)
    exact Finset.mem_image.mpr ⟨y, hy, (QuotientAddGroup.eq_iff_sub_mem.mpr hxy).symm⟩

end Generic

/-- A locally constant compactly supported function on `𝔸_f^n` is invariant under some
`L_m^n`. -/
theorem exists_latticeVec_invariant {α : Type*} [Zero α]
    {f : (Fin n → FiniteAdeles F) → α} (hlc : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ m : FinitePlace F →₀ ℤ, ∀ x, ∀ h ∈ latticeVec n m, f (x + h) = f x :=
  exists_invariant_of_basis (latticeVec n) (isOpen_latticeVec n)
    (fun _ hV => exists_latticeVec_subset n hV) hlc hc

/-- The coset-indicator expansion of a locally constant compactly supported function on
`𝔸_f^n`, for one lattice `L_m^n`. -/
theorem exists_eq_sum_latticeVec {f : (Fin n → FiniteAdeles F) → ℂ}
    (hlc : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ (m : FinitePlace F →₀ ℤ) (s : Finset (Fin n → FiniteAdeles F)),
      f = fun x => ∑ a ∈ s, f a * cosetIndicator (latticeVec n m) a x := by
  obtain ⟨m, hm⟩ := exists_latticeVec_invariant n hlc hc
  obtain ⟨s, hs⟩ := exists_eq_sum_cosetIndicator _ (isOpen_latticeVec n m) hc hm
  exact ⟨m, s, hs⟩

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof
