import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Lattice

/-! # The restricted-tensor description of `S(𝔸^n)`

The span of the pure tensors `Φ_∞ ⊗ Φ_f` equals the span of the restricted pure tensors
`Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`. A locally constant compactly supported `Φ_f`
is a finite combination of indicators of cosets `a + L_m^n`, and `1_(a + L_m^n)` is a
restricted pure tensor; conversely the finite part of a restricted pure tensor is locally
constant with compact support contained in a vector lattice `L_m^n`.
-/

noncomputable section
universe u
open NumberField MeasureTheory Topology Filter
open Langlands.Global.CompletionPadic
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

variable {F : Type u} [Field F] [NumberField F] (n : ℕ)

/-! ### Generic locally constant functions -/

theorem isLocallyConstant_ite_of_isClopen {X : Type*} [TopologicalSpace X] {p : X → Prop}
    [DecidablePred p] (hUo : IsOpen {x | p x}) (hUc : IsClosed {x | p x}) {f : X → ℂ}
    (hf : IsLocallyConstant f) : IsLocallyConstant (fun x => if p x then f x else 0) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨V, hVo, hxV, hV⟩ := (IsLocallyConstant.iff_exists_open f).mp hf x
  by_cases hx : p x
  · refine ⟨{x | p x} ∩ V, hUo.inter hVo, ⟨hx, hxV⟩, fun y hy => ?_⟩
    have hy1 : p y := hy.1
    simp [hy1, hx, hV y hy.2]
  · refine ⟨{x | p x}ᶜ, hUc.isOpen_compl, hx, fun y hy => ?_⟩
    have hy1 : ¬ p y := hy
    simp [hx, hy1]

theorem isLocallyConstant_finset_prod {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    {f : ι → X → ℂ} (hf : ∀ i ∈ s, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∏ i ∈ s, f i x) := by
  have h := Finset.prod_induction f IsLocallyConstant (fun a b ha hb => ha.mul hb)
    IsLocallyConstant.one hf
  convert h using 1
  funext x
  rw [Finset.prod_apply]

/-! ### Local vector lattices -/

/-- The local vector lattice `L_v(k)^n = (π_v^(-k) 𝒪_v)^n ⊆ F_v^n`. -/
def localLatticeVec (v : FinitePlace F) (k : ℤ) : AddSubgroup (Fin n → FiniteCompletion F v) :=
  AddSubgroup.pi Set.univ fun _ => (topologicalData v).additiveLattice k

theorem mem_localLatticeVec {v : FinitePlace F} {k : ℤ} {z : Fin n → FiniteCompletion F v} :
    z ∈ localLatticeVec n v k ↔ ∀ j, z j ∈ (topologicalData v).additiveLattice k := by
  simp [localLatticeVec, AddSubgroup.mem_pi]

theorem coe_localLatticeVec (v : FinitePlace F) (k : ℤ) :
    (localLatticeVec n v k : Set (Fin n → FiniteCompletion F v)) =
      Set.univ.pi fun _ => ((topologicalData v).additiveLattice k : Set (FiniteCompletion F v)) := by
  ext z
  simp [mem_localLatticeVec]

theorem isOpen_localLatticeVec (v : FinitePlace F) (k : ℤ) :
    IsOpen (localLatticeVec n v k : Set (Fin n → FiniteCompletion F v)) := by
  rw [coe_localLatticeVec]
  exact isOpen_set_pi Set.finite_univ fun _ _ => (topologicalData v).isOpen_additiveLattice k

theorem isCompact_localLatticeVec (v : FinitePlace F) (k : ℤ) :
    IsCompact (localLatticeVec n v k : Set (Fin n → FiniteCompletion F v)) := by
  rw [coe_localLatticeVec]
  exact isCompact_univ_pi fun _ => (topologicalData v).isCompact_additiveLattice k

/-! ### Vectors integral outside a finite set of places -/

/-- The subgroup of `𝔸_f^n` of vectors whose coordinates are integral at every finite place
outside `S`. -/
def integralVecOutside (S : Finset (FinitePlace F)) : AddSubgroup (Fin n → FiniteAdeles F) where
  carrier := {z | ∀ v ∉ S, ∀ j, z j v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun v _ _ => zero_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v hv j => add_mem (ha v hv j) (hb v hv j)
  neg_mem' := fun ha v hv j => neg_mem (ha v hv j)

theorem mem_integralVecOutside {S : Finset (FinitePlace F)} {z : Fin n → FiniteAdeles F} :
    z ∈ integralVecOutside n S ↔ ∀ v ∉ S, ∀ j, z j v ∈ v.adicCompletionIntegers F :=
  Iff.rfl

theorem mem_integralOutside_iff {S : Finset (FinitePlace F)} {x : RowVector F n} :
    x ∈ integralOutside F n S ↔ finiteCoordinates F n x ∈ integralVecOutside n S :=
  Iff.rfl

theorem isOpen_integralVecOutside (S : Finset (FinitePlace F)) :
    IsOpen (integralVecOutside n S : Set (Fin n → FiniteAdeles F)) := by
  have h1 : IsOpen {b : FiniteAdeles F | ∀ v, v ∉ S → b v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
  have h2 : (integralVecOutside n S : Set (Fin n → FiniteAdeles F)) =
      ⋂ j, (fun z : Fin n → FiniteAdeles F => z j) ⁻¹'
        {b : FiniteAdeles F | ∀ v, v ∉ S → b v ∈ v.adicCompletionIntegers F} := by
    ext z
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h j v hv => h v hv j, fun h v hv j => h j v hv⟩
  rw [h2]
  exact isOpen_iInter_of_finite fun j => h1.preimage (continuous_apply j)

theorem isClosed_integralVecOutside (S : Finset (FinitePlace F)) :
    IsClosed (integralVecOutside n S : Set (Fin n → FiniteAdeles F)) :=
  AddSubgroup.isClosed_of_isOpen _ (isOpen_integralVecOutside n S)

/-! ### Coset indicators are restricted pure tensors -/

/-- A finite set of places outside of which `m` vanishes and `a` is integral. -/
theorem exists_finset_adapted (m : FinitePlace F →₀ ℤ) (a : Fin n → FiniteAdeles F) :
    ∃ S : Finset (FinitePlace F), ∀ v ∉ S, m v = 0 ∧ ∀ j, a j v ∈ v.adicCompletionIntegers F := by
  classical
  have hfin : ∀ j, {v : FinitePlace F | a j v ∉ v.adicCompletionIntegers F}.Finite :=
    fun j => Filter.eventually_cofinite.mp (a j).2
  refine ⟨m.support ∪ Finset.univ.biUnion fun j => (hfin j).toFinset,
    fun v hv => ⟨?_, fun j => ?_⟩⟩
  · by_contra h
    exact hv (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
  · by_contra h
    exact hv (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, (hfin j).mem_toFinset.mpr h⟩))

theorem sub_mem_latticeVec_iff {m : FinitePlace F →₀ ℤ} {a : Fin n → FiniteAdeles F}
    {S : Finset (FinitePlace F)}
    (hS : ∀ v ∉ S, m v = 0 ∧ ∀ j, a j v ∈ v.adicCompletionIntegers F)
    {z : Fin n → FiniteAdeles F} (hz : z ∈ integralVecOutside n S) :
    z - a ∈ latticeVec n m ↔
      ∀ v ∈ S, (fun j => z j v) - (fun j => a j v) ∈ localLatticeVec n v (m v) := by
  rw [mem_latticeVec]
  constructor
  · intro h v _
    rw [mem_localLatticeVec]
    intro j
    exact (mem_finiteLattice m _).mp (h j) v
  · intro h j
    rw [mem_finiteLattice]
    intro v
    by_cases hv : v ∈ S
    · exact (mem_localLatticeVec n).mp (h v hv) j
    · obtain ⟨hm, ha⟩ := hS v hv
      rw [hm, Hecke.mem_additiveLattice_zero_iff]
      exact sub_mem (hz v hv j) (ha j)

theorem mem_integralVecOutside_of_sub_mem {m : FinitePlace F →₀ ℤ}
    {a : Fin n → FiniteAdeles F} {S : Finset (FinitePlace F)}
    (hS : ∀ v ∉ S, m v = 0 ∧ ∀ j, a j v ∈ v.adicCompletionIntegers F)
    {z : Fin n → FiniteAdeles F} (h : z - a ∈ latticeVec n m) : z ∈ integralVecOutside n S := by
  intro v hv j
  obtain ⟨hm, ha⟩ := hS v hv
  have h1 := (mem_finiteLattice m _).mp ((mem_latticeVec n).mp h j) v
  rw [hm, Hecke.mem_additiveLattice_zero_iff] at h1
  have h2 := add_mem h1 (ha j)
  have e : (z - a) j v + a j v = z j v := sub_add_cancel (z j v) (a j v)
  rw [e] at h2
  exact h2

open scoped Classical in
/-- `Φ_∞ ⊗ 1_(a + L_m^n)` is a restricted pure tensor. -/
theorem isRestrictedPure_mul_cosetIndicator
    (Φinf : SchwartzMap (Fin n → mixedEmbedding.mixedSpace F) ℂ)
    (m : FinitePlace F →₀ ℤ) (a : Fin n → FiniteAdeles F) :
    IsRestrictedPureSchwartzBruhat F n (fun x => Φinf (archimedeanCoordinates F n x) *
      cosetIndicator (latticeVec n m) a (finiteCoordinates F n x)) := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_adapted n m a
  refine ⟨Φinf, S, fun v => cosetIndicator (localLatticeVec n v (m v)) (fun j => a j v),
    fun v _ => ⟨isLocallyConstant_cosetIndicator _ (isOpen_localLatticeVec n v _) _,
      hasCompactSupport_cosetIndicator _ (isOpen_localLatticeVec n v _)
        (isCompact_localLatticeVec n v _) _⟩, ?_⟩
  funext x
  by_cases hx : x ∈ integralOutside F n S
  · have hx' : finiteCoordinates F n x ∈ integralVecOutside n S := hx
    have hiff := sub_mem_latticeVec_iff n hS hx'
    rw [Set.indicator_of_mem hx]
    simp only [cosetIndicator]
    rw [Finset.prod_boole]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · rfl
  · have h : finiteCoordinates F n x - a ∉ latticeVec n m := fun h =>
      hx (mem_integralVecOutside_of_sub_mem n hS h)
    rw [Set.indicator_of_notMem hx]
    simp [cosetIndicator, h]

theorem schwartzBruhat_le_restricted : schwartzBruhat F n ≤ restrictedSchwartzBruhat F n := by
  refine Submodule.span_le.mpr ?_
  rintro Φ ⟨Φinf, Φfin, hlc, hc, rfl⟩
  obtain ⟨m, s, hs⟩ := exists_eq_sum_latticeVec n hlc hc
  have key : (fun x => Φinf (archimedeanCoordinates F n x) * Φfin (finiteCoordinates F n x)) =
      ∑ a ∈ s, Φfin a • (fun x => Φinf (archimedeanCoordinates F n x) *
        cosetIndicator (latticeVec n m) a (finiteCoordinates F n x)) := by
    funext x
    rw [Finset.sum_apply, congrFun hs (finiteCoordinates F n x), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [SetLike.mem_coe, key]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span (isRestrictedPure_mul_cosetIndicator n Φinf m a))

/-! ### Restricted pure tensors are pure tensors -/

open scoped Classical in
/-- The finite part `⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)` of a restricted pure tensor, as a
function on `𝔸_f^n`. -/
def restrictedFinitePart (S : Finset (FinitePlace F))
    (Φloc : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ)
    (z : Fin n → FiniteAdeles F) : ℂ :=
  if z ∈ integralVecOutside n S then ∏ v ∈ S, Φloc v (fun j => z j v) else 0

theorem isLocallyConstant_restrictedFinitePart (S : Finset (FinitePlace F))
    (Φloc : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ)
    (hloc : ∀ v ∈ S, IsLocallyConstant (Φloc v)) :
    IsLocallyConstant (restrictedFinitePart n S Φloc) := by
  classical
  unfold restrictedFinitePart
  exact isLocallyConstant_ite_of_isClopen (p := fun z => z ∈ integralVecOutside n S)
    (isOpen_integralVecOutside n S) (isClosed_integralVecOutside n S)
    (isLocallyConstant_finset_prod S fun v hv => (hloc v hv).comp_continuous
      (continuous_pi fun j => (RestrictedProduct.continuous_eval v).comp (continuous_apply j)))

theorem hasCompactSupport_restrictedFinitePart (S : Finset (FinitePlace F))
    (Φloc : (v : FinitePlace F) → (Fin n → FiniteCompletion F v) → ℂ)
    (hloc : ∀ v ∈ S, HasCompactSupport (Φloc v)) :
    HasCompactSupport (restrictedFinitePart n S Φloc) := by
  classical
  have hk : ∀ v, ∃ k : ℤ, v ∈ S → ∀ z ∈ tsupport (Φloc v), ∀ j,
      z j ∈ (topologicalData v).additiveLattice k := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨k, hk⟩ := exists_additiveLattice_pi_of_isCompact n v (hloc v hv).isCompact
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose k hk using hk
  let m : FinitePlace F →₀ ℤ := Finsupp.onFinset S
    (fun v => if v ∈ S then max (k v) 0 else 0) (by
      intro v hv
      by_contra h
      exact hv (by simp [h]))
  refine HasCompactSupport.intro' (isCompact_latticeVec n m) (isClosed_latticeVec n m)
    fun z hz => ?_
  by_contra hne
  apply hz
  rw [SetLike.mem_coe, mem_latticeVec]
  intro j
  rw [mem_finiteLattice]
  intro v
  unfold restrictedFinitePart at hne
  by_cases hzO : z ∈ integralVecOutside n S
  · simp only [hzO, ↓reduceIte] at hne
    by_cases hv : v ∈ S
    · have h1 := Finset.prod_ne_zero_iff.mp hne v hv
      have h2 := hk v hv (fun j => z j v) (subset_tsupport _ h1) j
      refine (topologicalData v).additiveLattice_mono ?_ h2
      simp only [m, Finsupp.onFinset_apply, hv, ↓reduceIte]
      exact le_max_left _ _
    · have hm : m v = 0 := by simp [m, hv]
      rw [hm, Hecke.mem_additiveLattice_zero_iff]
      exact hzO v hv j
  · simp [hzO] at hne

theorem restricted_le_schwartzBruhat : restrictedSchwartzBruhat F n ≤ schwartzBruhat F n := by
  refine Submodule.span_le.mpr ?_
  rintro Φ ⟨Φinf, S, Φloc, hloc, rfl⟩
  refine Submodule.subset_span ⟨Φinf, restrictedFinitePart n S Φloc,
    isLocallyConstant_restrictedFinitePart n S Φloc fun v hv => (hloc v hv).1,
    hasCompactSupport_restrictedFinitePart n S Φloc fun v hv => (hloc v hv).2, ?_⟩
  funext x
  by_cases hx : x ∈ integralOutside F n S
  · have hx' : finiteCoordinates F n x ∈ integralVecOutside n S := hx
    rw [Set.indicator_of_mem hx]
    simp only [restrictedFinitePart, hx', ↓reduceIte]
    rfl
  · have hx' : finiteCoordinates F n x ∉ integralVecOutside n S := hx
    rw [Set.indicator_of_notMem hx]
    simp [restrictedFinitePart, hx']

/-- **Part A.** `S(𝔸^n)` equals the restricted tensor product. -/
theorem schwartzBruhat_eq_restricted :
    schwartzBruhat F n = restrictedSchwartzBruhat F n :=
  le_antisymm (schwartzBruhat_le_restricted n) (restricted_le_schwartzBruhat n)

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof
