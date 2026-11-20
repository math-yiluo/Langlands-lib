import Langlands.Global.FiniteAdelicGL.CompactProduct
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Group.GL.CompactOpen

/-!
# Product levels in the finite adelic compact group

Every open finite adelic stabilizer contains a level specified by finitely many
local open subgroups and by the full local integral group elsewhere.
-/

noncomputable section

open scoped Topology

set_option autoImplicit false

universe u

namespace Langlands.Global.FiniteAdelicGL

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

private theorem localIntegral_openSubgroup_basis (v : FinitePlace F)
    {V : Set (localIntegral F n v)} (hV : V ∈ 𝓝 (1 : localIntegral F n v)) :
    ∃ L : OpenSubgroup (localIntegral F n v), (L : Set (localIntegral F n v)) ⊆ V := by
  let : NonarchimedeanGroup (FiniteLocalGL F n v) := by
    have h := (CompletionPadic.padicField v).canonicalTopologicalData.generalLinearNonarchimedean n
    change @NonarchimedeanGroup (FiniteLocalGL F n v) _
      ((CompletionPadic.padicField v).canonicalGeneralLinearTopology n) at h
    rw [← localGL_topology_eq F v n] at h
    exact h
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨V', hV', hVV⟩ := hV
  have hV' : V' ∈ 𝓝 (1 : FiniteLocalGL F n v) := hV'
  obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V' hV'
  exact ⟨L.comap (localIntegral F n v).toSubgroup.subtype continuous_subtype_val,
    fun _ hx => hVV (hL hx)⟩

/-- An actual finite adelic open subgroup contains a product level in the
standard integral subgroup. -/
theorem exists_productLevel_le (U : OpenSubgroup (FiniteAdelicGL F n)) :
    ∃ (S : Finset (FinitePlace F))
      (L : ∀ v : FinitePlace F, OpenSubgroup (localIntegral F n v)),
      (∀ v ∉ S, L v = ⊤) ∧
      ∀ x : ∀ v : FinitePlace F, localIntegral F n v, (∀ v, x v ∈ L v) →
        ((standardIntegralProductEquiv F n).symm x).val ∈ U := by
  classical
  let e := standardIntegralProductEquiv F n
  let q : (∀ v : FinitePlace F, localIntegral F n v) → FiniteAdelicGL F n :=
    fun x => (e.symm x).val
  have hq : Continuous q := continuous_subtype_val.comp e.symm.continuous
  have hU : q ⁻¹' (U : Set (FiniteAdelicGL F n)) ∈
      𝓝 (1 : ∀ v : FinitePlace F, localIntegral F n v) := by
    apply (U.isOpen.preimage hq).mem_nhds
    change (e.symm 1).val ∈ U
    rw [map_one]
    exact U.one_mem
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨S, V, hV, hVU⟩ := hU
  choose L hL using fun v => localIntegral_openSubgroup_basis F n v (hV v)
  refine ⟨S, fun v => if v ∈ S then L v else ⊤, ?_, ?_⟩
  · intro v hv
    simp [hv]
  · intro x hx
    refine hVU fun v hv => hL v ?_
    change v ∈ S at hv
    simpa [hv] using hx v

/-- The product of a family of local levels that is full outside a finite set,
assembled as an open subgroup of the actual finite adelic matrix group. -/
def productLevel (S : Finset (FinitePlace F))
    (L : ∀ v : FinitePlace F, OpenSubgroup (localIntegral F n v))
    (hL : ∀ v ∉ S, L v = ⊤) : OpenSubgroup (FiniteAdelicGL F n) := by
  let e := standardIntegralProductEquiv F n
  let J := Subgroup.pi Set.univ (fun v => (L v).toSubgroup)
  let H := J.comap e.toMonoidHom
  have hJ : (J : Set (∀ v : FinitePlace F, localIntegral F n v)) =
      Set.pi (S : Set (FinitePlace F)) (fun v => (L v : Set (localIntegral F n v))) := by
    ext x
    simp only [J, Subgroup.coe_pi, Set.mem_pi, Set.mem_univ, forall_const, Finset.mem_coe]
    refine ⟨fun hx v _ => hx v, fun hx v => ?_⟩
    by_cases hv : v ∈ S
    · exact hx v hv
    · simp [hL v hv]
  have hO : IsOpen (J : Set (∀ v : FinitePlace F, localIntegral F n v)) := by
    rw [hJ]
    exact isOpen_set_pi S.finite_toSet fun v _ => (L v).isOpen
  exact { toSubgroup := H.map (standardIntegral F n).toSubgroup.subtype
          isOpen' := (standardIntegral F n).isOpen.isOpenMap_subtype_val _
            (hO.preimage e.continuous) }

/-- A product level is obtained by assembling precisely the allowed local matrices. -/
theorem mem_productLevel_iff {S : Finset (FinitePlace F)}
    {L : ∀ v : FinitePlace F, OpenSubgroup (localIntegral F n v)}
    (hL : ∀ v ∉ S, L v = ⊤) (g : FiniteAdelicGL F n) :
    g ∈ productLevel F n S L hL ↔
      ∃ x : ∀ v : FinitePlace F, localIntegral F n v,
        (∀ v, x v ∈ L v) ∧ ((standardIntegralProductEquiv F n).symm x).val = g := by
  let e := standardIntegralProductEquiv F n
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨e k, fun v => hk v (Set.mem_univ _), congrArg Subtype.val (e.symm_apply_apply k)⟩
  · rintro ⟨x, hx, hg⟩
    refine ⟨e.symm x, ?_, hg⟩
    change ∀ v ∈ Set.univ, e (e.symm x) v ∈ L v
    rw [e.apply_symm_apply]
    exact fun v _ => hx v

theorem productLevel_le_standardIntegral {S : Finset (FinitePlace F)}
    {L : ∀ v : FinitePlace F, OpenSubgroup (localIntegral F n v)}
    (hL : ∀ v ∉ S, L v = ⊤) :
    productLevel F n S L hL ≤ standardIntegral F n := by
  intro g hg
  obtain ⟨x, _, rfl⟩ := (mem_productLevel_iff F n hL g).mp hg
  exact ((standardIntegralProductEquiv F n).symm x).property

theorem isCompact_productLevel {S : Finset (FinitePlace F)}
    {L : ∀ v : FinitePlace F, OpenSubgroup (localIntegral F n v)}
    (hL : ∀ v ∉ S, L v = ⊤) :
    IsCompact (productLevel F n S L hL : Set (FiniteAdelicGL F n)) :=
  (isCompact_standardIntegral F n).of_isClosed_subset
    (productLevel F n S L hL).isClosed (productLevel_le_standardIntegral F n hL)

/-- The actual compact product levels are cofinal among open finite adelic subgroups. -/
theorem exists_productLevelSubgroup_le (U : OpenSubgroup (FiniteAdelicGL F n)) :
    ∃ (S : Finset (FinitePlace F))
      (L : ∀ v : FinitePlace F, OpenSubgroup (localIntegral F n v))
      (hL : ∀ v ∉ S, L v = ⊤), productLevel F n S L hL ≤ U := by
  obtain ⟨S, L, hL, hU⟩ := exists_productLevel_le F n U
  refine ⟨S, L, hL, fun g hg => ?_⟩
  obtain ⟨x, hx, rfl⟩ := (mem_productLevel_iff F n hL _).mp hg
  exact hU x hx

end Langlands.Global.FiniteAdelicGL
