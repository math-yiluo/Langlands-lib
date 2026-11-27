import Langlands.BushnellKutzko.SimpleCharacterCommutatorAlgebra
import Langlands.BushnellKutzko.TerminalSimpleCharacter
import Langlands.BushnellKutzko.LatticeCharacterIntertwining

/-! # Centralizer intertwining below the cutoff -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

local notation "O" => 𝒪[F]
local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "P" => LatticeChain.endFiltration
local notation "Q" => centralizerLattice

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem adjointKernel_conj_iff {b : A} {g : G} (hg : g ∈ centralizerUnitGroup b) (x : A) :
    endUnitConjugation g x ∈ (adjointMap O b).ker ↔ x ∈ (adjointMap O b).ker := by
  have hc : Commute b (g : A) := hg
  have hci := Commute.units_inv_right hc
  have he : adjointMap O b (endUnitConjugation g x) = endUnitConjugation g (adjointMap O b x) := by
    change b * ((g : A) * x * (↑g⁻¹ : A)) - ((g : A) * x * (↑g⁻¹ : A)) * b =
      (g : A) * (b * x - x * b) * (↑g⁻¹ : A)
    rw [mul_sub, sub_mul]
    rw [← mul_assoc b ((g : A) * x), ← mul_assoc b (g : A) x, hc.eq]
    rw [mul_assoc ((g : A) * x) _ b, ← hci.eq]
    simp only [mul_assoc]
  change adjointMap O b (endUnitConjugation g x) = 0 ↔ adjointMap O b x = 0
  rw [he]
  exact ⟨fun h => (endUnitConjugation g).injective (h.trans (map_zero _).symm),
    fun h => h ▸ (endUnitConjugation g).map_zero⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem centralizerLattice_map_conj (L : LatticeChain O F V) {b : A} {g : G}
    (hg : g ∈ centralizerUnitGroup b) (i : ℤ) :
    (Q L b i).map (endUnitConjugation g).toLinearMap =
      (P L i).map (endUnitConjugation g).toLinearMap ⊓ (adjointMap O b).ker := by
  ext x
  rw [Submodule.mem_inf, Submodule.mem_map_equiv, Submodule.mem_map_equiv, endUnitConjugation_symm]
  change (_ ∧ endUnitConjugation g⁻¹ x ∈ (adjointMap O b).ker) ↔ _
  rw [adjointKernel_conj_iff ((centralizerUnitGroup b).inv_mem hg)]
  rfl

private theorem endFiltration_sum_for_centralizer (S : Stratum O F V) (hS : S.IsPure)
    {g : G} (hg : g ∈ centralizerUnitGroup S.b) (i j : ℤ) :
    (P S.chain i ⊔ (P S.chain j).map (endUnitConjugation g).toLinearMap) ⊓ (adjointMap O S.b).ker =
      Q S.chain S.b i ⊔ (Q S.chain S.b j).map (endUnitConjugation g).toLinearMap := by
  obtain ⟨hE, hunits⟩ := hS.1
  let E := elementAlgebra S.b
  let : Field E := hE.toField
  let b₀ : E := ⟨S.b, Algebra.self_mem_adjoin_singleton F S.b⟩
  have hb₀ : Algebra.adjoin F ({b₀} : Set E) = ⊤ := by
    apply Subalgebra.map_injective (f := E.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
    rfl
  let y := (relativeEndUnitEquiv S.b hE).symm ⟨g, hg⟩
  have hy : relativeEndUnits E y = g := congrArg (fun z : centralizerUnitGroup S.b => (z : G))
    ((relativeEndUnitEquiv S.b hE).apply_symm_apply ⟨g, hg⟩)
  have h := endFiltration_sup_conj_inf_centralizer S.chain hunits b₀ hb₀ y i j
  change (P S.chain i ⊔ (P S.chain j).map (endUnitConjugation (relativeEndUnits E y)).toLinearMap) ⊓
      (adjointMap O S.b).ker = Q S.chain S.b i ⊔
      (Q S.chain S.b j).map (endUnitConjugation (relativeEndUnits E y)).toLinearMap at h
  rwa [hy] at h

/-- At low depth, the domain overlap is the product of the relative overlap
and the overlap of the deeper domains. Determinant invariance and
intertwining on the deeper domain give intertwining on the full domain. -/
theorem centralizer_intertwines_of_deep_intertwining (S : Stratum O F V) (hS : S.IsPure)
    {k d : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (D : Submodule O A) (H H' : Subgroup G)
    (hD : D ≤ P S.chain d) (hQD : Q S.chain S.b d ≤ D)
    (hmul : Q S.chain S.b 0 * D ≤ D)
    (hH : ∀ u : G, u ∈ H ↔ (u : A) - 1 ∈ Q S.chain S.b k ⊔ D)
    (hH' : ∀ u : G, u ∈ H' ↔ (u : A) - 1 ∈ D)
    (hinc : H' ≤ H) (θ : H →* ℂˣ) (hdet : factorsThroughCentralizerDet S.b θ)
    {g : G} (hg : g ∈ centralizerUnitGroup S.b)
    (hg' : g ∈ characterSelfIntertwining (θ.comp (Subgroup.inclusion hinc))) :
    g ∈ characterSelfIntertwining θ := by
  let L := S.chain
  let b := S.b
  let e := endUnitConjugation g⁻¹
  let K := (adjointMap O b).ker
  let U := Q L b k ⊓ (Q L b k).map e.toLinearMap
  let W := D ⊓ D.map e.toLinearMap
  let R := relativeUnitFiltration L b k
  have hgi := (centralizerUnitGroup b).inv_mem hg
  have hQ (i : ℤ) : (Q L b i).map e.toLinearMap = (P L i).map e.toLinearMap ⊓ K :=
    centralizerLattice_map_conj L hgi i
  have hdeep : (D ⊔ D.map e.toLinearMap) ⊓ K = (D ⊓ K) ⊔ (D.map e.toLinearMap ⊓ K) := by
    refine le_antisymm ?_ (sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl))
    have hf := endFiltration_sum_for_centralizer S hS hgi (d : ℤ) (d : ℤ)
    change (P L d ⊔ (P L d).map e.toLinearMap) ⊓ K = Q L b d ⊔ (Q L b d).map e.toLinearMap at hf
    refine (inf_le_inf (sup_le_sup hD (Submodule.map_mono hD)) le_rfl).trans ?_
    rw [hf]
    refine sup_le (le_inf hQD inf_le_right |>.trans le_sup_left) ?_
    exact (le_inf (Submodule.map_mono hQD) (by rw [hQ]; exact inf_le_right)).trans le_sup_right
  have hinter : (Q L b k ⊔ D) ⊓ (Q L b k ⊔ D).map e.toLinearMap = U ⊔ W := by
    simp only [Submodule.map_sup, U, W, hQ]
    have hle : D ≤ P L k := hD.trans (L.endFiltration_antitone (by omega))
    exact inf_sup_eq_of_deep_kernel_split hle (Submodule.map_mono hle) hdeep
  have hpos : U ≤ P L 1 := fun _ hx => L.endFiltration_antitone (by exact_mod_cast hk) hx.1.1
  have hmul' : U * W ≤ W := by
    apply Submodule.mul_le.mpr
    intro u hu w hw
    have hmul₀ {u w : A} (hu : u ∈ Q L b k) (hw : w ∈ D) : u * w ∈ D :=
      hmul (Submodule.mul_mem_mul ⟨L.endFiltration_antitone (Int.natCast_nonneg k) hu.1, hu.2⟩ hw)
    refine ⟨hmul₀ hu.1 hw.1, ?_⟩
    obtain ⟨u', hu', hval⟩ := Submodule.mem_map.mp hu.2
    obtain ⟨w', hw', hval'⟩ := Submodule.mem_map.mp hw.2
    refine ⟨u' * w', hmul₀ hu' hw', ?_⟩
    change e (u' * w') = u * w
    rw [← hval, ← hval']
    exact ((LinearMap.GeneralLinearGroup.toLinearEquiv g⁻¹).conjAlgEquiv F).map_mul u' w'
  have hR (u : G) : u ∈ R ↔ (u : A) - 1 ∈ Q L b k :=
    mem_relativeUnitFiltration_iff_of_pos L b hk u
  have hU (u : G) : (u ∈ R ∧ g * u * g⁻¹ ∈ R) ↔ (u : A) - 1 ∈ U :=
    mem_congruence_overlap_iff _ hR g u
  have hW (u : G) : (u ∈ H' ∧ g * u * g⁻¹ ∈ H') ↔ (u : A) - 1 ∈ W :=
    mem_congruence_overlap_iff _ hH' g u
  have hinv (u : G) (hu : (u : A) - 1 ∈ U) : (↑u⁻¹ : A) - 1 ∈ U := by
    obtain ⟨hu, hv⟩ := (hU u).mpr hu
    refine (hU u⁻¹).mp ⟨R.inv_mem hu, ?_⟩
    have he : (g * u * g⁻¹)⁻¹ = g * u⁻¹ * g⁻¹ := by group
    exact he ▸ R.inv_mem hv
  intro x hx
  have hx' := (mem_congruence_overlap_iff _ hH g x).mp ⟨x.property, hx⟩
  rw [hinter] at hx'
  obtain ⟨u, hu, w, hw, huw⟩ := exists_mul_of_sub_one_mem_sup L hpos hmul' hinv hx'
  obtain ⟨huR, hguR⟩ := (hU u).mpr hu
  have huH : u ∈ H := (hH _).mpr (Submodule.mem_sup_left ((hR _).mp huR))
  have hguH : g * u * g⁻¹ ∈ H := (hH _).mpr (Submodule.mem_sup_left ((hR _).mp hguR))
  have hw' := (hW w).mpr hw
  have he₁ := hdet.conj_eq hg ⟨u, huH⟩ huR.1 hguH
  have he₂ := hg' ⟨w, hw'.1⟩ hw'.2
  change θ ⟨g * w * g⁻¹, hinc hw'.2⟩ = θ ⟨w, hinc hw'.1⟩ at he₂
  have hleft : (⟨g * (x : G) * g⁻¹, hx⟩ : H) = ⟨g * u * g⁻¹, hguH⟩ *
      ⟨g * w * g⁻¹, hinc hw'.2⟩ := by
    apply Subtype.ext
    change g * (x : G) * g⁻¹ = (g * u * g⁻¹) * (g * w * g⁻¹)
    rw [← huw]
    group
  have hright : x = ⟨u, huH⟩ * ⟨w, hinc hw'.1⟩ := Subtype.ext huw.symm
  rw [hleft, map_mul, he₁, he₂, hright, map_mul]

end Langlands.BushnellKutzko
