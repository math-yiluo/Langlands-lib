import Langlands.LocalFactor.Ramification.Herbrand.RelativeIndex
import Langlands.LocalFactor.Ramification.Herbrand.TameSubextension
import Langlands.Correspondence.HenniartTameFieldCount

/-!
# Herbrand rescaling across a tame totally ramified subextension: proof
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open LocalClassField Weil.Local Henniart Henniart.WildInertia Henniart.TameOrbit
open Henniart.TameField

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier

/-- An open subgroup of inertia of index prime to `p` contains wild inertia. -/
theorem wildIn_le_of_isOpen_coprime (U : Subgroup (localInertia K))
    (hU : IsOpen (U : Set (localInertia K))) (hcop : Nat.Coprime U.index p) : wildIn K ≤ U := by
  obtain ⟨L, hL⟩ := ker_res_le K hU
  have hsurj : Function.Surjective (res K L).toMonoidHom := res_surjective K L
  let G₁ := Ramification.Padic.inertiaLowerGroup (finT K L) K.Carrier 1
  have : G₁.Normal := inertiaLowerGroup_isNormal (finT K L) K.Carrier 1
  obtain ⟨b, hb⟩ := exists_card_inertiaLowerGroup K L
  have hP : IsPGroup p G₁ := IsPGroup.of_card hb
  let V := U.map (res K L).toMonoidHom
  have hidx : V.index = U.index := Subgroup.index_map_eq U hsurj hL
  have hrel : V.relIndex G₁ ∣ U.index := by
    rw [← hidx, ← relIndex_normal_sup V G₁]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_right
  have : Finite G₁ := inferInstance
  obtain ⟨n, hn⟩ := hP.index (V.subgroupOf G₁)
  have hn' : V.relIndex G₁ = p ^ n := hn
  have h1 : p ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hcop.symm)
    (hn' ▸ hrel)
  have hle : G₁ ≤ V := Subgroup.relIndex_eq_one.mp (hn'.trans h1)
  intro x hx
  have hx1 : (res K L).toMonoidHom x ∈ G₁ := by
    have hG : G₁ = (wildIn K).map (res K L).toMonoidHom := inertiaLowerGroup_eq_map K L
    rw [hG]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx1
  have hker : y⁻¹ * x ∈ U := by
    apply hL
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have := U.mul_mem hy hker
  rwa [mul_inv_cancel_left] at this

/-- Wild inertia lies in the Weil group of a finite subextension of degree prime to `p`. -/
theorem weilWildInertia_le_range (E : FiniteIntermediateExtension K.Carrier)
    (hm : ¬ p ∣ extensionDegree K (E.asPadicField (p := p)) (intermediateEmbedding K E)) :
    ∀ x : localWeilGroup K, x ∈ weilWildInertia K →
      x ∈ (intermediateWeilMap K E).toMonoidHom.range := by
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  let GE := E.field.fixingSubgroup
  let Ia := K.absoluteInertia K.canonicalTopologicalData
  have hIa : Ia.Normal := inferInstanceAs (K.absoluteInertia K.canonicalTopologicalData).Normal
  let e := localInertiaEquiv K
  let U : Subgroup (localInertia K) := (GE.subgroupOf Ia).comap e.toMulEquiv.toMonoidHom
  have hU : IsOpen (U : Set (localInertia K)) :=
    ((E.field.fixingSubgroup_isOpen.preimage continuous_subtype_val).preimage e.continuous)
  have hidx : U.index = GE.relIndex Ia :=
    Subgroup.index_comap_of_surjective _ e.surjective
  have hdvd : GE.relIndex Ia ∣ Module.finrank K.Carrier E.field := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← @relIndex_normal_sup _ _ GE Ia hIa]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_right
  have hcop : Nat.Coprime U.index p := by
    rw [hidx]
    apply Nat.Coprime.coprime_dvd_left hdvd
    rw [← PadicField.extensionDegree_intermediateEmbedding K E]
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  intro x hx
  have hmem := wildIn_le_of_isOpen_coprime K U hU hcop
    (Subgroup.mem_subgroupOf.mpr hx :
      (⟨x, weilWildInertia_le_localInertia K hx⟩ : localInertia K) ∈ wildIn K)
  have hproj : localProjection K x ∈ GE := hmem
  rw [intermediateWeilMap_range]
  exact hproj

/-- **Herbrand rescaling across a tame totally ramified subextension.** -/
theorem tameSubextensionHerbrand : TameSubextensionHerbrandStatement.{u} := by
  intro p _ K E L ι m hres hm
  have hker := weilWildInertia_le_range K E hm
  have hdeg : extensionDegree K L ι = m := rfl
  refine ⟨fun v hv => relativeHerbrandPsi_eq K E hdeg hres hker hv, fun v hv => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast degree_pos K E hdeg
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (map_mem_upperGroup_iff K E hdeg hres hker hv w).mpr hw
  · intro hx
    obtain ⟨w, hw⟩ := hker x (upperGroup_le_weilWildInertia K hv hx)
    refine ⟨w, ?_, hw⟩
    change w ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup (E.asPadicField (p := p))
      ((m : ℝ) * v)
    rw [← map_mem_upperGroup_iff K E hdeg hres hker hv]
    change (intermediateWeilMap K E).toMonoidHom w ∈ _
    rw [hw]
    exact hx

end Langlands.Ramification.HerbrandBridge
