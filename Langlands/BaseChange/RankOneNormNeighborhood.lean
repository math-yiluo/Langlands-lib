import Langlands.BaseChange.RankOneSigmaLiftNorm
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.ClassFieldTheory.Local.NormUnitImageIndexSupport
import Langlands.ClassFieldTheory.Local.OpenFiniteIndexSeparationProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationConductor
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # Compact open rank-one norm neighborhoods -/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Langlands.BaseChange

universe u v

section Hilbert90

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- Hilbert 90 for independently sized carriers, using the norm of the
actual extension. The cyclic sum uses linear independence of field maps. -/
theorem IsCyclicAlgebra.exists_unit_div_sigma_eq_of_norm_eq_one
    (hcyc : IsCyclicAlgebra σ l) (x : Eˣ) (hx : Units.map (Algebra.norm F) x = 1) :
    ∃ y : Eˣ, y / Units.map σ.toMonoidHom y = x := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hcyc.pos.ne'
  let partialNorm (n : ℕ) : E := ∏ i ∈ Finset.range n, (σ ^ i) (x : E)
  have hrec (n : ℕ) : (x : E) * σ (partialNorm n) = partialNorm (n + 1) := by
    rw [show partialNorm (n + 1) = _ from Finset.prod_range_succ' _ n]
    change (x : E) * σ (∏ i ∈ Finset.range n, (σ ^ i) (x : E)) = _
    rw [map_prod, pow_zero, AlgEquiv.one_apply, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [pow_succ', AlgEquiv.mul_apply]
  have hend : partialNorm (m + 1) = 1 := by
    change (∏ i ∈ Finset.range (m + 1), (σ ^ i) (x : E)) = 1
    rw [← hcyc.norm_eq_prod_powers x]
    change algebraMap F E (↑(Units.map (Algebra.norm F) x) : F) = 1
    rw [hx, Units.val_one, map_one]
  let φ (i : Fin (m + 1)) := (σ ^ (i : ℕ)).toMonoidHom
  have hinj : Function.Injective φ := by
    intro i j h
    have he : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
      ext z
      exact DFunLike.congr_fun h z
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (hcyc.2.2.2.1.symm ▸ i.isLt)
      (hcyc.2.2.2.1.symm ▸ j.isLt) he
  have hind : LinearIndependent E (fun i : Fin (m + 1) => (φ i : E → E)) :=
    (linearIndependent_monoidHom E E).comp φ hinj
  have hnz : ∃ z : E, (∑ i : Fin (m + 1), partialNorm i * φ i z) ≠ 0 := by
    by_contra! h
    have hsum : (∑ i : Fin (m + 1), partialNorm i • (φ i : E → E)) = 0 := by
      ext z
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using h z
    have hzero := (Fintype.linearIndependent_iff.mp hind _ hsum) (0 : Fin (m + 1))
    simp [partialNorm] at hzero
  obtain ⟨z, hz⟩ := hnz
  let terms (i : ℕ) : E := partialNorm i * (σ ^ i) z
  let b : E := ∑ i ∈ Finset.range (m + 1), terms i
  have hb : b ≠ 0 := by
    rw [show b = _ from Finset.sum_range _]
    exact hz
  have ht (i : ℕ) : (x : E) * σ (terms i) = terms (i + 1) := by
    change (x : E) * σ (partialNorm i * (σ ^ i) z) = _
    rw [map_mul, ← mul_assoc, hrec]
    change partialNorm (i + 1) * σ ((σ ^ i) z) = partialNorm (i + 1) * (σ ^ (i + 1)) z
    rw [pow_succ', AlgEquiv.mul_apply]
  have hshift : (∑ i ∈ Finset.range (m + 1), terms (i + 1)) = b := by
    have hterm : terms (m + 1) = terms 0 := by
      simp only [terms, hend, hcyc.pow_eq_one, pow_zero, AlgEquiv.one_apply, partialNorm,
        Finset.range_zero, Finset.prod_empty, one_mul]
    have h := (Finset.sum_range_succ' terms (m + 1)).symm.trans
      (Finset.sum_range_succ terms (m + 1))
    rw [hterm] at h
    exact add_right_cancel h
  have he : (x : E) * σ b = b := by
    change (x : E) * σ (∑ i ∈ Finset.range (m + 1), terms i) = _
    rw [map_sum, Finset.mul_sum]
    exact (Finset.sum_congr rfl (fun i _ => ht i)).trans hshift
  refine ⟨Units.mk0 b hb, Units.ext ?_⟩
  rw [Units.val_div_eq_div_val]
  change b / σ b = (x : E)
  exact (div_eq_iff (map_ne_zero σ |>.mpr hb)).mpr he.symm

/-- A character invariant under the cyclic generator is trivial on the kernel
of the actual determinant norm on units. -/
theorem IsCyclicAlgebra.character_eq_one_of_norm_eq_one
    (hcyc : IsCyclicAlgebra σ l) (η : Eˣ →* ℂˣ)
    (hσ : ∀ x : Eˣ, η (Units.map σ.toMonoidHom x) = η x) (x : Eˣ)
    (hx : Units.map (Algebra.norm F) x = 1) : η x = 1 := by
  obtain ⟨y, rfl⟩ := hcyc.exists_unit_div_sigma_eq_of_norm_eq_one x hx
  rw [map_div, hσ, div_self']

end Hilbert90

section Topology

open LocalClassField ClassFieldTheory.Local
open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] [IsAbelianGalois F.Carrier E.Carrier]
  (T : F.TopologicalData) (S : E.TopologicalData)

include S in
/-- A cyclic norm range is an open subgroup of the base multiplicative group. -/
theorem isOpen_normSubgroup_of_isAbelianGalois :
    letI := T.topology
    IsOpen (normSubgroup F.Carrier E.Carrier : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : (normSubgroup F.Carrier E.Carrier).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by
      rw [NormUnitImage.normSubgroup_index_eq_finrank F E]
      exact Module.finrank_pos.ne')
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_normSubgroup F E T S)

/-- Choose a compact open base neighborhood of one contained in the norm
range whose full norm preimage is compact open and lies in a prescribed open
neighborhood of the norm kernel. Both spaces use their supplied topologies. -/
theorem exists_compactOpen_normPreimage :
    letI := T.topology
    letI := S.topology
    ∀ (U : Set F.Carrierˣ) (V : Set E.Carrierˣ), IsOpen U → 1 ∈ U → IsOpen V →
      (localNorm T S) ⁻¹' {1} ⊆ V →
      ∃ D : Set F.Carrierˣ, IsOpen D ∧ IsCompact D ∧ 1 ∈ D ∧ D ⊆ U ∧
        D ⊆ Set.range (localNorm T S) ∧ IsOpen ((localNorm T S) ⁻¹' D) ∧
        IsCompact ((localNorm T S) ⁻¹' D) ∧ (localNorm T S) ⁻¹' D ⊆ V := by
  let := T.topology
  let := S.topology
  let := T.localField
  let := S.localField
  let := T.valuativeRel
  let := S.valuativeRel
  let := T.fieldT2
  let := S.fieldT2
  intro U V hU hU₁ hV hker
  let N := localNorm T S
  let bad := N '' ((S.unitSubgroup : Set E.Carrierˣ) \ V)
  have hS : IsCompact (S.unitSubgroup : Set E.Carrierˣ) := by
    rw [← S.unitFiltration_zero]
    exact S.isCompact_unitFiltration 0
  have hbad : IsClosed bad := ((hS.diff hV).image N.continuous).isClosed
  have hone : (1 : F.Carrierˣ) ∉ bad := by
    rintro ⟨a, ha, hn⟩
    exact ha.2 (hker hn)
  let W := (U ∩ (normSubgroup F.Carrier E.Carrier : Set F.Carrierˣ) ∩
    (T.unitSubgroup : Set F.Carrierˣ)) \ bad
  have hW : IsOpen W :=
    ((hU.inter (isOpen_normSubgroup_of_isAbelianGalois T S)).inter
      (isOpen_unitSubgroup F T)).inter hbad.isOpen_compl
  have hW₁ : (1 : F.Carrierˣ) ∈ W := ⟨⟨⟨hU₁, (normSubgroup F.Carrier E.Carrier).one_mem⟩,
    T.unitSubgroup.one_mem⟩, hone⟩
  obtain ⟨n, hn⟩ := T.exists_principalUnits_subset (hW.mem_nhds hW₁)
  let D := (T.unitFiltration n : Set F.Carrierˣ)
  have hD : D ⊆ W := by simpa only [D, T.unitFiltration_eq_principalUnits] using hn
  have hDc : IsCompact D := T.isCompact_unitFiltration n
  have hDo : IsOpen D := T.isOpen_unitFiltration n
  have hpre : N ⁻¹' D ⊆ (S.unitSubgroup : Set E.Carrierˣ) := by
    intro a ha
    exact (mem_unitSubgroup_iff_ord_eq_zero E S a).mpr
      ((ord_relative_norm_units_eq_zero_iff F E T S a).mp
        ((mem_unitSubgroup_iff_ord_eq_zero F T (N a)).mp (hD ha).1.2))
  refine ⟨D, hDo, hDc, (T.unitFiltration n).one_mem, fun a ha => (hD ha).1.1.1,
    fun a ha => (hD ha).1.1.2, hDo.preimage N.continuous,
    hS.of_isClosed_subset (hDc.isClosed.preimage N.continuous) hpre, ?_⟩
  intro a ha
  by_contra hVa
  exact (hD ha).2 ⟨a, ⟨hpre ha, hVa⟩, rfl⟩

end Topology

end Langlands.BaseChange
