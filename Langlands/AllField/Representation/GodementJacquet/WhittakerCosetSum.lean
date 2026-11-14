import Langlands.Representation.GodementJacquet.WhittakerCosetSum
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-!
# Finite coset sums over a compact subgroup

A compact subgroup `K` of a topological group is a finite disjoint union of left
cosets of an open subgroup `K₀ ≤ K`. Hence the Haar integral over `K` of a
function that is invariant under right translation by `K₀` is a finite sum of
values times the mass of `K₀`. For `GL_(n+1)` of a `p`-adic field, every
full-matrix test function is invariant under right translation by some open
subgroup. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.CosetSum
open Langlands.GodementJacquet.CosetSum
open Langlands.AllField.GodementJacquet.CosetSum
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis
open scoped ENNReal Pointwise

universe uF uG

section Generic



end Generic

namespace Padic
open Langlands.GodementJacquet.CosetSum.Padic hiding cosetSumLocalField cosetSumTopology cosetSumValuativeRel exists_nhds_matrixTest_rightInvariant exists_openSubgroup_rightInvariant isCompact_integralSubgroup isOpen_integralSubgroup
open Langlands.AllField.GodementJacquet.CosetSum.Padic
open Langlands.GodementJacquet.CosetSum
open Langlands.AllField.GodementJacquet.CosetSum
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {n : ℕ}

/-- A full-matrix test function is invariant under right multiplication by every
element of some neighborhood of the identity. -/
theorem exists_nhds_matrixTest_rightInvariant (Φ : MatrixTestFunction n F) :
    ∃ U ∈ 𝓝 (1 : Langlands.GeneralLinear (n + 1) F),
      ∀ g ∈ U, ∀ M, Φ (M * g.val) = Φ M := by
  let G := Langlands.GeneralLinear (n + 1) F
  let X := Matrix (Fin (n + 1)) (Fin (n + 1)) F
  have hcont : Continuous fun z : G × X => z.2 * z.1.val :=
    continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst)
  have hlc : IsLocallyConstant fun z : G × X => Φ (z.2 * z.1.val) - Φ z.2 :=
    IsLocallyConstant.comp₂ ((SchwartzBruhat.locallyConstant Φ).comp_continuous hcont)
      ((SchwartzBruhat.locallyConstant Φ).comp_continuous continuous_snd) (· - ·)
  have hsub : ({1} : Set G) ×ˢ tsupport (Φ : X → ℂ) ⊆
      {z : G × X | Φ (z.2 * z.1.val) - Φ z.2 = 0} := by
    rintro ⟨g, M⟩ ⟨hg, -⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show Φ (M * (1 : G).val) - Φ M = 0
    rw [Units.val_one, Matrix.mul_one, sub_self]
  obtain ⟨u, v, hu, -, h1u, hSv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (SchwartzBruhat.hasCompactSupport Φ).isCompact (hlc.isOpen_fiber 0) hsub
  have hun : u ∈ 𝓝 (1 : G) := hu.mem_nhds (h1u rfl)
  have key : ∀ h ∈ u, ∀ N ∈ tsupport (Φ : X → ℂ), Φ (N * h.val) = Φ N := by
    intro h hh N hN
    have hm : Φ (N * h.val) - Φ N = 0 := huv (Set.mk_mem_prod hh (hSv hN))
    exact sub_eq_zero.mp hm
  refine ⟨u ∩ u⁻¹, Filter.inter_mem hun (inv_mem_nhds_one G hun), ?_⟩
  rintro g ⟨hgu, hgu'⟩ M
  by_cases hM : M ∈ tsupport (Φ : X → ℂ)
  · exact key g hgu M hM
  by_cases hgM : M * g.val ∈ tsupport (Φ : X → ℂ)
  · have hinv := key g⁻¹ (Set.mem_inv.mp hgu') _ hgM
    have e : M * g.val * (g⁻¹ : G).val = M := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [e] at hinv
    exact hinv.symm
  · rw [image_eq_zero_of_notMem_tsupport hM, image_eq_zero_of_notMem_tsupport hgM]

/-- The integral subgroup `GL_(n+1)(O)` is compact. -/
theorem isCompact_integralSubgroup :
    IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) :=
  Langlands.GeneralLinear.isCompact_integralRange F (n + 1)

/-- The integral subgroup `GL_(n+1)(O)` is open. -/
theorem isOpen_integralSubgroup :
    IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) :=
  Conductor.isOpen_integralSubgroup _ _
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F))

/-- An open subgroup of `GL_(n+1)(O)` under which a full-matrix test function and
a function on the group, right invariant under some open subgroup, are both
right invariant. -/
theorem exists_openSubgroup_rightInvariant (Φ : MatrixTestFunction n F)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ)
    (L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hW : ∀ g, ∀ k ∈ L, W (g * k) = W g) :
    ∃ K₀ : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
      (K₀ : Subgroup (Langlands.GeneralLinear (n + 1) F)) ≤
        Conductor.integralSubgroup (ValuativeRel.valuation F).integer n ∧
      ∀ k ∈ K₀, (∀ M, Φ (M * k.val) = Φ M) ∧ ∀ g, W (g * k) = W g := by
  obtain ⟨U, hU, hΦ⟩ := exists_nhds_matrixTest_rightInvariant F Φ
  let T := (⟨⟩ : LocalFieldData F)
  have hK : (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :
      Set (Langlands.GeneralLinear (n + 1) F)) ∈ 𝓝 1 :=
    (isOpen_integralSubgroup F).mem_nhds (one_mem _)
  have hL : (L : Set (Langlands.GeneralLinear (n + 1) F)) ∈ 𝓝 1 :=
    L.isOpen.mem_nhds (one_mem L)
  obtain ⟨K₀, -, hK₀⟩ := T.generalLinearCompactOpen (n + 1) _
    (Filter.inter_mem (Filter.inter_mem hU hL) hK)
  exact ⟨K₀, fun k hk => (hK₀ hk).2, fun k hk => ⟨hΦ k (hK₀ hk).1.1,
    fun g => hW g k (hK₀ hk).1.2⟩⟩

end Padic

end Langlands.AllField.GodementJacquet.CosetSum
