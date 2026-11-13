import Langlands.Representation.Jacquet.BlockPowerKernelProof
import Langlands.AllField.Group.GL.BlockContractionProof
import Langlands.AllField.Representation.Jacquet.BlockCompressionProof
import Langlands.AllField.Representation.Jacquet.CanonicalLiftStatement
/-! # The generalized compression kernel is the upper Jacquet kernel -/

namespace Langlands.AllField.Jacquet
open Langlands.Jacquet hiding BlockCompressionStatement BlockStableImageJacquetBijectiveClause blockCompressedAction_mk blockCompressedAction_mul blockCompression blockPowerKernel_eq_jacquetKernel
open Langlands.AllField.Jacquet

universe uG uF uV

section Averaging

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

private theorem average_right_invariant (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (k : K) (v : V) :
    Compact.averageMap ρ hρ K hK (ρ k.val v) = Compact.averageMap ρ hρ K hK v := by
  let τ := ρ.comp K.toSubgroup.subtype
  have ho : Compact.orbit τ (τ k v) = Compact.orbit τ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * k, by simp⟩
    · rintro ⟨h, rfl⟩
      refine ⟨h * k⁻¹, ?_⟩
      simp [map_mul, Module.End.mul_apply]
  change Compact.orbitMean τ (τ k v) = Compact.orbitMean τ v
  unfold Compact.orbitMean
  rw [ho]

/-- Span induction combines the eventual thresholds for genuine Jacquet relations. -/
private theorem relations_eventually_average_zero
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (N : Subgroup G) (g : G)
    (hc : ∀ x : N, ∃ r : ℕ, ∀ s : ℕ, r ≤ s → g ^ s * x.val * (g ^ s)⁻¹ ∈ K)
    (v : V) (hv : v ∈ relations ρ N) :
    ∃ r : ℕ, ∀ s : ℕ, r ≤ s → Compact.averageMap ρ hρ K hK (ρ (g ^ s) v) = 0 := by
  rw [relations_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, w⟩, rfl⟩ := hw
    obtain ⟨r, hr⟩ := hc x
    refine ⟨r, fun s hs => ?_⟩
    rw [map_sub, map_sub, sub_eq_zero]
    calc
      _ = Compact.averageMap ρ hρ K hK
          (ρ (g ^ s * x.val * (g ^ s)⁻¹) (ρ (g ^ s) w)) := by
        congr 1
        simp only [← Module.End.mul_apply, ← map_mul ρ]
        congr 1
        group
      _ = _ := average_right_invariant ρ hρ K hK ⟨_, hr s hs⟩ _
  | zero => exact ⟨0, fun s _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨rx, hx⟩ := hx
    obtain ⟨ry, hy⟩ := hy
    refine ⟨max rx ry, fun s hs => ?_⟩
    rw [map_add, map_add, hx s (le_trans (le_max_left _ _) hs),
      hy s (le_trans (le_max_right _ _) hs), add_zero]
  | smul c x _ hx =>
    obtain ⟨r, hr⟩ := hx
    refine ⟨r, fun s hs => ?_⟩
    rw [map_smul, map_smul, hr s hs, smul_zero]

end Averaging

/-- Equality with the actual fixed Jacquet kernel, already valid for smooth representations. -/
theorem blockPowerKernel_eq_jacquetKernel 
    (F : Type uF) [Field F] (T : LocalFieldData F) {n : ℕ}
    (B : GeneralLinear.BlockShape n) (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F))
      (hK : IsCompact (K : Set (GeneralLinear n F))),
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K →
      ∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a →
        powerKernelSup ρ hρ K hK (B.blockScalar F a) =
          LinearMap.ker (fixedJacquetMap ρ
            (B.unipotentSubgroup F) (B.leviSubgroup F)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F) K.toSubgroup) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac a ha
  have hweak (r : ℕ) : (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T (a ^ r) := by
    induction r with
    | zero => simpa only [pow_zero] using (Langlands.AllField.GeneralLinear.BlockShape.isWeaklyContracting_one B) T
    | succ r hr => simpa only [pow_succ] using Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting.mul B T hr ha.weak
  have hpow (r : ℕ) :
      compressedAction ρ hρ K hK (B.blockScalar F a) ^ r =
        compressedAction ρ hρ K hK (B.blockScalar F (a ^ r)) := by
    induction r with
    | zero => simp only [pow_zero, map_one, compressedAction_one]; rfl
    | succ r hr =>
      rw [pow_succ, hr, pow_succ,
        blockCompressedAction_mul F T n B V ρ hρ K hK hfac _ _ (hweak r) ha.weak]
  have hfixed (v : fixedVectors ρ K.toSubgroup) :
      v ∈ LinearMap.ker (fixedJacquetMap ρ
        (B.unipotentSubgroup F) (B.leviSubgroup F)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F) K.toSubgroup) ↔
        mk ρ (B.unipotentSubgroup F) v.val = 0 := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext_iff
  apply le_antisymm
  · apply iSup_le
    intro r v hv
    apply (hfixed v).mpr
    have hz : compressedAction ρ hρ K hK (B.blockScalar F (a ^ r)) v = 0 := by
      simpa only [LinearMap.mem_ker, hpow r] using hv
    have hq := blockCompressedAction_mk F T n B V ρ hρ K hK hfac
      (a ^ r) (hweak r) v
    rw [hz] at hq
    have hi := (Representation.apply_bijective
      (action ρ (B.unipotentSubgroup F) (B.leviSubgroup F)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F))
      (B.blockScalarInLevi F (a ^ r))).injective
    apply hi
    simpa only [ZeroMemClass.coe_zero, map_zero] using hq.symm
  · intro v hv
    have hvrel := (mk_eq_zero ρ (B.unipotentSubgroup F) v.val).mp
      ((hfixed v).mp hv)
    have hc (x : B.unipotentSubgroup F) :
        ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
          (B.blockScalar F a) ^ s * x.val *
            ((B.blockScalar F a) ^ s)⁻¹ ∈ K := by
      obtain ⟨r, hr⟩ := (Langlands.AllField.GeneralLinear.BlockShape.strictPowers_eventually_mem_iwahori B) T K a ha x.val 1
        x.property (B.oppositeUnipotentSubgroup F).one_mem
      exact ⟨r, fun s hs => (hr s hs).1.1⟩
    obtain ⟨r, hr⟩ := relations_eventually_average_zero ρ hρ K hK
      (B.unipotentSubgroup F) (B.blockScalar F a) hc v.val hvrel
    apply (le_iSup (fun s : ℕ => LinearMap.ker
      (compressedAction ρ hρ K hK (B.blockScalar F a) ^ s)) r)
    rw [LinearMap.mem_ker, hpow r]
    apply Subtype.ext
    change Compact.averageMap ρ hρ K hK
      (ρ (B.blockScalar F (a ^ r)) v.val) = 0
    rw [map_pow]
    exact hr r le_rfl

end Langlands.AllField.Jacquet
