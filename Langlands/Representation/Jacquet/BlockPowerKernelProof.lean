import Langlands.Representation.Jacquet.CanonicalLiftStatement
import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.Group.GL.BlockContractionProof

/-! # The generalized compression kernel is the upper Jacquet kernel -/

namespace Langlands.Jacquet

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
theorem blockPowerKernel_eq_jacquetKernel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        powerKernelSup ρ hρ K hK (B.blockScalar F.Carrier a) =
          LinearMap.ker (fixedJacquetMap ρ
            (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) K.toSubgroup) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ K hK hfac a ha
  have hweak (r : ℕ) : B.IsWeaklyContracting T (a ^ r) := by
    induction r with
    | zero => simpa only [pow_zero] using B.isWeaklyContracting_one T
    | succ r hr => simpa only [pow_succ] using GeneralLinear.BlockShape.IsWeaklyContracting.mul B T hr ha.weak
  have hpow (r : ℕ) :
      compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) ^ r =
        compressedAction ρ hρ K hK (B.blockScalar F.Carrier (a ^ r)) := by
    induction r with
    | zero => simp only [pow_zero, map_one, compressedAction_one]; rfl
    | succ r hr =>
      rw [pow_succ, hr, pow_succ,
        blockCompressedAction_mul F T n B V ρ hρ K hK hfac _ _ (hweak r) ha.weak]
  have hfixed (v : fixedVectors ρ K.toSubgroup) :
      v ∈ LinearMap.ker (fixedJacquetMap ρ
        (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) K.toSubgroup) ↔
        mk ρ (B.unipotentSubgroup F.Carrier) v.val = 0 := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext_iff
  apply le_antisymm
  · apply iSup_le
    intro r v hv
    apply (hfixed v).mpr
    have hz : compressedAction ρ hρ K hK (B.blockScalar F.Carrier (a ^ r)) v = 0 := by
      simpa only [LinearMap.mem_ker, hpow r] using hv
    have hq := blockCompressedAction_mk F T n B V ρ hρ K hK hfac
      (a ^ r) (hweak r) v
    rw [hz] at hq
    have hi := (Representation.apply_bijective
      (action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier))
      (B.blockScalarInLevi F.Carrier (a ^ r))).injective
    apply hi
    simpa only [ZeroMemClass.coe_zero, map_zero] using hq.symm
  · intro v hv
    have hvrel := (mk_eq_zero ρ (B.unipotentSubgroup F.Carrier) v.val).mp
      ((hfixed v).mp hv)
    have hc (x : B.unipotentSubgroup F.Carrier) :
        ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
          (B.blockScalar F.Carrier a) ^ s * x.val *
            ((B.blockScalar F.Carrier a) ^ s)⁻¹ ∈ K := by
      obtain ⟨r, hr⟩ := B.strictPowers_eventually_mem_iwahori T K a ha x.val 1
        x.property (B.oppositeUnipotentSubgroup F.Carrier).one_mem
      exact ⟨r, fun s hs => (hr s hs).1.1⟩
    obtain ⟨r, hr⟩ := relations_eventually_average_zero ρ hρ K hK
      (B.unipotentSubgroup F.Carrier) (B.blockScalar F.Carrier a) hc v.val hvrel
    apply (le_iSup (fun s : ℕ => LinearMap.ker
      (compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) ^ s)) r)
    rw [LinearMap.mem_ker, hpow r]
    apply Subtype.ext
    change Compact.averageMap ρ hρ K hK
      (ρ (B.blockScalar F.Carrier (a ^ r)) v.val) = 0
    rw [map_pow]
    exact hr r le_rfl

/-- The complete published generalized-kernel clause, with no additional hypotheses. -/
theorem blockPowerKernelJacquet {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    BlockPowerKernelJacquetClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdmissible
  dsimp only
  intro K hK hfac a ha
  exact blockPowerKernel_eq_jacquetKernel F T B V ρ hAdmissible.1 K hK hfac a ha

end Langlands.Jacquet
