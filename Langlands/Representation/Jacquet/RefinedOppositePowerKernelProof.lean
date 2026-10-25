import Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftStatement
import Langlands.Representation.Jacquet.RefinedOppositeCompressionProof
import Langlands.Group.GL.BlockContractionProof

namespace Langlands.Jacquet

open GeneralLinear Geometric

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

/-- The actual product opposite generalized kernel, already for smooth inputs. -/
theorem refinedOppositePowerKernel_eq_jacquetKernel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        let KP := CuspidalSupport.leviPiOpenSubgroup T B K
        let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
        let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
        powerKernelSup ρ hρ KP hKP g =
          LinearMap.ker (fixedJacquetMap ρ
            (refinedOppositeUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
            (fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)
            KP.toSubgroup) := by
  classical
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hρ K hK hfac a ha
  let KP := CuspidalSupport.leviPiOpenSubgroup T B K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
  let N := refinedOppositeUnipotent F.Carrier B S
  let M := refinedLevi F.Carrier B S
  let hMN : M ≤ Subgroup.normalizer (N : Set (B.Levi F.Carrier)) :=
    fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property
  let g := fun (b : ∀ i, Fin (S i).length → F.Carrierˣ) =>
    (fun i => ((S i).blockScalar F.Carrier (b i))⁻¹ : B.Levi F.Carrier)
  let gm (b : ∀ i, Fin (S i).length → F.Carrierˣ) : M :=
    ⟨g b, fun i _ => (S i).leviSubgroup F.Carrier |>.inv_mem
      ((S i).blockScalarInLevi F.Carrier (b i)).property⟩
  have hweak (r : ℕ) : ∀ i, (S i).IsWeaklyContracting T ((a ^ r) i) := by
    intro i
    induction r with
    | zero => simpa only [pow_zero, Pi.one_apply] using (S i).isWeaklyContracting_one T
    | succ r hr =>
      simpa only [pow_succ, Pi.mul_apply] using
        BlockShape.IsWeaklyContracting.mul (S i) T hr (ha i).weak
  have hgp (r : ℕ) : g (a ^ r) = g a ^ r := by
    funext i
    simp only [g, Pi.pow_apply, map_pow, inv_pow]
  have hpow (r : ℕ) :
      compressedAction ρ hρ KP hKP (g a) ^ r =
        compressedAction ρ hρ KP hKP (g (a ^ r)) := by
    induction r with
    | zero =>
      rw [hgp, pow_zero, pow_zero, compressedAction_one]
      rfl
    | succ r hr =>
      rw [pow_succ, hr, pow_succ]
      exact ((refinedOppositeCompression p F T n B S V ρ hρ K hK hfac).1
        (a ^ r) a (hweak r) (fun i => (ha i).weak)).symm
  have hfixed (v : fixedVectors ρ KP.toSubgroup) :
      v ∈ LinearMap.ker (fixedJacquetMap ρ N M hMN KP.toSubgroup) ↔
        mk ρ N v.val = 0 := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext_iff
  change powerKernelSup ρ hρ KP hKP (g a) =
    LinearMap.ker (fixedJacquetMap ρ N M hMN KP.toSubgroup)
  apply le_antisymm
  · apply iSup_le
    intro r v hv
    apply (hfixed v).mpr
    have hz : compressedAction ρ hρ KP hKP (g (a ^ r)) v = 0 := by
      simpa only [LinearMap.mem_ker, hpow r] using hv
    have hq := (refinedOppositeCompression p F T n B S V ρ hρ K hK hfac).2
      (a ^ r) (hweak r) v
    change mk ρ N (compressedAction ρ hρ KP hKP (g (a ^ r)) v).val =
      mk ρ N (ρ (g (a ^ r)) v.val) at hq
    rw [hz] at hq
    apply (Representation.apply_bijective (action ρ N M hMN) (gm (a ^ r))).injective
    change mk ρ N (ρ (g (a ^ r)) v.val) = _
    simpa only [ZeroMemClass.coe_zero, map_zero] using hq.symm
  · intro v hv
    have hvrel := (mk_eq_zero ρ N v.val).mp ((hfixed v).mp hv)
    have hc (x : N) : ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
        g a ^ s * x.val * (g a ^ s)⁻¹ ∈ KP := by
      have hx : ∀ i, x.val i ∈ (S i).oppositeUnipotentSubgroup F.Carrier :=
        (mem_refinedOppositeUnipotent F.Carrier B S x.val).mp x.property
      choose r hr using fun i => (S i).strictPowers_eventually_mem_iwahori T (K i)
        (a i) (ha i) 1 (x.val i)
        ((S i).unipotentSubgroup F.Carrier).one_mem (hx i)
      refine ⟨Finset.univ.sup r, fun s hs => ?_⟩
      apply (CuspidalSupport.mem_leviPiOpenSubgroup T B K _).mpr
      intro i
      have hi := (hr i s ((Finset.le_sup (Finset.mem_univ i)).trans hs)).2.1
      change ((S i).blockScalar F.Carrier (a i))⁻¹ ^ s * x.val i *
        ((S i).blockScalar F.Carrier (a i)) ^ s ∈ K i at hi
      simpa only [g, Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, inv_pow, inv_inv] using hi
    obtain ⟨r, hr⟩ := relations_eventually_average_zero ρ hρ KP hKP N (g a) hc v.val hvrel
    apply (le_iSup (fun s : ℕ => LinearMap.ker
      (compressedAction ρ hρ KP hKP (g a) ^ s)) r)
    rw [LinearMap.mem_ker, hpow r]
    apply Subtype.ext
    change Compact.averageMap ρ hρ KP hKP (ρ (g (a ^ r)) v.val) = 0
    rw [hgp]
    exact hr r le_rfl

/-- The exact published product opposite kernel clause. -/
theorem refinedOppositePowerKernelJacquet {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    RefinedOppositePowerKernelJacquetClause F T B S V := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hAdmissible
  dsimp only
  intro K hK hfac a ha
  exact refinedOppositePowerKernel_eq_jacquetKernel F T B S V ρ hAdmissible.1 K hK hfac a ha

end Langlands.Jacquet
