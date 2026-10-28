import Langlands.Representation.Classification.ProductLeviNecessityCombinatorics
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Group.GL.BlockContractionProof
import Langlands.Representation.Jacquet.StablePairingProof

/-!
# Eigenvectors of compressions from generalized Jacquet exponents

A generalized eigencharacter of the normalized refined Jacquet module gives a
nonzero compact-open fixed vector which is an eigenvector of the compression by
any weakly contracting block-scalar tuple, with eigenvalue the square root of the
refined modulus times the character. A smooth functional which is invariant under
the same compact open subgroup and nonzero on that vector then has the matrix
coefficients `λ ^ m ℓ(x)` along the powers of the block-scalar tuple.
-/

noncomputable section

open scoped BigOperators NNReal Topology

namespace Langlands.ProductLeviNecessity

open GeneralLinear Geometric ProductLeviChamber

universe uF uV uG

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (C : BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem isWeaklyContracting_mul {N : ℕ} (B : BlockShape N) {a b : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (hb : B.IsWeaklyContracting T b) :
    B.IsWeaklyContracting T (a * b) := by
  intro i j hij
  rw [map_mul, Units.val_mul, NNReal.coe_mul]
  exact (mul_le_mul (ha i j hij) (hb i j hij) (NNReal.coe_nonneg _) zero_le_one).trans
    (mul_one 1).le

theorem isWeaklyContracting_pow {N : ℕ} (B : BlockShape N) {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (m : ℕ) : B.IsWeaklyContracting T (a ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact B.isWeaklyContracting_one T
  | succ m ih => rw [pow_succ]; exact isWeaklyContracting_mul T B ih ha

/-- Compressions by weakly contracting block-scalar tuples commute. -/
theorem compressedAction_commute :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (C.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (C.size i) F.Carrier)))
      (D : BlockRefinement C), (∀ i, (D i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a b : ∀ i, Fin (D i).length → F.Carrierˣ,
        (∀ i, (D i).IsWeaklyContracting T (a i)) → (∀ i, (D i).IsWeaklyContracting T (b i)) →
        Commute
          (Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (fun i => (D i).blockScalar F.Carrier (a i)))
          (Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (fun i => (D i).blockScalar F.Carrier (b i))) := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hρ K hK D hfac a b ha hb
  have h := Jacquet.refinedUpperCompression F T C D V ρ hρ K hK hfac
  have h1 := h.1 a b ha hb
  have h2 := h.1 b a hb ha
  rw [mul_comm b a] at h2
  change _ * _ = _ * _
  rw [← h1, ← h2]

/-- Compression by a power of a weakly contracting block-scalar tuple is the power
of the compression. -/
theorem compressedAction_pow :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (C.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (C.size i) F.Carrier)))
      (D : BlockRefinement C), (∀ i, (D i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (D i).length → F.Carrierˣ,
        (∀ i, (D i).IsWeaklyContracting T (a i)) → ∀ m : ℕ,
        Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            ((fun i => (D i).blockScalar F.Carrier (a i) : C.Levi F.Carrier) ^ m) =
          Jacquet.compressedAction ρ hρ (CuspidalSupport.leviPiOpenSubgroup T C K)
            (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
            (fun i => (D i).blockScalar F.Carrier (a i)) ^ m := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hρ K hK D hfac a ha m
  have hpow : ∀ m : ℕ, ((fun i => (D i).blockScalar F.Carrier (a i) : C.Levi F.Carrier) ^ m) =
      fun i => (D i).blockScalar F.Carrier ((a ^ m) i) := by
    intro m
    funext i
    rw [Pi.pow_apply, Pi.pow_apply, map_pow]
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, Jacquet.compressedAction_one]
    rfl
  | succ m ih =>
    rw [hpow (m + 1), pow_succ a m, (Jacquet.refinedUpperCompression F T C D V ρ hρ K hK hfac).1
      (a ^ m) a (fun i => by rw [Pi.pow_apply]; exact isWeaklyContracting_pow T (D i) (ha i) m) ha,
      ← hpow m, ih, pow_succ]

/-- The eigenvalue `√δ(c) ψ(c)` of the compression by the block-scalar tuple `c`,
where `δ` is the refined modulus. -/
def compressionEigenvalue (D : BlockRefinement C)
    (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ)
    (c : ∀ i, Fin (D i).length → F.Carrierˣ) : ℂ :=
  (Real.sqrt ((T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
    ((C.flatten D).blockScalarLevi F.Carrier (flatScalars C D c))) : ℝ≥0) : ℝ) : ℂ) *
    (ψ (flatScalars C D c) : ℂ)

/-- A generalized eigencharacter of the pulled-back normalized refined Jacquet
module gives a nonzero compact-open fixed vector which is an eigenvector of the
compression by any weakly contracting block-scalar tuple. The compact open
subgroup can be chosen inside any identity neighbourhood. -/
theorem exists_compressedAction_eigenvector :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (hadm : IsAdmissible ρ)
      (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D ρ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ {U : Set (C.Levi F.Carrier)}, U ∈ 𝓝 (1 : C.Levi F.Carrier) →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsWeaklyContracting T (c i)) →
      ∃ (K : ∀ j, OpenSubgroup (GeneralLinear (C.size j) F.Carrier))
        (hK : ∀ j, IsCompact (K j : Set (GeneralLinear (C.size j) F.Carrier))),
        (∀ j (S : BlockShape (C.size j)), S.HasBlockIwahoriFactorization T (K j)) ∧
        (CuspidalSupport.leviPiOpenSubgroup T C K : Set (C.Levi F.Carrier)) ⊆ U ∧
        ∃ x : fixedVectors ρ (CuspidalSupport.leviPiOpenSubgroup T C K).toSubgroup, x ≠ 0 ∧
          Jacquet.compressedAction ρ hadm.1 (CuspidalSupport.leviPiOpenSubgroup T C K)
              (CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK)
              (fun i => (D i).blockScalar F.Carrier (c i)) x =
            compressionEigenvalue T C D ψ c • x := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm D ψ hgen U hU c hc
  classical
  let N := refinedUnipotent F.Carrier C D
  let M := refinedLevi F.Carrier C D
  let hMN : M ≤ Subgroup.normalizer N :=
    fun m hm => (refinedLeviNormalizer F.Carrier C D ⟨m, hm⟩).property
  let z := (flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
    ((C.flatten D).blockScalarLevi F.Carrier)
  let π := (T.normalizedRefinedJacquet C D ρ).comp z
  obtain ⟨k, w0, hw0, hk⟩ := (isGeneralizedEigencharacter_iff π ψ).mp hgen
  obtain ⟨v0, rfl⟩ := Jacquet.mk_surjective ρ N w0
  obtain ⟨U0, hU0⟩ := hadm.1 v0
  obtain ⟨K, hK, hfac, hKU⟩ := CuspidalSupport.exists_leviPiOpenSubgroup_subset_forall T C
    (Filter.inter_mem hU (U0.isOpen.mem_nhds U0.one_mem))
  let KP := CuspidalSupport.leviPiOpenSubgroup T C K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK
  have hfacD : ∀ i, (D i).HasBlockIwahoriFactorization T (K i) := fun i => hfac i (D i)
  have hc0 : ∀ i, ∃ a : Fin (D i).length → F.Carrierˣ, (D i).IsStrictlyContracting T a := by
    intro i
    obtain ⟨a, ha⟩ := (D i).deepChamberNonempty T 1 one_pos
    exact ⟨a, BlockShape.IsDeeplyContracting.strict (D i) T ha le_rfl⟩
  choose c0 hc0 using hc0
  let g : C.Levi F.Carrier := fun i => (D i).blockScalar F.Carrier (c i)
  let g0 : C.Levi F.Carrier := fun i => (D i).blockScalar F.Carrier (c0 i)
  let A := Jacquet.compressedAction ρ hadm.1 KP hKP g
  let A0 := Jacquet.compressedAction ρ hadm.1 KP hKP g0
  have hcomm : Commute A A0 := compressedAction_commute T C ρ hadm.1 K hK D hfacD c c0 hc
    (fun i => (hc0 i).weak)
  have hbij := Jacquet.refinedStableImageJacquetBijective F T C D V ρ hadm K hK hfacD c0 hc0
  let J := Jacquet.stableImageJacquetMap ρ hadm.1 KP hKP g0 N M hMN
  let Y := fixedVectors (Jacquet.action ρ N M hMN) (KP.toSubgroup.comap M.subtype)
  have hπ : ∀ (b : Fin (C.flatten D).length → F.Carrierˣ) (y : Jacquet.Coinvariants ρ N),
      π b y = (T.refinedLeviInverseHalfModulus C D (z b) : ℂ) •
        Jacquet.action ρ N M hMN (z b) y := by
    intro b y
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N y
    change T.normalizedRefinedJacquet C D ρ (z b) (refinedJacquetMk C D ρ v) = _
    rw [T.normalizedRefinedJacquet_mk, Jacquet.action_mk]
  have hzval : ∀ b, ((z b : M) : C.Levi F.Carrier) =
      fun i => (D i).blockScalar F.Carrier (fun l => b (C.flattenBlockEquiv D ⟨i, l⟩)) :=
    fun b => funext fun i => Geometric.flattenedLeviEquiv_blockScalarLevi_apply F.Carrier C D b i
  have hzcomm : ∀ b (m : M), z b * m = m * z b := by
    intro b m
    apply Subtype.ext
    change ((z b : M) : C.Levi F.Carrier) * m = m * (z b : M)
    rw [hzval b]
    exact blockScalars_commute_refinedLevi (F := F) C D
      (fun i l => b (C.flattenBlockEquiv D ⟨i, l⟩)) m m.property
  have hactcomm : ∀ b (m : M) (y : Jacquet.Coinvariants ρ N),
      Jacquet.action ρ N M hMN (z b) (Jacquet.action ρ N M hMN m y) =
        Jacquet.action ρ N M hMN m (Jacquet.action ρ N M hMN (z b) y) := by
    intro b m y
    rw [← Module.End.mul_apply, ← map_mul, hzcomm, map_mul, Module.End.mul_apply]
  let W : Submodule ℂ (Jacquet.Coinvariants ρ N) := Y ⊓ characterSpace π ψ k
  have hWπ : ∀ b, ∀ y ∈ W, π b y ∈ W := by
    intro b y hy
    obtain ⟨hyY, hyC⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨?_, map_mem_characterSpace π ψ k b hyC⟩
    rw [hπ]
    refine Submodule.smul_mem _ _ ?_
    intro h
    have hh := hyY h
    change Jacquet.action ρ N M hMN h.val y = y at hh
    change Jacquet.action ρ N M hMN h.val (Jacquet.action ρ N M hMN (z b) y) =
      Jacquet.action ρ N M hMN (z b) y
    rw [← hactcomm b h.val y, hh]
  have hv0Y : Jacquet.mk ρ N v0 ∈ Y := by
    intro h
    change Jacquet.action ρ N M hMN h.val (Jacquet.mk ρ N v0) = Jacquet.mk ρ N v0
    rw [Jacquet.action_mk]
    have hmem : ((h.val : M) : C.Levi F.Carrier) ∈ U0 := (hKU h.property).2
    have := hU0 ⟨_, hmem⟩
    change ρ ((h.val : M) : C.Levi F.Carrier) v0 = v0 at this
    change Jacquet.mk ρ N (ρ ((h.val : M) : C.Levi F.Carrier) v0) = _
    rw [this]
  have hv0W : Jacquet.mk ρ N v0 ∈ W :=
    Submodule.mem_inf.mpr ⟨hv0Y, (mem_characterSpace π ψ k _).mpr hk⟩
  let b0 := flatScalars C D c
  let Nb : Module.End ℂ (Jacquet.Coinvariants ρ N) := π b0 - (ψ b0 : ℂ) • 1
  have hNW : ∀ y ∈ W, Nb y ∈ W := by
    intro y hy
    change π b0 y - (ψ b0 : ℂ) • y ∈ W
    exact Submodule.sub_mem _ (hWπ b0 y hy) (Submodule.smul_mem _ _ hy)
  have hNk : ∀ y ∈ W, (Nb ^ k) y = 0 := fun y hy =>
    (mem_characterSpace π ψ k y).mp (Submodule.mem_inf.mp hy).2 b0
  obtain ⟨w, hwW, hw0', hNw⟩ := exists_mem_ker_of_pow_eq_zero Nb hNW k hNk hv0W hw0
  have hπw : π b0 w = (ψ b0 : ℂ) • w := by
    have h : π b0 w - (ψ b0 : ℂ) • w = 0 := hNw
    exact sub_eq_zero.mp h
  have hgM : g ∈ M := blockScalars_mem_refinedLevi C D c
  have hzb0 : z b0 = ⟨g, hgM⟩ := Subtype.ext (flattenedLeviEquiv_flatScalars_val C D c)
  set lam : ℂ := (((Real.sqrt ((T.refinedLeviModulus C D (z b0) : ℝ≥0) : ℝ)) : ℝ) : ℂ) *
    (ψ b0 : ℂ) with hlam
  have hsqrt0 : ((Real.sqrt ((T.refinedLeviModulus C D (z b0) : ℝ≥0) : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < Real.sqrt ((T.refinedLeviModulus C D (z b0) : ℝ≥0) : ℝ) :=
      Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _)))
    exact_mod_cast hpos.ne'
  have hactw : Jacquet.action ρ N M hMN ⟨g, hgM⟩ w = lam • w := by
    rw [hπ, hzb0, T.refinedLeviInverseHalfModulus_apply] at hπw
    have h := congrArg (fun y => (((Real.sqrt ((T.refinedLeviModulus C D (z b0) : ℝ≥0) : ℝ)) :
      ℝ) : ℂ) • y) hπw
    simp only [smul_smul] at h
    rw [hzb0, ← Real.coe_sqrt, mul_inv_cancel₀ (by rw [Real.coe_sqrt, ← hzb0]; exact hsqrt0),
      one_smul] at h
    rw [h, hlam, hzb0, Real.coe_sqrt]
  have hwY : w ∈ Y := (Submodule.mem_inf.mp hwW).1
  obtain ⟨x', hx'⟩ := hbij.2 ⟨w, hwY⟩
  let x : fixedVectors ρ KP.toSubgroup := x'.val
  have hJx : (J x' : Jacquet.Coinvariants ρ N) = Jacquet.mk ρ N (x : V) := rfl
  have hxw : Jacquet.mk ρ N (x : V) = w := by
    rw [← hJx, hx']
  have hx0 : x ≠ 0 := by
    intro h0
    apply hw0'
    rw [← hxw, h0]
    simp
  have hAx : A x ∈ Jacquet.stableImage ρ hadm.1 KP hKP g0 := by
    have hxs := x'.property
    rw [Jacquet.mem_stableImage] at hxs ⊢
    intro r
    obtain ⟨y, hy⟩ := hxs r
    refine ⟨A y, ?_⟩
    exact (LinearMap.congr_fun (hcomm.pow_right r).eq y).symm.trans (congrArg A hy)
  have hJA : J ⟨A x, hAx⟩ = J (lam • x') := by
    apply Subtype.ext
    change Jacquet.mk ρ N ((A x : fixedVectors ρ KP.toSubgroup) : V) =
      ((J (lam • x') : Y) : Jacquet.Coinvariants ρ N)
    rw [map_smul]
    change _ = lam • (J x' : Jacquet.Coinvariants ρ N)
    rw [(Jacquet.refinedUpperCompression F T C D V ρ hadm.1 K hK hfacD).2 c hc x, hJx, hxw,
      ← hactw, ← hxw, Jacquet.action_mk]
  have hAxeq : A x = lam • x := congrArg Subtype.val (hbij.1 hJA)
  exact ⟨K, hK, hfac, fun y hy => (hKU hy).1, x, hx0, hAxeq⟩

/-- A generalized eigencharacter of the pulled-back normalized refined Jacquet
module gives, inside any identity neighbourhood, a compact open subgroup `K`, a
`K`-fixed vector `x` and a `K`-invariant smooth functional `ℓ` with `ℓ(x) ≠ 0`,
whose matrix coefficient along the powers of a weakly contracting block-scalar
tuple `c` is `λ ^ m ℓ(x)` for the compression eigenvalue `λ` of `c`. -/
theorem exists_eigen_coefficient :
    letI := T.topology
    letI := T.leviTopologicalGroup C
    ∀ (ρ : Representation ℂ (C.Levi F.Carrier) V) (_ : IsAdmissible ρ)
      (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
      IsGeneralizedEigencharacter
        ((T.normalizedRefinedJacquet C D ρ).comp
          ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
            ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
      ∀ {U : Set (C.Levi F.Carrier)}, U ∈ 𝓝 (1 : C.Levi F.Carrier) →
      ∀ (c : ∀ i, Fin (D i).length → F.Carrierˣ), (∀ i, (D i).IsWeaklyContracting T (c i)) →
      ∃ K : OpenSubgroup (C.Levi F.Carrier), IsCompact (K : Set (C.Levi F.Carrier)) ∧
        (K : Set (C.Levi F.Carrier)) ⊆ U ∧
        ∃ (ℓ : SmoothDual ρ) (x : V), (ℓ : Module.Dual ℂ V) x ≠ 0 ∧
          (∀ k ∈ K, ρ k x = x) ∧
          (∀ k ∈ K, ∀ y, (ℓ : Module.Dual ℂ V) (ρ k y) = (ℓ : Module.Dual ℂ V) y) ∧
          ∀ m : ℕ, (ℓ : Module.Dual ℂ V)
              (ρ ((fun i => (D i).blockScalar F.Carrier (c i) : C.Levi F.Carrier) ^ m) x) =
            compressionEigenvalue T C D ψ c ^ m * (ℓ : Module.Dual ℂ V) x := by
  let := T.topology
  let := T.leviTopologicalGroup C
  intro ρ hadm D ψ hgen U hU c hc
  obtain ⟨K, hK, hfac, hKU, x, hx0, hAx⟩ :=
    exists_compressedAction_eigenvector T C ρ hadm D ψ hgen hU c hc
  let KP := CuspidalSupport.leviPiOpenSubgroup T C K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T C K hK
  let A := Jacquet.compressedAction ρ hadm.1 KP hKP
    (fun i => (D i).blockScalar F.Carrier (c i))
  let lam := compressionEigenvalue T C D ψ c
  have hxV : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨ℓ0, hℓ0⟩ : ∃ ℓ0 : Module.Dual ℂ V, ℓ0 x ≠ 0 := by
    simpa using mt (Module.forall_dual_apply_eq_zero_iff ℂ (x : V)).mp hxV
  let avg := Compact.averageMap ρ hadm.1 KP hKP
  let ℓ : Module.Dual ℂ V := ℓ0 ∘ₗ avg
  have hℓinv : ∀ k ∈ KP, ∀ y, ℓ (ρ k y) = ℓ y := fun k hk y => by
    change ℓ0 (avg (ρ k y)) = ℓ0 (avg y)
    rw [Jacquet.averageMap_apply_of_mem ρ hadm.1 KP hKP hk]
  have hℓsmooth : ℓ ∈ smoothVectors ρ.dual := by
    refine ⟨KP, ?_⟩
    intro k
    change ρ.dual k ℓ = ℓ
    ext y
    rw [Representation.dual_apply, Module.Dual.transpose_apply]
    exact hℓinv _ (KP.inv_mem k.property) y
  have hℓx : ℓ x = ℓ0 x := by
    change ℓ0 (avg x) = ℓ0 x
    rw [Compact.averageMap_id ρ hadm.1 KP hKP x x.property]
  have hAm : ∀ m : ℕ, (A ^ m) x = lam ^ m • x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul]
      rw [hAx, smul_smul, pow_succ]
  refine ⟨KP, hKP, fun y hy => hKU hy, ⟨ℓ, hℓsmooth⟩, x, ?_, fun k hk => x.property ⟨k, hk⟩,
    hℓinv, fun m => ?_⟩
  · change ℓ x ≠ 0
    rw [hℓx]
    exact hℓ0
  · change ℓ (ρ _ x) = lam ^ m * ℓ x
    have hpow := compressedAction_pow T C ρ hadm.1 K hK D (fun i => hfac i (D i)) c hc m
    have h : avg (ρ ((fun i => (D i).blockScalar F.Carrier (c i) : C.Levi F.Carrier) ^ m) x) =
        ((A ^ m) x : V) := by
      rw [← hpow]
      rfl
    change ℓ0 (avg _) = _
    rw [h, hAm, Submodule.coe_smul, map_smul, smul_eq_mul, hℓx]

end Langlands.ProductLeviNecessity
