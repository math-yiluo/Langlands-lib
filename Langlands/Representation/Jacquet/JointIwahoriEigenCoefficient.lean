import Langlands.Representation.Jacquet.WeakIwahoriBasis
import Langlands.Representation.Jacquet.IwahoriEigenCoefficient
import Langlands.Representation.Jacquet.CompressionStabilizationProof

/-! # Exact coefficients along a strict and a weak contraction

For a compact open subgroup with an Iwahori factorization, an element `b` with an
Iwahori contraction and a commuting element `a` with a weak Iwahori contraction,
a common eigenvector of `a` and `b` in the invariants of the Jacquet module lifts
to a fixed vector whose compressions by `a` and `b` act by the same scalars. A
smooth invariant functional then has the exact coefficients
`ℓ(ρ(a ^ m * b ^ n) x) = μ_a ^ m * μ_b ^ n * ℓ(x)`.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

namespace IsWeakIwahoriContraction

variable {K : OpenSubgroup G} {N M Nbar : Subgroup G}

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hK : IsCompact (K : Set G))

/-- Compression is multiplicative on weakly contracting elements of a factorized
compact open subgroup. -/
theorem compressedAction_mul
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    {g h : G} (hg : IsWeakIwahoriContraction K N M Nbar g)
    (hh : IsWeakIwahoriContraction K N M Nbar h) :
    compressedAction ρ hρ K hK (g * h) =
      compressedAction ρ hρ K hK g * compressedAction ρ hρ K hK h :=
  compressedAction_mul_of_factor ρ hρ K hK N M Nbar hfactor g h
    (fun u hu => (hg.upper u hu).1) (fun l hl => (hh.lower l hl).1)
    (fun m hm => (hh.levi m hm).1)

/-- Compression by a power of a weakly contracting element is the power of its
compression. -/
theorem compressedAction_pow
    (hfactor : ∀ k ∈ K, ∃ l ∈ K.toSubgroup ⊓ Nbar, ∃ m ∈ K.toSubgroup ⊓ M,
      ∃ u ∈ K.toSubgroup ⊓ N, k = l * m * u)
    {g : G} (hg : IsWeakIwahoriContraction K N M Nbar g) (n : ℕ) :
    compressedAction ρ hρ K hK (g ^ n) = compressedAction ρ hρ K hK g ^ n := by
  induction n with
  | zero => simp only [pow_zero, compressedAction_one]; rfl
  | succ n ih =>
    rw [pow_succ, compressedAction_mul ρ hρ hK hfactor (hg.pow n) hg, ih, pow_succ]

end IsWeakIwahoriContraction

/-- A common eigenvector of a strictly contracting element `b` and a commuting
weakly contracting element `a` in the `K ∩ M`-invariants of the ordinary Jacquet
module gives an exact smooth matrix coefficient along all products `a ^ m * b ^ n`. -/
theorem exists_joint_eigen_coefficient_of_jacquet_eigenvector
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (b a : G)
    (hb : IsIwahoriContraction K N M Nbar b) (ha : IsWeakIwahoriContraction K N M Nbar a)
    (hab : Commute a b)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (μb μa : ℂ) (w : Coinvariants ρ N) (hw0 : w ≠ 0)
    (hwK : w ∈ fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))
    (hwb : action ρ N M hMN ⟨b, hb.mem_levi⟩ w = μb • w)
    (hwa : action ρ N M hMN ⟨a, ha.mem_levi⟩ w = μa • w) :
    ∃ (x : fixedVectors ρ K.toSubgroup) (ℓ : SmoothDual ρ),
      (ℓ : Module.Dual ℂ V) x ≠ 0 ∧
      (∀ k ∈ K, ∀ y, (ℓ : Module.Dual ℂ V) (ρ k y) = (ℓ : Module.Dual ℂ V) y) ∧
      ∀ m n : ℕ, (ℓ : Module.Dual ℂ V) (ρ (a ^ m * b ^ n) x) =
        μa ^ m * μb ^ n * (ℓ : Module.Dual ℂ V) x := by
  let C : G → Module.End ℂ (fixedVectors ρ K.toSubgroup) := compressedAction ρ hρ K hK
  have hbw := hb.isWeakIwahoriContraction
  obtain ⟨x, hx0, hxw, hxb⟩ :=
    exists_compressedAction_eigenvector_of_jacquet_eigenvector
      ρ hρ K hK N M Nbar hMN b hb hfin μb w hw0 hwK hwb
  -- The eigenvalue of `b` is nonzero, since `b` acts invertibly on the quotient.
  have hμb : μb ≠ 0 := by
    intro h0
    apply hw0
    have h1 := congrArg (action ρ N M hMN (⟨b, hb.mem_levi⟩ : M)⁻¹) hwb
    rw [h0, zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] at h1
    exact h1
  -- Compressions by `a` and `b` commute.
  have hcomm : C a * C b = C b * C a := by
    change compressedAction ρ hρ K hK a * compressedAction ρ hρ K hK b =
      compressedAction ρ hρ K hK b * compressedAction ρ hρ K hK a
    rw [← IsWeakIwahoriContraction.compressedAction_mul ρ hρ hK hb.factor ha hbw,
      ← IsWeakIwahoriContraction.compressedAction_mul ρ hρ hK hb.factor hbw ha, hab.eq]
  -- The lift is also an eigenvector of the compression by `a`.
  have hxa : C a x = μa • x := by
    let y := C a x - μa • x
    have hmky : fixedJacquetMap ρ N M hMN K.toSubgroup y = 0 := by
      apply Subtype.ext
      rw [map_sub, map_smul]
      change mk ρ N ((C a x : fixedVectors ρ K.toSubgroup) : V) -
        μa • mk ρ N (x : V) = 0
      rw [mk_compressedAction_of_factor ρ hρ K hK N M Nbar hMN hb.factor ⟨a, ha.mem_levi⟩
        (fun l hl => (ha.lower l hl).1) (fun m hm => (ha.levi m hm).1), hxw, hwa, sub_self]
    have hyb : C b y = μb • y := by
      change C b (C a x - μa • x) = μb • (C a x - μa • x)
      have h1 : C b (C a x) = C a (C b x) := by
        rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]
      rw [map_sub, map_smul, h1]
      change C a (C b x) - μa • C b x = _
      rw [show C b x = μb • x from hxb, map_smul, smul_sub, smul_comm μa μb]
    have hyker : y ∈ powerKernelSup ρ hρ K hK b := by
      rw [powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK hb hMN]
      exact hmky
    have hystab : y ∈ stableImage ρ hρ K hK b := by
      rw [mem_stableImage]
      intro r
      refine ⟨(μb ^ r)⁻¹ • y, ?_⟩
      have hpow : (compressedAction ρ hρ K hK b ^ r) y = μb ^ r • y := by
        induction r with
        | zero => simp
        | succ r ih =>
          rw [pow_succ', Module.End.mul_apply, ih, map_smul]
          change μb ^ r • C b y = _
          rw [hyb, smul_smul, pow_succ, mul_comm]
      rw [map_smul, hpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero r hμb), one_smul]
    have hy0 : y = 0 := by
      have hdis := (powerKernelSup_isCompl_stableImage ρ hρ K hK b hfin).disjoint
      exact (Submodule.disjoint_def.mp hdis) y hyker hystab
    exact sub_eq_zero.mp hy0
  -- The averaged functional.
  have hxV : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  obtain ⟨ℓ0, hℓ0⟩ : ∃ ℓ0 : Module.Dual ℂ V, ℓ0 x ≠ 0 := by
    simpa using mt (Module.forall_dual_apply_eq_zero_iff ℂ (x : V)).mp hxV
  let avg := Compact.averageMap ρ hρ K hK
  let ℓ : Module.Dual ℂ V := ℓ0 ∘ₗ avg
  have hℓinv : ∀ k ∈ K, ∀ y, ℓ (ρ k y) = ℓ y := by
    intro k hk y
    change ℓ0 (avg (ρ k y)) = ℓ0 (avg y)
    rw [averageMap_apply_of_mem ρ hρ K hK hk]
  have hℓsmooth : ℓ ∈ smoothVectors ρ.dual := by
    refine ⟨K, ?_⟩
    intro k
    change ρ.dual k ℓ = ℓ
    ext y
    rw [Representation.dual_apply, Module.Dual.transpose_apply]
    exact hℓinv _ (K.inv_mem k.property) y
  have hℓx : ℓ x = ℓ0 x := by
    change ℓ0 (avg x) = ℓ0 x
    rw [Compact.averageMap_id ρ hρ K hK x x.property]
  have hAm : ∀ m : ℕ, (C a ^ m) x = μa ^ m • x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hxa, smul_smul, pow_succ]
  have hBn : ∀ n : ℕ, (C b ^ n) x = μb ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul,
        show C b x = μb • x from hxb, smul_smul, pow_succ, mul_comm (μb ^ n)]
  refine ⟨x, ⟨ℓ, hℓsmooth⟩, ?_, hℓinv, fun m n => ?_⟩
  · change ℓ x ≠ 0
    rw [hℓx]
    exact hℓ0
  · change ℓ (ρ (a ^ m * b ^ n) x) = μa ^ m * μb ^ n * ℓ x
    have hcomp : C (a ^ m * b ^ n) = C a ^ m * C b ^ n := by
      change compressedAction ρ hρ K hK (a ^ m * b ^ n) = _
      rw [IsWeakIwahoriContraction.compressedAction_mul ρ hρ hK hb.factor (ha.pow m)
        (hbw.pow n), IsWeakIwahoriContraction.compressedAction_pow ρ hρ hK hb.factor ha m,
        IsWeakIwahoriContraction.compressedAction_pow ρ hρ hK hb.factor hbw n]
    have hn : avg (ρ (a ^ m * b ^ n) x) = ((C (a ^ m * b ^ n)) x : V) := rfl
    change ℓ0 (avg _) = _
    rw [hn, hcomp, Module.End.mul_apply, hBn, map_smul, hAm, smul_smul,
      Submodule.coe_smul, map_smul, smul_eq_mul, hℓx, mul_comm (μb ^ n) (μa ^ m)]

end Langlands.Jacquet
