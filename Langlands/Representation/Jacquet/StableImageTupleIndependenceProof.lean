import Langlands.Representation.Jacquet.CanonicalLiftCompatibilityStatement
import Langlands.Representation.Jacquet.BlockCompressionProof
import Langlands.Group.GL.BlockContractionProof

/-! # Independence of actual stable images from the strict contracting tuple -/

namespace Langlands.Jacquet

open Filter
open scoped NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

private theorem weak_pow {a : Fin B.length → F.Carrierˣ}
    (ha : B.IsWeaklyContracting T a) (r : ℕ) :
    B.IsWeaklyContracting T (a ^ r) := by
  induction r with
  | zero => simp only [pow_zero]; exact B.isWeaklyContracting_one T
  | succ r hr => simpa only [pow_succ] using GeneralLinear.BlockShape.IsWeaklyContracting.mul B T hr ha

private theorem exists_weak_quotient (a d : Fin B.length → F.Carrierˣ)
    (ha : B.IsStrictlyContracting T a) :
    ∃ r : ℕ, B.IsWeaklyContracting T (a ^ r * d⁻¹) := by
  have he : ∀ᶠ r : ℕ in atTop, ∀ i j : Fin B.length, i < j →
      (((B.blockScalarRatio T i j (a ^ r) : ℝ≥0) : ℝ)) <
        (((B.blockScalarRatio T i j d : ℝ≥0) : ℝ)) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hpos : 0 < (((B.blockScalarRatio T i j d : ℝ≥0) : ℝ)) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (B.blockScalarRatio T i j d)))
    obtain ⟨r, hr⟩ := B.strictPowersEventuallyDeep T a ha _ hpos
    exact eventually_atTop.mpr ⟨r, fun s hs hij => hr s hs i j hij⟩
  obtain ⟨r, hr⟩ := he.exists
  refine ⟨r, fun i j hij => ?_⟩
  have hpos : 0 < (((B.blockScalarRatio T i j d : ℝ≥0) : ℝ)) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (Units.ne_zero (B.blockScalarRatio T i j d)))
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    NNReal.coe_mul, NNReal.coe_inv, ← div_eq_mul_inv]
  exact (div_le_one hpos).mpr (hr i j hij).le

/-- Equality of the actual stable-image submodules for any smooth representation. -/
theorem stableImage_blockScalar_eq :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a b : Fin B.length → F.Carrierˣ,
        B.IsStrictlyContracting T a → B.IsStrictlyContracting T b →
        stableImage ρ hρ K hK (B.blockScalar F.Carrier a) =
          stableImage ρ hρ K hK (B.blockScalar F.Carrier b) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ hρ K hK hfac
  let C := fun a => compressedAction ρ hρ K hK (B.blockScalar F.Carrier a)
  have hmul (a b : Fin B.length → F.Carrierˣ)
      (ha : B.IsWeaklyContracting T a) (hb : B.IsWeaklyContracting T b) :
      C (a * b) = C a * C b :=
    blockCompressedAction_mul F T n B V ρ hρ K hK hfac a b ha hb
  have hpow (a : Fin B.length → F.Carrierˣ) (ha : B.IsWeaklyContracting T a)
      (r : ℕ) : C (a ^ r) = C a ^ r := by
    induction r with
    | zero => simp only [pow_zero, C, map_one, compressedAction_one]; rfl
    | succ r hr => rw [pow_succ, hmul _ _ (weak_pow F T B ha r) ha, hr, pow_succ]
  have hle (a b : Fin B.length → F.Carrierˣ)
      (ha : B.IsStrictlyContracting T a) (hb : B.IsStrictlyContracting T b) :
      stableImage ρ hρ K hK (B.blockScalar F.Carrier a) ≤
        stableImage ρ hρ K hK (B.blockScalar F.Carrier b) := by
    intro v hv
    rw [mem_stableImage] at hv ⊢
    intro m
    obtain ⟨r, hc⟩ := exists_weak_quotient F T B a (b ^ m) ha
    obtain ⟨w, hw⟩ := hv r
    refine ⟨C (a ^ r * (b ^ m)⁻¹) w, ?_⟩
    change (C b ^ m) (C (a ^ r * (b ^ m)⁻¹) w) = v
    have heq : b ^ m * (a ^ r * (b ^ m)⁻¹) = a ^ r := by
      rw [mul_left_comm, mul_inv_cancel, mul_one]
    calc
      _ = (C (b ^ m) * C (a ^ r * (b ^ m)⁻¹)) w := by
        rw [hpow b (GeneralLinear.BlockShape.IsStrictlyContracting.weak B T hb) m]
        rfl
      _ = C (a ^ r) w := by
        rw [← hmul _ _ (weak_pow F T B (GeneralLinear.BlockShape.IsStrictlyContracting.weak B T hb) m) hc, heq]
      _ = v := by rw [hpow a (GeneralLinear.BlockShape.IsStrictlyContracting.weak B T ha) r]; exact hw
  intro a b ha hb
  exact le_antisymm (hle a b ha hb) (hle b a hb ha)

/-- The exact published tuple-independence clause, with its full telescope. -/
theorem blockStableImageTupleIndependence (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    BlockStableImageTupleIndependenceClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdmissible
  exact stableImage_blockScalar_eq F T B V ρ hAdmissible.1

end Langlands.Jacquet
