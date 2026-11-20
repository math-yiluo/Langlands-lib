import Langlands.Representation.Jacquet.CanonicalLiftCompatibilityStatement
import Langlands.Representation.Jacquet.StableImageAverageBridgeProof
import Langlands.Representation.Jacquet.StableImageTupleIndependenceProof
import Langlands.Representation.Jacquet.BlockPowerKernelProof
import Langlands.Representation.Jacquet.CompressionStabilizationProof

/-! # Nested averaging of same-class canonical Jacquet lifts -/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The upper Jacquet quotient is injective on the actual stable image. -/
private theorem stableImage_eq_of_mk_eq :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdm : IsAdmissible ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
      ∀ x y : fixedVectors ρ K.toSubgroup,
        x ∈ stableImage ρ hAdm.1 K hK (B.blockScalar F.Carrier a) →
        y ∈ stableImage ρ hAdm.1 K hK (B.blockScalar F.Carrier a) →
        mk ρ (B.unipotentSubgroup F.Carrier) x.val =
          mk ρ (B.unipotentSubgroup F.Carrier) y.val → x = y := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdm K hK hfac a ha x y hx hy hq
  have hsplit := powerKernelSup_isCompl_stableImage ρ hAdm.1 K hK
    (B.blockScalar F.Carrier a) (hAdm.2 K)
  have hker : x - y ∈ powerKernelSup ρ hAdm.1 K hK (B.blockScalar F.Carrier a) := by
    rw [blockPowerKernel_eq_jacquetKernel F T B V ρ hAdm.1 K hK hfac a ha,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    apply Subtype.ext
    exact hq
  have hstable := (stableImage ρ hAdm.1 K hK (B.blockScalar F.Carrier a)).sub_mem hx hy
  have hz := hsplit.disjoint.le_bot ⟨hker, hstable⟩
  exact sub_eq_zero.mp (by simpa only [Submodule.mem_bot] using hz)

/-- For a common strictly contracting tuple, normalized averaging over `K0`
recovers the supplied `K0` stable vector with the same upper Jacquet class. -/
theorem averageMap_eq_of_stableImage_mk_eq :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdm : IsAdmissible ρ)
      (K1 K0 : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK1 : IsCompact (K1 : Set (GeneralLinear n F.Carrier)))
      (hK0 : IsCompact (K0 : Set (GeneralLinear n F.Carrier))),
      K1 ≤ K0 →
      B.HasBlockIwahoriFactorization T K1 →
      B.HasBlockIwahoriFactorization T K0 →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
      ∀ (w1 : stableImage ρ hAdm.1 K1 hK1 (B.blockScalar F.Carrier a))
        (w0 : stableImage ρ hAdm.1 K0 hK0 (B.blockScalar F.Carrier a)),
        let v1 := stableImageToRepresentation ρ hAdm.1 K1 hK1 (B.blockScalar F.Carrier a) w1
        let v0 := stableImageToRepresentation ρ hAdm.1 K0 hK0 (B.blockScalar F.Carrier a) w0
        mk ρ (B.unipotentSubgroup F.Carrier) v1 =
          mk ρ (B.unipotentSubgroup F.Carrier) v0 →
        Compact.averageMap ρ hAdm.1 K0 hK0 v1 = v0 := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdm K1 K0 hK1 hK0 hle hfac1 hfac0 a ha w1 w0 v1 v0 hq
  obtain ⟨hstable, hclass⟩ :=
    blockStableImageAverageBridge F T B V ρ hAdm.1 K1 K0 hK1 hK0
      hle hfac1 hfac0 a ha w1
  have hqavg := hclass (by
    rw [hq]
    exact (fixedJacquetMap ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
      (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) K0.toSubgroup w0.val).property)
  let avg : fixedVectors ρ K0.toSubgroup :=
    ⟨Compact.averageMap ρ hAdm.1 K0 hK0 v1,
      Compact.averageMap_mem_fixedVectors ρ hAdm.1 K0 hK0 v1⟩
  have heq := stableImage_eq_of_mk_eq F T B V ρ hAdm K0 hK0 hfac0 a ha
    avg w0.val hstable w0.property (hqavg.trans hq)
  exact congrArg Subtype.val heq

/-- Same-class nested averaging for independently chosen strictly contracting tuples. -/
theorem blockStableImageNestedAverage : BlockStableImageNestedAverageClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdm hρ K1 K0 hK1 hK0 hle hfac1 hfac0 a1 a0 ha1 ha0 w1 w0 v1 v0 hq
  have hstable0 :=
    blockStableImageTupleIndependence F T B V ρ hAdm K0 hK0 hfac0 a1 a0 ha1 ha0
  let w0' : stableImage ρ hρ K0 hK0 (B.blockScalar F.Carrier a1) :=
    ⟨w0.val, hstable0.symm ▸ w0.property⟩
  exact averageMap_eq_of_stableImage_mk_eq F T B V ρ hAdm K1 K0 hK1 hK0
    hle hfac1 hfac0 a1 ha1 w1 w0' hq

/-- Tuple independence and same-class nested averaging for the actual stable images. -/
theorem blockCanonicalLiftCompatibility : BlockCanonicalLiftCompatibilityStatement F T B V :=
  ⟨blockStableImageTupleIndependence F T B V, blockStableImageNestedAverage F T B V⟩

end Langlands.Jacquet
