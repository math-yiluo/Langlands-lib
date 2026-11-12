import Langlands.Representation.Exponents.CoefficientExtractionStatement
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.Representation.Jacquet.StableImageTupleIndependenceProof
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Group.GL.BlockIwahoriBasis

/-! # Exact coefficient extraction by common stable Jacquet lifts -/

noncomputable section

namespace Langlands

open Filter Topology
open scoped NNReal

universe uF uV

/-- A generalized normalized upper Jacquet exponent is one exact smooth
coefficient throughout the strict block-scalar chamber. -/
theorem glJacquetExponentCoefficientExtraction :
    GLJacquetExponentCoefficientExtractionStatement.{uF, uV} := by
  intro p _ F T n hn V _ _ ρ
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro hρ B χ hχ
  obtain ⟨w, hw, heig⟩ :=
    glJacquetExponentEigenvector p F T n hn V ρ hρ B χ hχ
  obtain ⟨v₀, hv₀⟩ := B.jacquetMk_surjective ρ w
  obtain ⟨U, hU⟩ := hρ.1 v₀
  obtain ⟨K, hK, hKU, hfac⟩ :=
    B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T
      (U.isOpen.mem_nhds U.one_mem)
  have hvK : v₀ ∈ fixedVectors ρ K.toSubgroup := by
    intro k
    exact hU ⟨k.val, hKU k.property⟩
  let N := B.unipotentSubgroup F.Carrier
  let M := B.leviSubgroup F.Carrier
  let hMN := B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier
  let A := Jacquet.action ρ N M hMN
  let W := Jacquet.fixedJacquetMap ρ N M hMN K.toSubgroup ⟨v₀, hvK⟩
  have hW : (W : Jacquet.Coinvariants ρ N) = B.jacquetModuleEquiv ρ w := by
    change Jacquet.mk ρ N v₀ = B.jacquetModuleEquiv ρ w
    rw [← B.jacquetModuleEquiv_mk, hv₀]
  have hW0 : (W : Jacquet.Coinvariants ρ N) ≠ 0 := by
    rw [hW]
    intro hz
    apply hw
    exact (B.jacquetModuleEquiv ρ).injective (hz.trans (map_zero _).symm)
  let μ := fun a : Fin B.length → F.Carrierˣ =>
    (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) * (χ a : ℂ)
  have hWeig (a : Fin B.length → F.Carrierˣ) :
      A (B.blockScalarInLevi F.Carrier a) (W : Jacquet.Coinvariants ρ N) =
        μ a • (W : Jacquet.Coinvariants ρ N) := by
    have h := heig a
    change T.normalizedJacquet B ρ (B.blockScalarLevi F.Carrier a) w =
      (χ a : ℂ) • w at h
    rw [← hv₀, T.normalizedJacquet_mk_eq_inv_halfModulus] at h
    have h' := congrArg (B.jacquetModuleEquiv ρ) h
    simp only [map_smul, B.jacquetModuleEquiv_mk, Units.smul_def,
      Units.val_inv_eq_inv_val] at h'
    have h'' := congrArg
      (fun z => (T.leviHalfModulus B (B.blockScalarLevi F.Carrier a) : ℂ) • z) h'
    simp only [smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul] at h''
    change Jacquet.mk ρ N
        (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a)) v₀) =
      μ a • Jacquet.mk ρ N v₀ at h''
    exact (Jacquet.action_mk ρ N M hMN _ v₀).trans h''
  obtain ⟨c, hc⟩ := B.deepChamberNonempty T 1 zero_lt_one
  have hc' : B.IsStrictlyContracting T c := hc
  obtain ⟨x, hx⟩ :=
    (Jacquet.stableImageJacquetMap_bijective_of_finiteDimensional F T B V
      ρ hρ.1 K hK (hρ.2 K) hfac c hc').2 W
  have hxq : Jacquet.mk ρ N ((x : fixedVectors ρ K.toSubgroup) : V) =
      (W : Jacquet.Coinvariants ρ N) := congrArg Subtype.val hx
  have hx0 : (x : fixedVectors ρ K.toSubgroup) ≠ 0 := by
    intro hx0
    apply hW0
    rw [← hxq, hx0]
    exact map_zero _
  have hxeig (a : Fin B.length → F.Carrierˣ)
      (ha : B.IsStrictlyContracting T a) :
      Jacquet.compressedAction ρ hρ.1 K hK (B.blockScalar F.Carrier a)
        (x : fixedVectors ρ K.toSubgroup) =
      μ a • (x : fixedVectors ρ K.toSubgroup) := by
    have hxa : (x : fixedVectors ρ K.toSubgroup) ∈
        Jacquet.stableImage ρ hρ.1 K hK (B.blockScalar F.Carrier a) := by
      rw [← Jacquet.stableImage_blockScalar_eq F T B V ρ hρ.1 K hK hfac c a hc' ha]
      exact x.property
    let xa : Jacquet.stableImage ρ hρ.1 K hK (B.blockScalar F.Carrier a) :=
      ⟨x, hxa⟩
    have heq : Jacquet.stableImageAction ρ hρ.1 K hK (B.blockScalar F.Carrier a) xa =
        μ a • xa := by
      apply (Jacquet.stableImageJacquetMap_bijective_of_finiteDimensional F T B V
        ρ hρ.1 K hK (hρ.2 K) hfac a ha).1
      apply Subtype.ext
      change Jacquet.mk ρ N
          (Jacquet.compressedAction ρ hρ.1 K hK (B.blockScalar F.Carrier a)
            (x : fixedVectors ρ K.toSubgroup) : V) =
        μ a • Jacquet.mk ρ N ((x : fixedVectors ρ K.toSubgroup) : V)
      rw [Jacquet.blockCompressedAction_mk F T n B V ρ hρ.1 K hK hfac a ha.weak,
        hxq, hWeig]
    exact congrArg Subtype.val heq
  obtain ⟨φ₀, hφ₀⟩ :
      ∃ φ₀ : Module.Dual ℂ (fixedVectors ρ K.toSubgroup), φ₀ x ≠ 0 := by
    simpa using mt (Module.forall_dual_apply_eq_zero_iff ℂ
      (x : fixedVectors ρ K.toSubgroup)).mp hx0
  let φ : Module.Dual ℂ (fixedVectors ρ K.toSubgroup) := (φ₀ x)⁻¹ • φ₀
  have hφ : φ x = 1 := inv_mul_cancel₀ hφ₀
  obtain ⟨ℓ, hℓ⟩ := (smoothDualFixedRestriction_bijective ρ hρ.1 K hK).2 φ
  have hℓx : ℓ.val.val ((x : fixedVectors ρ K.toSubgroup) : V) = 1 := by
    exact (congrArg (fun f => f (x : fixedVectors ρ K.toSubgroup)) hℓ).trans hφ
  have hℓK (k : K) (y : V) : ℓ.val.val (ρ k.val y) = ℓ.val.val y := by
    have h := congrArg (fun f : SmoothDual ρ => f.val y) (ℓ.property k⁻¹)
    change ℓ.val.val (ρ (k.val⁻¹)⁻¹ y) = ℓ.val.val y at h
    simpa only [inv_inv] using h
  have havg (y : V) :
      ℓ.val.val (Compact.averageMap ρ hρ.1 K hK y) = ℓ.val.val y :=
    Jacquet.map_averageMap_of_forall_eq ρ hρ.1 K hK ℓ.val.val y _ (fun k => hℓK k y)
  refine ⟨((x : fixedVectors ρ K.toSubgroup) : V), ℓ.val, 1, zero_lt_one, le_rfl, ?_⟩
  intro a ha
  have ha' : B.IsStrictlyContracting T a := by
    intro i j hij
    simpa only [GeneralLinear.BlockShape.blockScalarRatio_apply, T.normalizedAbsUnits_coe,
      Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv] using ha i j hij
  calc
    ℓ.val.val (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier a))
        ((x : fixedVectors ρ K.toSubgroup) : V)) =
        ℓ.val.val (Jacquet.compressedAction ρ hρ.1 K hK (B.blockScalar F.Carrier a)
          (x : fixedVectors ρ K.toSubgroup) : V) := (havg _).symm
    _ = μ a := by rw [hxeig a ha', Submodule.coe_smul, map_smul, hℓx, smul_eq_mul, mul_one]

end Langlands
