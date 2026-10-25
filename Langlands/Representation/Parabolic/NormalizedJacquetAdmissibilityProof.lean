import Langlands.Representation.Parabolic.NormalizedJacquetStatement
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Representation.Twist.AdmissibilityProof

noncomputable section
open Filter Topology

namespace Langlands.Parabolic

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The existing quotient comparison intertwines the actual product and embedded
Levi actions. -/
theorem jacquetModuleEquiv_leviCoinvariants
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : B.Levi F.Carrier) (v : B.JacquetModule ρ) :
    B.jacquetModuleEquiv ρ (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype) m v) =
      Jacquet.action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
        (B.leviEquiv F.Carrier m) (B.jacquetModuleEquiv ρ v) := by
  obtain ⟨w, rfl⟩ := B.jacquetMk_surjective ρ v
  rfl

/-- Smoothness of the actual untwisted product-Levi quotient. -/
theorem isSmooth_leviCoinvariants :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsSmooth ρ →
      IsSmooth (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)) := by
  let := T.topology
  intro ρ hρ v
  obtain ⟨w, rfl⟩ := B.jacquetMk_surjective ρ v
  obtain ⟨K, hK⟩ := hρ w
  refine ⟨K.comap (T.blockLeviEmbedding B).toMonoidHom (T.blockLeviEmbedding B).continuous, ?_⟩
  intro m
  change B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m.val) w) = B.jacquetMk ρ w
  exact congrArg (B.jacquetMk ρ) (hK ⟨_, m.property⟩)

omit V [AddCommGroup V] [Module ℂ V] in
/-- A small ambient Iwahori subgroup has Levi intersection inside any prescribed
open subgroup of the product Levi. -/
theorem exists_iwahori_levi_subset :
    letI := T.topology
    ∀ L : OpenSubgroup (B.Levi F.Carrier),
      ∃ K : OpenSubgroup (GeneralLinear n F.Carrier),
        IsCompact (K : Set (GeneralLinear n F.Carrier)) ∧
        B.HasBlockIwahoriFactorization T K ∧
        ∀ m : B.leviSubgroup F.Carrier, (m : GeneralLinear n F.Carrier) ∈ K →
          (B.leviEquiv F.Carrier).symm m ∈ L := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro L
  have hL : ((B.leviEquiv F.Carrier).symm ⁻¹' (L : Set (B.Levi F.Carrier))) ∈
      𝓝 (1 : B.leviSubgroup F.Carrier) :=
    ((L.isOpen.preimage (B.leviEquivContinuous F.Carrier).symm.continuous).mem_nhds
      (by simp))
  rw [nhds_subtype_eq_comap] at hL
  obtain ⟨U, hU, hUL⟩ := mem_comap.mp hL
  obtain ⟨K, hK, hKU, hfac⟩ := B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T hU
  exact ⟨K, hK, hfac, fun m hm => hUL (hKU hm)⟩

/-- Admissibility of the actual untwisted product-Levi quotient. -/
theorem isAdmissible_leviCoinvariants :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ
  refine ⟨isSmooth_leviCoinvariants F T B V ρ hρ.1, ?_⟩
  intro L
  obtain ⟨K, hK, hfac, hKL⟩ := exists_iwahori_levi_subset F T B L
  obtain ⟨a, ha⟩ := B.deepChamberNonempty T 1 zero_lt_one
  have has : B.IsStrictlyContracting T a := ha
  let : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let σ := Jacquet.action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
  let J := K.toSubgroup.comap (B.leviSubgroup F.Carrier).subtype
  let f := Jacquet.stableImageJacquetMap ρ hρ.1 K hK (B.blockScalar F.Carrier a)
    (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
  have hf : Function.Bijective f :=
    Jacquet.blockStableImageJacquetBijective F T B V ρ hρ K hK hfac a has
  let : FiniteDimensional ℂ (fixedVectors σ J) :=
    Module.Finite.of_surjective f hf.2
  let E := B.jacquetModuleEquiv ρ
  let g : fixedVectors (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype))
      L.toSubgroup →ₗ[ℂ] fixedVectors σ J :=
    ((E.toLinearMap.comp (fixedVectors
      (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)) L.toSubgroup).subtype)).codRestrict
      (fixedVectors σ J) (by
        intro v m
        have hm := hKL m.val m.property
        have hv := v.property ⟨(B.leviEquiv F.Carrier).symm m.val, hm⟩
        have h := congrArg E hv
        change B.jacquetModuleEquiv ρ
          (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)
            ((B.leviEquiv F.Carrier).symm m.val) v.val) = E v.val at h
        rw [jacquetModuleEquiv_leviCoinvariants, MulEquiv.apply_symm_apply] at h
        exact h)
  apply Module.Finite.of_injective g
  intro v w h
  apply Subtype.ext
  apply E.injective
  exact congrArg Subtype.val h

/-- The complete published clause, with independent field and carrier universes. -/
theorem normalizedJacquetAdmissibility :
    NormalizedJacquetAdmissibilityClause F T B V := by
  let := T.topology
  intro ρ hρ
  apply (isAdmissible_twist_iff _ _
    (Jacquet.isOpen_ker_inverseHalfCharacter (T.leviModulus B)
      (T.isOpen_ker_leviModulus B))).mpr
  exact isAdmissible_leviCoinvariants F T B V ρ hρ

end Langlands.Parabolic
