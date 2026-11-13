import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.AllField.Representation.Jacquet.Parabolic
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement
noncomputable section
open Filter Topology

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding NormalizedJacquetAdmissibilityClause exists_iwahori_levi_subset isAdmissible_leviCoinvariants isSmooth_leviCoinvariants jacquetModuleEquiv_leviCoinvariants normalizedJacquetAdmissibility
open Langlands.AllField.Parabolic

universe uF uV
variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The existing quotient comparison intertwines the actual product and embedded
Levi actions. -/
theorem jacquetModuleEquiv_leviCoinvariants
    (ρ : Representation ℂ (GeneralLinear n F) V)
    (m : B.Levi F) (v : B.JacquetModule ρ) :
    B.jacquetModuleEquiv ρ (leviCoinvariants B (ρ.comp (B.parabolic F).subtype) m v) =
      Jacquet.action ρ (B.unipotentSubgroup F) (B.leviSubgroup F)
        (B.leviSubgroup_le_normalizer_unipotentSubgroup F)
        (B.leviEquiv F m) (B.jacquetModuleEquiv ρ v) := by
  obtain ⟨w, rfl⟩ := B.jacquetMk_surjective ρ v
  rfl

/-- Smoothness of the actual untwisted product-Levi quotient. -/
theorem isSmooth_leviCoinvariants :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F) V), IsSmooth ρ →
      IsSmooth (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)) := by
  let := T.topology
  intro ρ hρ v
  obtain ⟨w, rfl⟩ := B.jacquetMk_surjective ρ v
  obtain ⟨K, hK⟩ := hρ w
  refine ⟨K.comap (T.blockLeviEmbedding B).toMonoidHom (T.blockLeviEmbedding B).continuous, ?_⟩
  intro m
  change B.jacquetMk ρ (ρ (B.leviEmbedding F m.val) w) = B.jacquetMk ρ w
  exact congrArg (B.jacquetMk ρ) (hK ⟨_, m.property⟩)

omit V [AddCommGroup V] [Module ℂ V] in
/-- A small ambient Iwahori subgroup has Levi intersection inside any prescribed
open subgroup of the product Levi. -/
theorem exists_iwahori_levi_subset :
    letI := T.topology
    ∀ L : OpenSubgroup (B.Levi F),
      ∃ K : OpenSubgroup (GeneralLinear n F),
        IsCompact (K : Set (GeneralLinear n F)) ∧
        (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K ∧
        ∀ m : B.leviSubgroup F, (m : GeneralLinear n F) ∈ K →
          (B.leviEquiv F).symm m ∈ L := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro L
  have hL : ((B.leviEquiv F).symm ⁻¹' (L : Set (B.Levi F))) ∈
      𝓝 (1 : B.leviSubgroup F) :=
    ((L.isOpen.preimage (B.leviEquivContinuous F).symm.continuous).mem_nhds
      (by simp))
  rw [nhds_subtype_eq_comap] at hL
  obtain ⟨U, hU, hUL⟩ := mem_comap.mp hL
  obtain ⟨K, hK, hKU, hfac⟩ := (Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization B) T hU
  exact ⟨K, hK, hfac, fun m hm => hUL (hKU hm)⟩

/-- Admissibility of the actual untwisted product-Levi quotient. -/
theorem isAdmissible_leviCoinvariants :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F) V), IsAdmissible ρ →
      IsAdmissible (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ
  refine ⟨isSmooth_leviCoinvariants F T B V ρ hρ.1, ?_⟩
  intro L
  obtain ⟨K, hK, hfac, hKL⟩ := exists_iwahori_levi_subset F T B L
  obtain ⟨a, ha⟩ := (Langlands.AllField.GeneralLinear.BlockShape.deepChamberNonempty B) T 1 zero_lt_one
  have has : (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a := ha
  let : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let σ := Jacquet.action ρ (B.unipotentSubgroup F) (B.leviSubgroup F)
    (B.leviSubgroup_le_normalizer_unipotentSubgroup F)
  let J := K.toSubgroup.comap (B.leviSubgroup F).subtype
  let f := Jacquet.stableImageJacquetMap ρ hρ.1 K hK (B.blockScalar F a)
    (B.unipotentSubgroup F) (B.leviSubgroup F)
    (B.leviSubgroup_le_normalizer_unipotentSubgroup F)
  have hf : Function.Bijective f :=
    Langlands.AllField.Jacquet.blockStableImageJacquetBijective F T B V ρ hρ K hK hfac a has
  let : FiniteDimensional ℂ (fixedVectors σ J) :=
    Module.Finite.of_surjective f hf.2
  let E := B.jacquetModuleEquiv ρ
  let g : fixedVectors (leviCoinvariants B (ρ.comp (B.parabolic F).subtype))
      L.toSubgroup →ₗ[ℂ] fixedVectors σ J :=
    ((E.toLinearMap.comp (fixedVectors
      (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)) L.toSubgroup).subtype)).codRestrict
      (fixedVectors σ J) (by
        intro v m
        have hm := hKL m.val m.property
        have hv := v.property ⟨(B.leviEquiv F).symm m.val, hm⟩
        have h := congrArg E hv
        change B.jacquetModuleEquiv ρ
          (leviCoinvariants B (ρ.comp (B.parabolic F).subtype)
            ((B.leviEquiv F).symm m.val) v.val) = E v.val at h
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

end Langlands.AllField.Parabolic
