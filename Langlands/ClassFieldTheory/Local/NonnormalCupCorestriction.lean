import Langlands.ClassFieldTheory.Local.NormExistenceFiniteCorrespondence
import Langlands.ClassFieldTheory.Local.ClassFormationTransferLawsProof
import Mathlib.RingTheory.Norm.Transitivity

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

section Embeddings

variable [Normal K M]

/-- Restrict a top-field automorphism and embed its values in an algebraic closure. -/
def relativeGaloisEmbedding (σ : Gal(M/K)) : L →ₐ[K] AlgebraicClosure M :=
  ((Normal.algHomEquivAut K (AlgebraicClosure M) M).symm σ).domRestrict L

theorem relativeGaloisEmbedding_eq_iff (σ τ : Gal(M/K)) :
    relativeGaloisEmbedding K L M σ = relativeGaloisEmbedding K L M τ ↔
      σ⁻¹ * τ ∈ relativeGaloisSubgroup K L M := by
  constructor
  · intro h
    have hfix (x : L) : (σ⁻¹ * τ) (algebraMap L M x) = algebraMap L M x := by
      have hx := AlgHom.congr_fun h x
      change algebraMap M (AlgebraicClosure M) (σ (algebraMap L M x)) =
        algebraMap M (AlgebraicClosure M) (τ (algebraMap L M x)) at hx
      have hx' := (algebraMap M (AlgebraicClosure M)).injective hx
      change σ.symm (τ (algebraMap L M x)) = _
      rw [← hx', σ.symm_apply_apply]
    exact ⟨{ toRingEquiv := (σ⁻¹ * τ).toRingEquiv, commutes' := hfix }, rfl⟩
  · rintro ⟨ρ, hρ⟩
    ext x
    have hfix : (σ⁻¹ * τ) (algebraMap L M x) = algebraMap L M x := by
      rw [← hρ]
      exact ρ.commutes x
    have hx : τ (algebraMap L M x) = σ (algebraMap L M x) := by
      apply σ.symm.injective
      exact hfix.trans (σ.symm_apply_apply _).symm
    exact congrArg (algebraMap M (AlgebraicClosure M)) hx.symm

variable [FiniteDimensional L M]

/-- Left cosets of automorphisms over the middle field are its embeddings
in an algebraic closure, without normality of the middle field. -/
def relativeGaloisCosetEmbeddingEquiv :
    Gal(M/K) ⧸ relativeGaloisSubgroup K L M ≃ (L →ₐ[K] AlgebraicClosure M) := by
  let f : Gal(M/K) ⧸ relativeGaloisSubgroup K L M →
      (L →ₐ[K] AlgebraicClosure M) :=
    Quotient.lift (relativeGaloisEmbedding K L M) (fun σ τ h =>
      (relativeGaloisEmbedding_eq_iff K L M σ τ).mpr (QuotientGroup.leftRel_apply.mp h))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q q'
    refine Quotient.inductionOn₂ q q' ?_
    intro σ τ h
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr
      ((relativeGaloisEmbedding_eq_iff K L M σ τ).mp h)
  · intro ψ
    obtain ⟨φ, hφ⟩ :=
      IsAlgClosed.surjective_domRestrict_of_isAlgebraic (E := M) ψ
    refine ⟨QuotientGroup.mk ((Normal.algHomEquivAut K (AlgebraicClosure M) M) φ), ?_⟩
    change (((Normal.algHomEquivAut K (AlgebraicClosure M) M).symm
      ((Normal.algHomEquivAut K (AlgebraicClosure M) M) φ)).domRestrict L) = ψ
    rw [Equiv.symm_apply_apply]
    exact hφ

theorem relativeGaloisCosetEmbeddingEquiv_mk (σ : Gal(M/K)) :
    relativeGaloisCosetEmbeddingEquiv K L M (QuotientGroup.mk σ) =
      relativeGaloisEmbedding K L M σ := rfl

end Embeddings

variable [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K M] [IsGalois L M]

omit [IsGalois L M] in
/-- The coset sum on middle-field units is the actual determinant norm
even when the middle extension is not normal. -/
theorem relativeCosetNorm_baseUnit_nonnormal (a : Lˣ) :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
    Langlands.Tate.cosetNorm (relativeGaloisSubgroup K L M)
      (unitsRepresentation K M)
      (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) =
        baseUnitsToInvariants K M
          (Additive.ofMul (Langlands.LocalClassField.normUnits K L a)) := by
  classical
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  apply Subtype.ext
  apply (@Additive.toMul Mˣ).injective
  apply Units.ext
  apply (algebraMap M (AlgebraicClosure M)).injective
  change algebraMap M (AlgebraicClosure M)
    ((@Additive.toMul Mˣ (∑ q : Gal(M/K) ⧸ relativeGaloisSubgroup K L M,
      Langlands.Tate.cosetAction (relativeGaloisSubgroup K L M)
        (unitsRepresentation K M)
        (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) q)) : M) = _
  rw [toMul_sum, Units.coe_prod, map_prod]
  have hterm (q : Gal(M/K) ⧸ relativeGaloisSubgroup K L M) :
      algebraMap M (AlgebraicClosure M)
        ((@Additive.toMul Mˣ (Langlands.Tate.cosetAction (relativeGaloisSubgroup K L M)
          (unitsRepresentation K M)
          (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) q)) : M) =
        relativeGaloisCosetEmbeddingEquiv K L M q (a : L) := by
    induction q using QuotientGroup.induction_on with
    | H σ => rfl
  simp_rw [hterm]
  rw [Equiv.prod_comp (relativeGaloisCosetEmbeddingEquiv K L M)
    (fun ψ : L →ₐ[K] AlgebraicClosure M => ψ (a : L))]
  rw [← Algebra.norm_eq_prod_embeddings K (AlgebraicClosure M) (a : L)]
  exact (IsScalarTower.algebraMap_apply K M (AlgebraicClosure M) _).symm

omit [IsGalois L M] in
/-- Relative Tate corestriction takes a unit class to its field norm
without a normality assumption on the middle field. -/
theorem relativeTateCorestriction_zeroClass_nonnormal (a : Lˣ) :
    letI := Fintype.ofFinite Gal(M/L)
    letI := Fintype.ofFinite Gal(M/K)
    relativeTateCorestriction K L M 0
      (Langlands.Tate.zeroClass (unitsRepresentation L M)
        (baseUnitsToInvariants L M (Additive.ofMul a))) =
      Langlands.Tate.zeroClass (unitsRepresentation K M)
        (baseUnitsToInvariants K M
          (Additive.ofMul (Langlands.LocalClassField.normUnits K L a))) := by
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  change Langlands.Tate.corestrictionZero (relativeGaloisSubgroup K L M)
    (unitsRepresentation K M)
    ((relativeSubgroupTateIso K L M 0).hom
      (Langlands.Tate.zeroClass (unitsRepresentation L M)
        (baseUnitsToInvariants L M (Additive.ofMul a)))) = _
  rw [relativeSubgroupTateIso_zeroClass, Langlands.Tate.corestrictionZero_zeroClass,
    relativeCosetNorm_baseUnit_nonnormal]

/-- Degree-zero corestriction becomes the actual quotient norm for an
arbitrary finite middle field. -/
theorem tateZeroEquivNormQuotient_corestriction_nonnormal
    (x : relativeTateCohomology L M 0) :
    tateZeroEquivNormQuotient K M (relativeTateCorestriction K L M 0 x) =
      (Langlands.LocalClassField.normQuotientTowerNorm K L M).toAdditive
        (tateZeroEquivNormQuotient L M x) := by
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite Gal(M/K)
  obtain ⟨a, rfl⟩ := Langlands.Tate.zeroClass_surjective (unitsRepresentation L M) x
  obtain ⟨b, rfl⟩ := baseUnitsToInvariants_surjective L M a
  change tateZeroEquivNormQuotient K M
    (relativeTateCorestriction K L M 0
      (Langlands.Tate.zeroClass (unitsRepresentation L M)
        (baseUnitsToInvariants L M (Additive.ofMul b.toMul)))) =
    (Langlands.LocalClassField.normQuotientTowerNorm K L M).toAdditive
      (tateZeroEquivNormQuotient L M
        (Langlands.Tate.zeroClass (unitsRepresentation L M)
          (baseUnitsToInvariants L M (Additive.ofMul b.toMul))))
  rw [relativeTateCorestriction_zeroClass_nonnormal, tateZeroEquivNormQuotient_zeroClass,
    tateZeroEquivNormQuotient_zeroClass]
  rfl

/-- The actual abelianization cup intertwines inclusion and norm in
arbitrary finite towers with Galois upper extensions. -/
theorem abelianizationCupToNormQuotient_corestriction_nonnormal
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers)
    (invLM : relativeCohomology L M 2 →+ RationalModIntegers)
    (hcores : FundamentalClassTateCorestriction K L M invKM invLM)
    (c : relativeCohomology K M 2) (d : relativeCohomology L M 2)
    (hc : IsFundamentalClass K M invKM c) (hd : IsFundamentalClass L M invLM d)
    (x : Additive (Abelianization Gal(M/L))) :
    abelianizationCupToNormQuotient K M c (relativeAbelianizationInclusion K L M x) =
      (Langlands.LocalClassField.normQuotientTowerNorm K L M).toAdditive
        (abelianizationCupToNormQuotient L M d x) := by
  obtain ⟨y, rfl⟩ := (integralTateMinusTwoEquiv L M).surjective x
  rw [← integralTateMinusTwoEquiv_corestriction,
    abelianizationCupToNormQuotient_comparison,
    abelianizationCupToNormQuotient_comparison]
  change tateZeroEquivNormQuotient K M
    (relativeTateCup K M (-2) c (integralTateCorestriction K L M (-2) y)) = _
  rw [← hcores c d hc hd (-2) y]
  change tateZeroEquivNormQuotient K M
    (relativeTateCorestriction K L M 0 (relativeTateCup L M (-2) d y)) = _
  rw [tateZeroEquivNormQuotient_corestriction_nonnormal]
  rfl

end Langlands.ClassFieldTheory.Local
