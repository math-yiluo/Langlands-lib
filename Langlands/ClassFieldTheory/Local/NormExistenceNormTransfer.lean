import Langlands.ClassFieldTheory.Local.NormExistenceTransfers
import Langlands.ClassFieldTheory.Local.TateNormQuotient
import Langlands.Cohomology.Tate.ZeroProof

/-! # Degree-zero corestriction and the actual determinant norm -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- Middle-field units are invariant under automorphisms over the middle field. -/
def relativeBaseUnitsToInvariants :
    Additive Lˣ →+ (Rep.res (relativeGaloisSubgroup K L M).subtype
      (unitsRepresentation K M)).ρ.invariants :=
  (Langlands.Tate.reindexInvariants (relativeGaloisSubgroupEquiv K L M)
    (relativeSubgroupUnitsIso K L M).hom).toAddMonoidHom.comp
      (baseUnitsToInvariants L M)

lemma relativeGaloisCosetEquiv_mk [Normal K L] [Normal K M] (σ : Gal(M/K)) :
    relativeGaloisCosetEquiv K L M (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormal σ L := rfl

lemma relativeCosetAction_baseUnit [Normal K L] [Normal K M]
    (a : Lˣ) (q : Gal(M/K) ⧸ relativeGaloisSubgroup K L M) :
    Langlands.Tate.cosetAction (relativeGaloisSubgroup K L M)
      (unitsRepresentation K M)
      (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) q =
        baseUnit L M ((relativeGaloisCosetEquiv K L M q) • a) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply Units.ext
    exact (AlgEquiv.restrictNormal_commutes σ L (a : L)).symm

variable [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K L] [IsGalois K M] [IsGalois L M]

omit [FiniteDimensional L M] [IsGalois L M] in
/-- The coset sum on middle-field units is the embedded determinant norm. -/
lemma relativeCosetNorm_baseUnit (a : Lˣ) :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
    Langlands.Tate.cosetNorm (relativeGaloisSubgroup K L M)
      (unitsRepresentation K M)
      (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) =
        baseUnitsToInvariants K M
          (Additive.ofMul (Langlands.LocalClassField.normUnits K L a)) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(L/K)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  apply Subtype.ext
  change (∑ q : Gal(M/K) ⧸ relativeGaloisSubgroup K L M,
    Langlands.Tate.cosetAction (relativeGaloisSubgroup K L M)
      (unitsRepresentation K M)
      (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) q) = _
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun q _ => relativeCosetAction_baseUnit K L M a q)
  rw [hsum]
  change (∑ q : Gal(M/K) ⧸ relativeGaloisSubgroup K L M,
    (baseUnit L M ((relativeGaloisCosetEquiv K L M q) • a) : Additive Mˣ)) = _
  erw [Equiv.sum_comp (relativeGaloisCosetEquiv K L M).toEquiv
    (fun σ : Gal(L/K) => (baseUnit L M (σ • a) : Additive Mˣ))]
  have h := congrArg
    (fun b : Additive Lˣ => (Units.map (algebraMap L M).toMonoidHom).toAdditive b)
    (unitsRepresentation_norm K L a)
  simp only [Representation.norm, LinearMap.sum_apply] at h
  change unitInclusion L M (∑ σ : Gal(L/K), Additive.ofMul (σ • a)) =
    unitInclusion L M
      (baseUnit K L (Langlands.LocalClassField.normUnits K L a)) at h
  rw [map_sum] at h
  refine h.trans ?_
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K L M (Algebra.norm K (a : L))).symm

omit [FiniteDimensional K L] [IsGalois K L] [IsGalois K M] [IsGalois L M] in
/-- Reindexing the degree-zero class preserves the actual middle-field unit. -/
lemma relativeSubgroupTateIso_zeroClass (a : Lˣ) :
    letI := Fintype.ofFinite Gal(M/L)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    (relativeSubgroupTateIso K L M 0).hom
      (Langlands.Tate.zeroClass (unitsRepresentation L M)
        (baseUnitsToInvariants L M (Additive.ofMul a))) =
      Langlands.Tate.zeroClass
        (Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M))
        (relativeBaseUnitsToInvariants K L M (Additive.ofMul a)) := by
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  exact Langlands.Tate.reindex_zeroClass (relativeGaloisSubgroupEquiv K L M)
    (relativeSubgroupUnitsIso K L M).hom _

omit [IsGalois L M] in
/-- Relative Tate corestriction sends a base-unit class to its determinant norm. -/
lemma relativeTateCorestriction_zeroClass (a : Lˣ) :
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
    relativeCosetNorm_baseUnit]

/-- The degree-zero Tate comparison commutes with the actual tower norm map. -/
lemma tateZeroEquivNormQuotient_corestriction (x : relativeTateCohomology L M 0) :
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
  rw [relativeTateCorestriction_zeroClass, tateZeroEquivNormQuotient_zeroClass,
    tateZeroEquivNormQuotient_zeroClass]
  rfl

end Langlands.ClassFieldTheory.Local
