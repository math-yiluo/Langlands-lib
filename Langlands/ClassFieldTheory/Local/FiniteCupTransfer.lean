import Langlands.ClassFieldTheory.Local.NormExistenceNormTransfer
import Langlands.ClassFieldTheory.Local.ClassFormationTransferLawsProof
import Langlands.Cohomology.Tate.AbelianizationRestriction

/-!
# Finite cup reciprocity and transfer over an arbitrary intermediate field
-/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u

set_option backward.isDefEq.respectTransparency false

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M]

/-- Genuine finite-coset transfer, expressed in the actual Galois groups.
The middle field need not be normal over the base. -/
def relativeAbelianizationTransfer :
    Additive (Abelianization Gal(M/K)) →+ Additive (Abelianization Gal(M/L)) := by
  let := Fintype.ofFinite Gal(M/K)
  exact ((Abelianization.map
    (relativeGaloisSubgroupEquiv K L M).symm.toMonoidHom).toAdditive).comp
      (Langlands.Tate.abelianizationTransfer (relativeGaloisSubgroup K L M))

/-- Reindexing the actual degree-minus-two comparison changes only Galois coordinates. -/
lemma integralTateMinusTwoEquiv_reindex (x : integralTateCohomology L M (-2)) :
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    integralTateMinusTwoEquiv L M x =
      (Abelianization.map
        (relativeGaloisSubgroupEquiv K L M).symm.toMonoidHom).toAdditive
        (Langlands.Tate.integralMinusTwoEquiv (relativeGaloisSubgroup K L M)
          ((integralSubgroupTateIso K L M (-2)).hom x)) := by
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  obtain ⟨σ, rfl⟩ := Langlands.Tate.integralMinusTwoClass_surjective x
  rw [integralSubgroupTateIso_minusTwoClass]
  change Langlands.Tate.integralMinusTwoEquiv Gal(M/L)
      (Langlands.Tate.minusTwoClass (Langlands.Tate.integralTrivial Gal(M/L)) σ 1) =
    (Abelianization.map
      (relativeGaloisSubgroupEquiv K L M).symm.toMonoidHom).toAdditive
      (Langlands.Tate.integralMinusTwoEquiv (relativeGaloisSubgroup K L M)
        (Langlands.Tate.minusTwoClass
          (Langlands.Tate.integralTrivial (relativeGaloisSubgroup K L M))
          (relativeGaloisSubgroupEquiv K L M σ) 1))
  rw [Langlands.Tate.integralMinusTwoEquiv_class,
    Langlands.Tate.integralMinusTwoEquiv_class]
  change Additive.ofMul (Abelianization.of σ) =
    Additive.ofMul (Abelianization.of
      ((relativeGaloisSubgroupEquiv K L M).symm (relativeGaloisSubgroupEquiv K L M σ)))
  rw [MulEquiv.symm_apply_apply]

/-- Integral Tate restriction in degree minus two is the actual finite-coset transfer. -/
lemma integralTateMinusTwoEquiv_restriction (x : integralTateCohomology K M (-2)) :
    integralTateMinusTwoEquiv L M (integralTateRestriction K L M (-2) x) =
      relativeAbelianizationTransfer K L M (integralTateMinusTwoEquiv K M x) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  rw [integralTateMinusTwoEquiv_reindex K L M]
  change (Abelianization.map
      (relativeGaloisSubgroupEquiv K L M).symm.toMonoidHom).toAdditive
    (Langlands.Tate.integralMinusTwoEquiv (relativeGaloisSubgroup K L M)
      ((integralSubgroupTateIso K L M (-2)).hom
        ((integralSubgroupTateIso K L M (-2)).inv
          (Langlands.Tate.restriction (relativeGaloisSubgroup K L M)
            (Langlands.Tate.integralTrivial Gal(M/K)) (-2) x)))) = _
  rw [Iso.inv_hom_id_apply, Langlands.Tate.integralMinusTwoEquiv_restriction]
  rfl

/-- Degree-zero Tate restriction sends the class of a base-field unit to its
literal image in the middle field, whether or not that field is normal. -/
lemma relativeTateRestriction_zeroClass (a : Kˣ) :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite Gal(M/L)
    relativeTateRestriction K L M 0
      (Langlands.Tate.zeroClass (unitsRepresentation K M)
        (baseUnitsToInvariants K M (Additive.ofMul a))) =
      Langlands.Tate.zeroClass (unitsRepresentation L M)
        (baseUnitsToInvariants L M
          (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a))) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  apply (relativeSubgroupTateIso K L M 0).toLinearEquiv.injective
  change (relativeSubgroupTateIso K L M 0).hom
    ((relativeSubgroupTateIso K L M 0).inv
      (Langlands.Tate.restriction (relativeGaloisSubgroup K L M)
        (unitsRepresentation K M) 0
        (Langlands.Tate.zeroClass (unitsRepresentation K M)
          (baseUnitsToInvariants K M (Additive.ofMul a))))) =
    (relativeSubgroupTateIso K L M 0).hom
      (Langlands.Tate.zeroClass (unitsRepresentation L M)
        (baseUnitsToInvariants L M
          (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom a))))
  rw [Iso.inv_hom_id_apply, relativeSubgroupTateIso_zeroClass]
  change Langlands.Tate.restrictionZero (relativeGaloisSubgroup K L M)
    (unitsRepresentation K M)
    (Langlands.Tate.zeroClass (unitsRepresentation K M)
      (baseUnitsToInvariants K M (Additive.ofMul a))) = _
  rw [Langlands.Tate.restrictionZero_zeroClass]
  congr 1
  apply Subtype.ext
  apply Units.ext
  exact IsScalarTower.algebraMap_apply K L M (a : K)

variable [IsGalois K M] [IsGalois L M]

/-- Base-field norm units remain norm units after inclusion in an arbitrary
intermediate field of a finite Galois extension. -/
lemma unitsInclusion_mem_normSubgroup {a : Kˣ}
    (ha : a ∈ Langlands.LocalClassField.normSubgroup K M) :
    Units.map (algebraMap K L).toMonoidHom a ∈
      Langlands.LocalClassField.normSubgroup L M := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  have hzero :
      Langlands.Tate.zeroClass (unitsRepresentation K M)
        (baseUnitsToInvariants K M (Additive.ofMul a)) = 0 := by
    apply (tateZeroEquivNormQuotient K M).injective
    rw [tateZeroEquivNormQuotient_zeroClass, map_zero]
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff a).mpr ha)
  have hres := congrArg (relativeTateRestriction K L M 0) hzero
  rw [relativeTateRestriction_zeroClass, map_zero] at hres
  have hnorm := congrArg (tateZeroEquivNormQuotient L M) hres
  rw [tateZeroEquivNormQuotient_zeroClass, map_zero] at hnorm
  exact (QuotientGroup.eq_one_iff _).mp (Additive.ofMul.injective hnorm)

/-- Literal field inclusion descended to the two actual field norm quotients.
Its well-definedness was proved from degree-zero restriction. -/
def normQuotientTowerInclusion :
    Langlands.LocalClassField.NormQuotient K M →*
      Langlands.LocalClassField.NormQuotient L M :=
  QuotientGroup.map _ _ (Units.map (algebraMap K L).toMonoidHom)
    (fun _ ha => unitsInclusion_mem_normSubgroup K L M ha)

@[simp] lemma normQuotientTowerInclusion_projection (a : Kˣ) :
    normQuotientTowerInclusion K L M
      (Langlands.LocalClassField.normQuotientProjection K M a) =
    Langlands.LocalClassField.normQuotientProjection L M
      (Units.map (algebraMap K L).toMonoidHom a) := rfl

/-- The actual degree-zero comparison intertwines Tate restriction and literal
field inclusion on the norm quotients. -/
lemma tateZeroEquivNormQuotient_restriction (x : relativeTateCohomology K M 0) :
    tateZeroEquivNormQuotient L M (relativeTateRestriction K L M 0 x) =
      (normQuotientTowerInclusion K L M).toAdditive
        (tateZeroEquivNormQuotient K M x) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  obtain ⟨a, rfl⟩ := Langlands.Tate.zeroClass_surjective (unitsRepresentation K M) x
  obtain ⟨b, rfl⟩ := baseUnitsToInvariants_surjective K M a
  change tateZeroEquivNormQuotient L M
    (relativeTateRestriction K L M 0
      (Langlands.Tate.zeroClass (unitsRepresentation K M)
        (baseUnitsToInvariants K M (Additive.ofMul b.toMul)))) =
    (normQuotientTowerInclusion K L M).toAdditive
      (tateZeroEquivNormQuotient K M
        (Langlands.Tate.zeroClass (unitsRepresentation K M)
          (baseUnitsToInvariants K M (Additive.ofMul b.toMul))))
  rw [relativeTateRestriction_zeroClass, tateZeroEquivNormQuotient_zeroClass,
    tateZeroEquivNormQuotient_zeroClass]
  rfl

/-- The finite cup map carries genuine group transfer to field inclusion,
when the degree-two class over the middle field is the restricted class. -/
theorem abelianizationCupToNormQuotient_restriction
    (c : relativeCohomology K M 2) (x : Additive (Abelianization Gal(M/K))) :
    abelianizationCupToNormQuotient L M (relativeRestriction K L M 2 c)
        (relativeAbelianizationTransfer K L M x) =
      (normQuotientTowerInclusion K L M).toAdditive
        (abelianizationCupToNormQuotient K M c x) := by
  obtain ⟨y, rfl⟩ := (integralTateMinusTwoEquiv K M).surjective x
  rw [← integralTateMinusTwoEquiv_restriction,
    abelianizationCupToNormQuotient_comparison,
    abelianizationCupToNormQuotient_comparison]
  change tateZeroEquivNormQuotient L M
    (relativeTateCup L M (-2) (relativeRestriction K L M 2 c)
      (integralTateRestriction K L M (-2) y)) = _
  rw [← relativeTateRestriction_relativeTateCup]
  exact tateZeroEquivNormQuotient_restriction K L M _

/-- Multiplicative form of the actual finite-coset transfer. -/
def relativeGaloisAbelianTransfer :
    Abelianization Gal(M/K) →* Abelianization Gal(M/L) :=
  (relativeAbelianizationTransfer K L M).toMultiplicative

set_option maxRecDepth 2048 in
/-- The constructed cup equivalences satisfy the actual finite transfer square. -/
theorem abelianizationCupEquiv_restriction (c : relativeCohomology K M 2)
    (hc : Function.Bijective (relativeTateCup K M (-2) c))
    (hd : Function.Bijective
      (relativeTateCup L M (-2) (relativeRestriction K L M 2 c)))
    (x : Abelianization Gal(M/K)) :
    abelianizationCupEquiv L M (relativeRestriction K L M 2 c) hd
        (relativeGaloisAbelianTransfer K L M x) =
      normQuotientTowerInclusion K L M (abelianizationCupEquiv K M c hc x) := by
  exact congrArg Additive.toMul
    (abelianizationCupToNormQuotient_restriction K L M c (Additive.ofMul x))

set_option maxRecDepth 2048 in
/-- Arithmetic inverse-cup reciprocity carries field inclusion to actual transfer.
The bijectivity certificates remain explicit; no local existence is assumed. -/
theorem arithmeticReciprocityOfCup_restriction (c : relativeCohomology K M 2)
    (hc : Function.Bijective (relativeTateCup K M (-2) c))
    (hd : Function.Bijective
      (relativeTateCup L M (-2) (relativeRestriction K L M 2 c)))
    (a : Langlands.LocalClassField.NormQuotient K M) :
    arithmeticReciprocityOfCup L M (relativeRestriction K L M 2 c) hd
        (normQuotientTowerInclusion K L M a) =
      relativeGaloisAbelianTransfer K L M (arithmeticReciprocityOfCup K M c hc a) := by
  apply (abelianizationCupEquiv L M (relativeRestriction K L M 2 c) hd).injective
  rw [abelianizationCupEquiv_restriction]
  change (abelianizationCupEquiv L M (relativeRestriction K L M 2 c) hd)
      ((abelianizationCupEquiv L M (relativeRestriction K L M 2 c) hd).symm
        (normQuotientTowerInclusion K L M a)) =
    normQuotientTowerInclusion K L M
      ((abelianizationCupEquiv K M c hc) ((abelianizationCupEquiv K M c hc).symm a))
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-- Geometric inverse-cup reciprocity satisfies the same actual transfer square,
since inversion commutes with group homomorphisms. -/
theorem geometricReciprocityOfCup_restriction (c : relativeCohomology K M 2)
    (hc : Function.Bijective (relativeTateCup K M (-2) c))
    (hd : Function.Bijective
      (relativeTateCup L M (-2) (relativeRestriction K L M 2 c)))
    (a : Langlands.LocalClassField.NormQuotient K M) :
    geometricReciprocityOfCup L M (relativeRestriction K L M 2 c) hd
        (normQuotientTowerInclusion K L M a) =
      relativeGaloisAbelianTransfer K L M (geometricReciprocityOfCup K M c hc a) := by
  rw [geometricReciprocityOfCup_eq_inv, geometricReciprocityOfCup_eq_inv,
    arithmeticReciprocityOfCup_restriction, map_inv]

end Langlands.ClassFieldTheory.Local
