import Langlands.ClassFieldTheory.Local.NormExistenceFiniteCorrespondence
import Langlands.ClassFieldTheory.Local.NormExistenceAbelianReduction

/-! # The finite abelian norm correspondence -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

open scoped IsMulCommutative

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

variable {p : ℕ} [Fact p.Prime]

/-- The actual finite abelian Galois group maps isomorphically to the norm quotient. -/
def abelianNormCorrespondenceEquiv (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (F : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsAbelianGalois F.Carrier M] :
    Gal(M/F.Carrier) ≃* Langlands.LocalClassField.NormQuotient F.Carrier M :=
  Abelianization.equivOfComm.trans (normCorrespondenceEquiv I hFund hTate F M)

set_option maxRecDepth 2048 in
/-- Under the abelian correspondence, scalar restriction is the actual norm. -/
theorem abelianNormCorrespondenceEquiv_corestriction (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (hTransfers : I.TateTransferCompatibility)
    (F E : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier M] [FiniteDimensional E.Carrier M]
    [IsAbelianGalois F.Carrier E.Carrier] [IsAbelianGalois F.Carrier M]
    [IsAbelianGalois E.Carrier M] (σ : Gal(M/E.Carrier)) :
    abelianNormCorrespondenceEquiv I hFund hTate F M (σ.restrictScalars F.Carrier) =
      Langlands.LocalClassField.normQuotientTowerNorm F.Carrier E.Carrier M
        (abelianNormCorrespondenceEquiv I hFund hTate E M σ) := by
  exact normCorrespondenceEquiv_corestriction I hFund hTate hTransfers F E M
    (Abelianization.of σ)

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]

/-- The image of the quotient tower norm is the image of the middle norm group. -/
theorem normQuotientTowerNorm_range :
    (Langlands.LocalClassField.normQuotientTowerNorm K L M).range =
      (Langlands.LocalClassField.normSubgroup K L).map
        (Langlands.LocalClassField.normQuotientProjection K M) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
      (Langlands.LocalClassField.normSubgroup L M) x
    exact ⟨Langlands.LocalClassField.normUnits K L a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨Langlands.LocalClassField.normQuotientProjection L M a, rfl⟩

end Tower

/-- The norm quotient image of a middle field corresponds to its automorphism subgroup. -/
theorem normSubgroup_map_eq_relativeGaloisSubgroup_map (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (hTransfers : I.TateTransferCompatibility)
    (F E : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier M] [FiniteDimensional E.Carrier M]
    [IsAbelianGalois F.Carrier E.Carrier] [IsAbelianGalois F.Carrier M]
    [IsAbelianGalois E.Carrier M] :
    (Langlands.LocalClassField.normSubgroup F.Carrier E.Carrier).map
        (Langlands.LocalClassField.normQuotientProjection F.Carrier M) =
      (relativeGaloisSubgroup F.Carrier E.Carrier M).map
        (abelianNormCorrespondenceEquiv I hFund hTate F M).toMonoidHom := by
  rw [← normQuotientTowerNorm_range F.Carrier E.Carrier M]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨σ, rfl⟩ := (abelianNormCorrespondenceEquiv I hFund hTate E M).surjective x
    exact ⟨σ.restrictScalars F.Carrier, ⟨σ, rfl⟩,
      abelianNormCorrespondenceEquiv_corestriction I hFund hTate hTransfers F E M σ⟩
  · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
    exact ⟨abelianNormCorrespondenceEquiv I hFund hTate E M σ,
      (abelianNormCorrespondenceEquiv_corestriction I hFund hTate hTransfers F E M σ).symm⟩

/-- The finite abelian norm group is identified with the actual fixing subgroup. -/
theorem normSubgroup_map_eq_fixingSubgroup_map (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (hTransfers : I.TateTransferCompatibility)
    (F : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsAbelianGalois F.Carrier M] (E : IntermediateField F.Carrier M) :
    (Langlands.LocalClassField.normSubgroup F.Carrier E).map
        (Langlands.LocalClassField.normQuotientProjection F.Carrier M) =
      E.fixingSubgroup.map
        (abelianNormCorrespondenceEquiv I hFund hTate F M).toMonoidHom := by
  let : Algebra (Padic p) M :=
    ((algebraMap F.Carrier M).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  let : IsScalarTower (Padic p) F.Carrier M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F.Carrier E
  let E' : PadicField.{u} p := { Carrier := E }
  have h := normSubgroup_map_eq_relativeGaloisSubgroup_map I hFund hTate hTransfers
    F E' M
  change (Langlands.LocalClassField.normSubgroup F.Carrier E).map
      (Langlands.LocalClassField.normQuotientProjection F.Carrier M) =
    (relativeGaloisSubgroup F.Carrier E M).map
      (abelianNormCorrespondenceEquiv I hFund hTate F M).toMonoidHom at h
  rwa [relativeGaloisSubgroup_eq_ker, E.restrictNormalHom_ker] at h

/-- Every overgroup of a finite abelian norm group is the norm group of a subfield. -/
theorem finiteAbelianNormOvergroup (I : InvariantFamily.{u,u} p)
    (hFund : I.FundamentalClasses) (hTate : I.TateIsomorphisms)
    (hTransfers : I.TateTransferCompatibility)
    (F : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsAbelianGalois F.Carrier M] (H : Subgroup F.Carrierˣ)
    (hH : Langlands.LocalClassField.normSubgroup F.Carrier M ≤ H) :
    ∃ E : IntermediateField F.Carrier M,
      FiniteDimensional F.Carrier E ∧ IsAbelianGalois F.Carrier E ∧
        Langlands.LocalClassField.normSubgroup F.Carrier E = H := by
  let q := Langlands.LocalClassField.normQuotientProjection F.Carrier M
  let e := abelianNormCorrespondenceEquiv I hFund hTate F M
  let B := (H.map q).comap e.toMonoidHom
  let E := IntermediateField.fixedField B
  refine ⟨E, inferInstance, inferInstance, ?_⟩
  have hm : (Langlands.LocalClassField.normSubgroup F.Carrier E).map q = H.map q := by
    rw [normSubgroup_map_eq_fixingSubgroup_map I hFund hTate hTransfers F M E]
    change (IntermediateField.fixingSubgroup (IntermediateField.fixedField B)).map
      e.toMonoidHom = H.map q
    rw [IntermediateField.fixingSubgroup_fixedField]
    exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
  apply Subgroup.map_injective_of_ker_le (f := q) _ _ hm
  · change (QuotientGroup.mk' (Langlands.LocalClassField.normSubgroup F.Carrier M)).ker ≤ _
    rw [QuotientGroup.ker_mk']
    exact normSubgroup_le_of_tower F.Carrier M E
  · change (QuotientGroup.mk' (Langlands.LocalClassField.normSubgroup F.Carrier M)).ker ≤ _
    rwa [QuotientGroup.ker_mk']

/-- The local class formation discharges every arithmetic input of finite saturation. -/
theorem exists_normSubgroup_eq_of_le_finite_abelian (F : PadicField.{u} p)
    (M : Type u) [Field M] [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsAbelianGalois F.Carrier M] (H : Subgroup F.Carrierˣ)
    (hH : Langlands.LocalClassField.normSubgroup F.Carrier M ≤ H) :
    ∃ E : IntermediateField F.Carrier M,
      FiniteDimensional F.Carrier E ∧ IsAbelianGalois F.Carrier E ∧
        Langlands.LocalClassField.normSubgroup F.Carrier E = H := by
  obtain ⟨I, _, _, _, _, _, hFund, _, _, _, _, hTate, _, hTransfers, _, _⟩ :=
    localAbsoluteCorestrictionCompatibleClassFormation p
  exact finiteAbelianNormOvergroup I hFund hTate hTransfers F M H hH

end Langlands.ClassFieldTheory.Local
