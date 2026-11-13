import Langlands.Global.Factors.RelativeWeilLocalEpsilon
import Langlands.ClassFieldTheory.Local.WeilTransferReciprocityStatement
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof
import Langlands.ClassFieldTheory.Local.DenseTransferNaturality
import Langlands.Correspondence.BaseReciprocityCandidate
import Langlands.ClassField.Global.RelativeWeilTransfer

/-!
# The local Weil transfer/inclusion square along embeddings of p-adic fields

A normalized common-closure reciprocity system of `F` exists. Its components at the
bottom field and at the image of `E` are the unique geometric reciprocity maps of `F`
and of `E`. Its transfer relation for these two fields is the square.
-/

noncomputable section

namespace Langlands.LocalClassField

open Weil.Local LocalFactor.CommonClosure

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance baseCharZero : CharZero F.Carrier :=
  Algebra.charZero_of_charZero (Padic p) F.Carrier

/-- The canonical topology of each finite intermediate field, as used by
`reciprocityUnits`. -/
local instance intermediateFieldTopology (L : Extension F) : TopologicalSpace L.field :=
  (fieldData F L).topology

namespace ExtensionWeilTransfer

/-- Transfer to a subgroup equals transfer to an equal subgroup. -/
theorem transfer_subgroupCongr {G A : Type*} [Group G] [CommGroup A] {H K : Subgroup G}
    (h : H = K) [H.FiniteIndex] [K.FiniteIndex] (ϕ : K →* A) (g : G) :
    MonoidHom.transfer (ϕ.comp (MulEquiv.subgroupCongr h).toMonoidHom) g =
      MonoidHom.transfer ϕ g := by
  subst h
  rfl

/-- For a family with the transfer relation, the actual transfer from `W_F` to the
subgroup fixing a finite intermediate field `L` is the bottom component followed by
the inclusion of `⊥` in `L`. -/
theorem transfer_weilSubgroup (eC : ReciprocityFamily F)
    (hT : CommonClosure.TransferRelation F (CommonClosure.canonicalData F)
      (localResidueDegree F) eC)
    (L : Extension F) (y : localWeilGroup F) :
    MonoidHom.transfer (reciprocityUnits F eC L).toMonoidHom y =
      (Correspondence.baseExtension F).unitsInclusion L (Langlands.LocalFactor.CommonClosure.baseExtension_le F L)
        (reciprocityUnits F eC (Correspondence.baseExtension F)
          (Correspondence.baseWeilEquiv F y)) := by
  let B := Correspondence.baseExtension F
  let w := Correspondence.baseWeilEquiv F y
  have h := congrArg (fun g => g (abelianizationProjection _ w))
    (hT B L (Langlands.LocalFactor.CommonClosure.baseExtension_le F L))
  let ι : weilSubgroup F B →ₜ* localWeilGroup F :=
    { toMonoidHom := (weilSubgroup F B).subtype
      continuous_toFun := continuous_subtype_val }
  have hdense : DenseRange ι := by
    apply Function.Surjective.denseRange
    intro v
    exact ⟨Correspondence.baseWeilEquiv F v, rfl⟩
  let K := (weilSubgroup F L).comap ι.toMonoidHom
  let ρ := TransferNaturality.subgroupPreimageMap ι (weilSubgroup F L)
  calc MonoidHom.transfer (reciprocityUnits F eC L).toMonoidHom y
      = MonoidHom.transfer ((reciprocityUnits F eC L).toMonoidHom.comp ρ.toMonoidHom) w :=
        TransferNaturality.transfer_comp_denseRange ι (weilSubgroup F L) hdense
          (pullbackFixingSubgroup_open F.Carrier L.field (localResidueDegree F))
          (reciprocityUnits F eC L).toMonoidHom w
    _ = MonoidHom.transfer (((eC L).toMonoidHom.comp (abelianizationMap ρ).toMonoidHom).comp
          (abelianizationProjection K).toMonoidHom) w := rfl
    _ = ((eC L).toMonoidHom.comp (abelianizationMap ρ).toMonoidHom)
          (MonoidHom.transfer (abelianizationProjection K).toMonoidHom w) :=
        GroupTheory.Transfer.transfer_comp _ _ _
    _ = ((eC L).toMonoidHom.comp (FiniteIntermediateExtension.weilAbelianTransfer B L
          (Langlands.LocalFactor.CommonClosure.baseExtension_le F L) (localResidueDegree F)).toMonoidHom)
          (abelianizationProjection _ w) := rfl
    _ = _ := h

end ExtensionWeilTransfer

open ExtensionWeilTransfer in
/-- **Local transfer/inclusion square.** For every embedding `f : F → E` of p-adic
fields and arbitrary geometric reciprocity candidates `eF`, `eE`, the actual
coset-product transfer from `W_F` to the image of `W_E`, followed by reciprocity of
`E`, is reciprocity of `F` followed by `f` on units. -/
theorem extensionWeilTransferReciprocity : ExtensionWeilTransferReciprocityStatement.{u, v} := by
  intro p _ F E f eF eE hF hE
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  have := extensionWeilMap_range_finiteIndex F E f
  obtain ⟨eC, heC⟩ := commonClosureReciprocityExistence.{u} p F F.canonicalTopologicalData
  have hgeo := commonClosureGeometricProof.{u, v} p F eC heC
  have hFeq : eF = Correspondence.baseReciprocityCandidate F eC :=
    geometricWeilReciprocityUniqueness p F _ _ _ hF
      (hgeo.1 _ (Correspondence.baseReciprocityCandidate_spec F eC))
  have hEeq : eE = extensionReciprocityCandidate F E f eC :=
    geometricWeilReciprocityUniqueness p E _ _ _ hE (hgeo.2 E f)
  subst hFeq hEeq
  intro y
  let L := extensionFiniteIntermediate F E f
  have hcomp : (LocalFactor.RankOne.reciprocityUnits E
        (extensionReciprocityCandidate F E f eC)).toMonoidHom.comp
        (InductionAlong.rangeInverse (extensionWeilMap F E f).toMonoidHom
          (extensionWeilMap_injective F E f)) =
      ((extensionIntermediateUnitsEquiv F E f).symm : L.fieldˣ →* E.Carrierˣ).comp
        ((reciprocityUnits F eC L).toMonoidHom.comp
          (MulEquiv.subgroupCongr (extensionWeilRange_eq_fixing F E f)).toMonoidHom) := by
    apply MonoidHom.ext
    intro r
    have hr : extensionImageWeilEquiv F E f (InductionAlong.rangeInverse
        (extensionWeilMap F E f).toMonoidHom (extensionWeilMap_injective F E f) r) =
        MulEquiv.subgroupCongr (extensionWeilRange_eq_fixing F E f) r :=
      Subtype.ext (InductionAlong.apply_rangeInverse _ _ r)
    change (extensionIntermediateUnitsEquiv F E f).symm
        (eC L (abelianizationProjection _ (extensionImageWeilEquiv F E f
          (InductionAlong.rangeInverse (extensionWeilMap F E f).toMonoidHom
            (extensionWeilMap_injective F E f) r)))) =
      (extensionIntermediateUnitsEquiv F E f).symm
        (eC L (abelianizationProjection _
          (MulEquiv.subgroupCongr (extensionWeilRange_eq_fixing F E f) r)))
    rw [hr]
  rw [hcomp, GroupTheory.Transfer.transfer_comp, transfer_subgroupCongr,
    transfer_weilSubgroup F eC heC.1.2.1 L y]
  change (extensionIntermediateUnitsEquiv F E f).symm _ = _
  rw [ContinuousMulEquiv.symm_apply_eq]
  apply Units.ext
  apply Subtype.ext
  have hbase : ((IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)
      (reciprocityUnits F eC (Correspondence.baseExtension F)
        (Correspondence.baseWeilEquiv F y) : (Correspondence.baseExtension F).field)) :
          F.Carrier) =
      ((LocalFactor.RankOne.reciprocityUnits F (Correspondence.baseReciprocityCandidate F eC) y :
        F.Carrierˣ) : F.Carrier) :=
    Correspondence.baseReciprocityCandidate_spec F eC (Correspondence.baseWeilEquiv F y)
  change ((reciprocityUnits F eC (Correspondence.baseExtension F)
      (Correspondence.baseWeilEquiv F y) : (Correspondence.baseExtension F).field) :
        AlgebraicClosure F.Carrier) =
    extensionFieldEmbedding F E f (f ((LocalFactor.RankOne.reciprocityUnits F
      (Correspondence.baseReciprocityCandidate F eC) y : F.Carrierˣ) : F.Carrier))
  rw [← hbase, extensionFieldEmbedding_comp]
  exact congrArg Subtype.val
    ((IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm_apply_apply
      ((reciprocityUnits F eC (Correspondence.baseExtension F)
        (Correspondence.baseWeilEquiv F y) : (Correspondence.baseExtension F).field) :
          (⊥ : IntermediateField F.Carrier (AlgebraicClosure F.Carrier)))).symm

end Langlands.LocalClassField
