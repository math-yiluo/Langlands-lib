import Langlands.ClassFieldTheory.Local.Galois
import Langlands.Weil.Pullback
import Mathlib.GroupTheory.Transfer

/-!
# Continuous transfer for open subgroups of finite index

The homomorphism is Mathlib's actual finite-coset transfer. Openness makes
the coset space discrete and proves continuity of its finite product.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v

section Transfer

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type v} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  (H : Subgroup G) [H.FiniteIndex] (hH : IsOpen (H : Set G))

open scoped Pointwise

include hH in
private theorem transfer_continuous (f : H →ₜ* A) :
    Continuous (MonoidHom.transfer f.toMonoidHom) := by
  classical
  let := QuotientGroup.discreteTopology hH
  let := H.fintypeQuotientOfFiniteIndex
  let T : H.LeftTransversal := default
  change Continuous (fun g => Subgroup.leftTransversals.diff f.toMonoidHom T (g • T))
  unfold Subgroup.leftTransversals.diff
  apply continuous_finsetProd
  intro q _
  apply f.continuous.comp
  apply Continuous.subtype_mk
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  exact continuous_const.mul
    (continuous_id.mul ((continuous_subtype_val.comp
      (show Continuous T.2.leftQuotientEquiv from continuous_of_discreteTopology)).comp
      (continuous_inv.smul continuous_const)))

/-- The actual transfer homomorphism, with its continuity proved using
the discrete finite coset space of the open subgroup. -/
def continuousTransfer (f : H →ₜ* A) : G →ₜ* A where
  toMonoidHom := MonoidHom.transfer f.toMonoidHom
  continuous_toFun := transfer_continuous H hH f

/-- The continuous transfer into the actual topological abelianization
of the open subgroup. -/
def transferToAbelianization : G →ₜ* TopologicalAbelianization H :=
  continuousTransfer H hH (abelianizationProjection H)

/-- The continuous transfer on actual closed-commutator quotients. -/
def abelianizedTransfer :
    TopologicalAbelianization G →ₜ* TopologicalAbelianization H := by
  letI := abelianizationHausdorff H
  exact abelianizationLift (transferToAbelianization H hH)

end Transfer

section Nested

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H J : Subgroup G} (h : H ≤ J)

/-- The actual inclusion of nested subgroups, with their inherited topologies. -/
def subgroupInclusion : H →ₜ* J where
  toMonoidHom := Subgroup.inclusion h
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Rebracketing the same subgroup inside a larger subgroup is a continuous
group equivalence. Both topologies are the iterated subtype topology. -/
def subgroupOfEquiv : H.subgroupOf J ≃ₜ* H where
  toMulEquiv := Subgroup.subgroupOfEquivOfLe h
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Inclusion on topological abelianizations of any two nested subgroups. -/
def subgroupAbelianInclusion :
    TopologicalAbelianization H →ₜ* TopologicalAbelianization J :=
  abelianizationMap (subgroupInclusion h)

/-- Transfer from the larger subgroup to the smaller one. Finite index in
the ambient group implies finite index inside `J`; openness is inherited.
The target is the original subgroup, not an unidentified abstract copy. -/
def subgroupAbelianTransfer [H.FiniteIndex] (hH : IsOpen (H : Set G)) :
    TopologicalAbelianization J →ₜ* TopologicalAbelianization H :=
  (abelianizationMap (subgroupOfEquiv h :
    H.subgroupOf J →ₜ* H)).comp
    (abelianizedTransfer (H.subgroupOf J) (hH.preimage continuous_subtype_val))

end Nested

section Absolute

variable (K : Type u) [Field K] [PerfectField K]
  (E : IntermediateField K (AlgebraicClosure K)) [hfin : FiniteDimensional K E]

/-- The actual subgroup fixing a finite intermediate field has finite index.
Its quotient is compact and discrete. -/
theorem absoluteFixingFiniteIndex : E.fixingSubgroup.FiniteIndex := by
  let : IsGalois K (AlgebraicClosure K) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  let := QuotientGroup.discreteTopology E.fixingSubgroup_isOpen
  let : Finite (Field.absoluteGaloisGroup K ⧸ E.fixingSubgroup) :=
    finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Actual transfer from the absolute-Galois abelianization of the base
to the abelianization of the subgroup fixing `E`, in the common closure.
No identification with a separately chosen closure of `E` is assumed. -/
def absoluteTransferToFixing :
    Field.absoluteGaloisGroupAbelianization K →ₜ*
      TopologicalAbelianization E.fixingSubgroup := by
  letI := absoluteFixingFiniteIndex K E
  exact abelianizedTransfer E.fixingSubgroup E.fixingSubgroup_isOpen

/-- The opposite-direction inclusion on the same actual abelianized groups. -/
def absoluteFixingAbelianInclusion :
    TopologicalAbelianization E.fixingSubgroup →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  abelianizationMap
    { toMonoidHom := E.fixingSubgroup.subtype
      continuous_toFun := continuous_subtype_val }

variable (φ : Field.absoluteGaloisGroup K →ₜ* Weil.ProfiniteIntegers)

/-- The actual subgroup of the existing pullback whose Galois projection
fixes `E`. Its topology is inherited from the pullback. This definition
does not identify a separately presented local Weil group over `E`. -/
def pullbackFixingSubgroup : Subgroup (Weil.Pullback φ) :=
  E.fixingSubgroup.comap (Weil.projection φ).toMonoidHom

omit [PerfectField K] in
/-- Openness follows from the Krull-open fixing subgroup by preimage. -/
theorem pullbackFixingSubgroup_open :
    IsOpen (pullbackFixingSubgroup K E φ : Set (Weil.Pullback φ)) :=
  E.fixingSubgroup_isOpen.preimage (Weil.projection φ).continuous

include hfin in
/-- Finite index is preserved by homomorphic preimage; projection need
not be onto for this construction. -/
theorem pullbackFixingFiniteIndex :
    (pullbackFixingSubgroup K E φ).FiniteIndex := by
  exact @Subgroup.instFiniteIndexComap _ _ _ _
    (Weil.projection φ).toMonoidHom E.fixingSubgroup (absoluteFixingFiniteIndex K E)

/-- Actual continuous transfer to the subgroup fixing the finite extension
inside the existing Weil pullback. -/
def pullbackTransferToFixing :
    TopologicalAbelianization (Weil.Pullback φ) →ₜ*
      TopologicalAbelianization (pullbackFixingSubgroup K E φ) := by
  letI := pullbackFixingFiniteIndex K E φ
  exact abelianizedTransfer (pullbackFixingSubgroup K E φ)
    (pullbackFixingSubgroup_open K E φ)

/-- The corresponding inclusion on the actual abelianized pullback groups. -/
def pullbackFixingAbelianInclusion :
    TopologicalAbelianization (pullbackFixingSubgroup K E φ) →ₜ*
      TopologicalAbelianization (Weil.Pullback φ) :=
  abelianizationMap
    { toMonoidHom := (pullbackFixingSubgroup K E φ).subtype
      continuous_toFun := continuous_subtype_val }

end Absolute

end Langlands.LocalClassField
