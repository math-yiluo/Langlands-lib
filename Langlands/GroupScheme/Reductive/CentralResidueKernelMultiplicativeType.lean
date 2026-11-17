import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.Reductive.CenterMultiplicativeTypeProof
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.KernelInfinitesimalCentrality
import Langlands.GroupScheme.HopfFiberCentralityResidue

/-! # Absolute multiplicative type of central residue kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.CentralResidueKernelMultiplicativeType

/-- A central closed subgroup of a connected reductive field group is of
absolute multiplicative type, retaining the whole scheme structure. -/
theorem isMultiplicativeType_of_central_closedSubgroup
    {k : Type u} [Field k]
    {K G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (i : K ⟶ G)
    (hi : IsClosedSubgroup i) (hc : IsCentral i) : IsMultiplicativeType K := by
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
  let j := hz.isRepresentedBy.factorHom i ((isCentral_iff_range_le_center i).1 hc)
  have hj : IsClosedSubgroup j := IsClosedSubgroup.of_comp hz.1 (by
    rw [SubgroupFunctor.IsRepresentedBy.factorHom_comp]
    exact hi)
  exact (centerMultiplicativeType k G Z z hG hz).of_isClosedSubgroup j hj

/-- Centrality on all canonical residue fibres gives centrality after every
field-valued base change, by the residue-field factorization of that point. -/
theorem isCentral_field_baseChange_of_residue
    {S : Scheme.{u}} {K G : GroupScheme S} (i : K ⟶ G)
    (hc : ∀ s : S, IsCentral ((baseChange (S.fromSpecResidueField s)).map i))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsCentral ((baseChange b).map i) := by
  let s := b (IsLocalRing.closedPoint k)
  let φ : S.residueField s ⟶ CommRingCat.of k :=
    S.descResidueField (Scheme.stalkClosedPointTo b)
  have hb : Spec.map φ ≫ S.fromSpecResidueField s = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S b
  have h := (HopfFiberCentralityResidue.isCentral_baseChange_comp_iff
    (S.fromSpecResidueField s) (Spec.map φ) i).2 ((hc s).baseChange (Spec.map φ))
  rwa [hb] at h

/-- Every actual field fibre of the kernel is of absolute multiplicative type
when the source is reductive, the target is separated, and all actual
canonical residue kernels are central. -/
theorem isMultiplicativeType_kernel_fieldFiber
    {S : Scheme.{u}} {G H : GroupScheme S} (hG : IsReductive G)
    [IsSeparated H.X.hom] (f : G ⟶ H)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f)))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsMultiplicativeType ((baseChange b).obj (kernel f)) := by
  apply isMultiplicativeType_of_central_closedSubgroup
    (hG.isConnectedReductive_baseChange b) ((baseChange b).map (kernelι f))
  · exact (show IsClosedSubgroup (kernelι f) from
      inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left)).baseChange b
  · exact isCentral_field_baseChange_of_residue (kernelι f)
      (fun s => (KernelInfinitesimalCentrality.isCentral_kernel_baseChange_iff
        (S.fromSpecResidueField s) f).1 (hc s)) b

/-- The unchanged actual field fibre of the kernel, bundled with its
absolute multiplicative-type proof. -/
def multiplicativeTypeKernelFieldFiber
    {S : Scheme.{u}} {G H : GroupScheme S} (hG : IsReductive G)
    [IsSeparated H.X.hom] (f : G ⟶ H)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f)))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    {K : GroupScheme (Spec (CommRingCat.of k)) // IsMultiplicativeType K} :=
  ⟨(baseChange b).obj (kernel f), isMultiplicativeType_kernel_fieldFiber hG f hc b⟩

@[simp]
theorem multiplicativeTypeKernelFieldFiber_val
    {S : Scheme.{u}} {G H : GroupScheme S} (hG : IsReductive G)
    [IsSeparated H.X.hom] (f : G ⟶ H)
    (hc : ∀ s : S, IsCentral (kernelι
      ((baseChange (S.fromSpecResidueField s)).map f)))
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    (multiplicativeTypeKernelFieldFiber hG f hc b).val =
      (baseChange b).obj (kernel f) := rfl

end Langlands.GroupScheme.CentralResidueKernelMultiplicativeType
