import Langlands.GroupScheme.SimplyConnected.CentralMultiplicativeSection
import Langlands.GroupScheme.SimplyConnected.MultiplicativeExtensionSplitStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeConnectedActionStatement
import Langlands.GroupScheme.FiniteTypeIdentityComponent

/-! # Reduction of multiplicative extension splitting to connected-action rigidity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Construction

variable (hact : MultiplicativeTypeConnectedActionStatement.{u})
  {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
  (hG : IsSimplyConnected G) (q : H ⟶ G) [Flat q.hom.hom.left]
  (hK : IsMultiplicativeType (kernel q))

include hact hG hK

/-- Connected-action rigidity supplies the section of any multiplicative-type
extension after passing to its full, possibly nonsmooth identity component. -/
theorem IsSimplyConnected.exists_section_of_multiplicativeType_of_connectedAction :
    ∃ s : G ⟶ H, s ≫ q = 𝟙 G := by
  let C := FiniteTypeIdentityComponent.groupScheme H
  let i : C ⟶ H := FiniteTypeIdentityComponent.inclusion H
  let r : C ⟶ G := i ≫ q
  let : Flat r.hom.hom.left := by
    change Flat (i.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  have hKC : IsMultiplicativeType (kernel r) :=
    hK.kernel_comp_of_isClosedSubgroup q i
      (FiniteTypeIdentityComponent.isClosedSubgroup_identityComponentι H)
  have hnormal : (SubgroupFunctor.range (kernelι r)).IsNormal := by
    intro T g x _ hx
    apply (mem_range_kernelι_iff r _).mpr
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
      (mem_range_kernelι_iff r x).mp hx, mul_one, mul_inv_cancel]
  have hcentral : IsCentral (kernelι r) :=
    (hact k C (kernel r) inferInstance inferInstance inferInstance hKC).2
      (kernelι r) (show IsClosedImmersion (kernelι r).hom.hom.left from inferInstance)
      hnormal
  obtain ⟨s, hs⟩ := hG.exists_section_of_central_multiplicative r hcentral hKC
  refine ⟨s ≫ i, ?_⟩
  simpa only [Category.assoc] using hs

/-- A section of an arbitrary multiplicative-type extension, with the
connected-action rigidity proposition supplied explicitly. -/
def IsSimplyConnected.multiplicativeExtensionSection : G ⟶ H :=
  (hG.exists_section_of_multiplicativeType_of_connectedAction hact q hK).choose

/-- The construction gives a section into the original full source. -/
@[reassoc]
theorem IsSimplyConnected.multiplicativeExtensionSection_comp :
    hG.multiplicativeExtensionSection hact q hK ≫ q = 𝟙 G :=
  (hG.exists_section_of_multiplicativeType_of_connectedAction hact q hK).choose_spec

end Construction

/-- The exact published splitting target follows from the exact published
connected-action rigidity proposition, without any other hypotheses. -/
theorem simplyConnectedMultiplicativeExtensionSplit_of_connectedAction
    (hact : MultiplicativeTypeConnectedActionStatement.{u}) :
    SimplyConnectedMultiplicativeExtensionSplitStatement.{u} := by
  intro k _ G H _ _ q hG hflat _ hK
  let : Flat q.hom.hom.left := hflat
  exact hG.exists_section_of_multiplicativeType_of_connectedAction hact q hK

end Langlands.GroupScheme
