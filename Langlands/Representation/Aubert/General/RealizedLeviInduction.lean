import Langlands.GroupScheme.Dynamic.LeviExtensionPoints
import Langlands.Representation.Aubert.General.RepresentedDynamicTransport

/-! # Normalized induction through an exact realization inside a Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RealizedLeviTransport

universe u uV

variable (R : Type u) [CommRing R] [TopologicalSpace R]
    {G L : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffine G.X.left] [IsAffine L.X.left]
    (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
    (j : L ⟶ G) (hj : (Dynamic.centralizer χ).IsRepresentedBy j)
    (hc : IsClosedSubgroup j)
    (ν : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ L)
    (ψ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
    (hReal :
      Dynamic.parabolic ψ =
          Dynamic.extendFromCentralizer χ j hj (Dynamic.parabolic ν) ∧
        Dynamic.centralizer ψ = (Dynamic.centralizer ν).map j ∧
        Dynamic.unipotent ψ =
          Dynamic.extendFromCentralizer χ j hj (Dynamic.unipotent ν))

local instance ambientPointTopology :
    TopologicalSpace (RationalPoint R G.X) := rationalPointTopology R G.X

local instance representativePointTopology :
    TopologicalSpace (RationalPoint R L.X) := rationalPointTopology R L.X

local notation "test" => Over.mk (𝟙 (Spec (CommRingCat.of R)))

variable [IsSeparated G.X.hom]

include hReal in
/-- The source parabolic matches the realized parabolic inside the outer Levi. -/
theorem parabolic_mem (x : RationalPoint R L.X) :
    x ∈ (Dynamic.parabolic ν).carrier test ↔
      (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc) x ∈
        ((Dynamic.parabolic ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test) := by
  rw [Dynamic.realized_parabolic_subgroupOf χ j hj ν ψ hc hReal.1 test]
  exact RepresentedDynamicTransport.parabolic_mem R (Dynamic.centralizer χ) j hj hc ν x

omit [IsSeparated G.X.hom] in
include hReal in
/-- The source centralizer matches the realized centralizer inside the outer Levi. -/
theorem centralizer_mem (x : RationalPoint R L.X) :
    x ∈ (Dynamic.centralizer ν).carrier test ↔
      (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc) x ∈
        ((Dynamic.centralizer ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test) := by
  rw [Dynamic.realized_centralizer_subgroupOf χ j hj ν ψ hc hReal.2.1 test]
  exact RepresentedDynamicTransport.centralizer_mem R (Dynamic.centralizer χ) j hj hc ν x

include hReal in
/-- The source radical matches the realized radical inside the outer Levi. -/
theorem unipotent_mem (x : RationalPoint R L.X) :
    x ∈ (Dynamic.unipotent ν).carrier test ↔
      (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc) x ∈
        ((Dynamic.unipotent ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test) := by
  rw [Dynamic.realized_unipotent_subgroupOf χ j hj ν ψ hc hReal.2.2 test]
  exact RepresentedDynamicTransport.unipotent_mem R (Dynamic.centralizer χ) j hj hc ν x

include hc hReal in
/-- Exact realization supplies the literal inner semidirect decomposition. -/
theorem insideDecomposition [IsSeparated L.X.hom] :
    IsSemidirectDecomposition
      (((Dynamic.parabolic ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test))
      (((Dynamic.centralizer ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test))
      (((Dynamic.unipotent ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test)) :=
  GroupTransport.semidirectDecomposition (dynamic_isSemidirectDecomposition ν test)
    (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc).toMulEquiv
    (parabolic_mem R χ j hj hc ν ψ hReal)
    (centralizer_mem R χ j hj hc ν ψ hReal)
    (unipotent_mem R χ j hj hc ν ψ hReal)

omit [IsSeparated G.X.hom] in
/-- The source Levi points identify with the realized inner Levi. -/
def centralizerEquiv :
    (Dynamic.centralizer ν).carrier test ≃ₜ*
      ((Dynamic.centralizer ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test) :=
  GroupTransport.subgroupEquiv (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc)
    (centralizer_mem R χ j hj hc ν ψ hReal)

include hc hReal in
/-- Ambient closedness of the realized radical implies source radical closedness. -/
theorem unipotentClosed
    (hU : IsClosed ((Dynamic.unipotent ψ).carrier test :
      Set (RationalPoint R G.X))) :
    IsClosed ((Dynamic.unipotent ν).carrier test : Set (RationalPoint R L.X)) := by
  have heq : ((Dynamic.unipotent ν).carrier test : Set (RationalPoint R L.X)) =
      (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc) ⁻¹'
        (((Dynamic.unipotent ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test) :
          Set ((Dynamic.centralizer χ).carrier test)) :=
    Set.ext (unipotent_mem R χ j hj hc ν ψ hReal)
  rw [heq]
  exact (hU.preimage continuous_subtype_val).preimage
    (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc).continuous

section Functors

variable [LocallyCompactSpace ((Dynamic.centralizer χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))))]
    [NonarchimedeanGroup ((Dynamic.centralizer χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))))]
    [LocallyCompactSpace (RationalPoint R L.X)]
    [NonarchimedeanGroup (RationalPoint R L.X)]
    [IsSeparated L.X.hom]
    (hU : IsClosed ((Dynamic.unipotent ψ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) : Set (RationalPoint R G.X)))

/-- The full-parabolic normalized induction in the realized inner parabolic
agrees naturally with normalized induction in the source representative. -/
def inductionIso :
    normalizedInductionFunctor.{u, uV}
        (insideDecomposition R χ j hj hc ν ψ hReal)
        (hU.preimage continuous_subtype_val) ⋙
      SmoothRep.pullbackFunctor (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc) ≅
      SmoothRep.pullbackFunctor (centralizerEquiv R χ j hj hc ν ψ hReal) ⋙
        normalizedInductionFunctor (dynamic_isSemidirectDecomposition ν test)
          (unipotentClosed R χ j hj hc ν ψ hReal hU) :=
  GroupTransport.inductionIso (insideDecomposition R χ j hj hc ν ψ hReal)
    (dynamic_isSemidirectDecomposition ν test)
    (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc)
    (parabolic_mem R χ j hj hc ν ψ hReal) (centralizer_mem R χ j hj hc ν ψ hReal)
    (unipotent_mem R χ j hj hc ν ψ hReal) (hU.preimage continuous_subtype_val)
    (unipotentClosed R χ j hj hc ν ψ hReal hU)

/-- On actual induced functions the comparison is precomposition by the
represented-point homeomorphism. -/
@[simp]
theorem inductionIso_hom_eval
    (A : SmoothRep.{0, u, uV} ℂ
      (((Dynamic.centralizer ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test)))
    (f : (normalizedInductionFunctor (insideDecomposition R χ j hj hc ν ψ hReal)
      (hU.preimage continuous_subtype_val)).obj A) (y : RationalPoint R L.X) :
    Induction.eval ((Dynamic.parabolic ν).carrier test)
      (inducingRepresentation (dynamic_isSemidirectDecomposition ν test)
        (unipotentClosed R χ j hj hc ν ψ hReal hU)
        ((SmoothRep.pullbackFunctor (centralizerEquiv R χ j hj hc ν ψ hReal)).obj A))
      (SmoothRep.hom ((inductionIso R χ j hj hc ν ψ hReal hU).app A).hom f) y =
    Induction.eval (((Dynamic.parabolic ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test))
      (inducingRepresentation (insideDecomposition R χ j hj hc ν ψ hReal)
        (hU.preimage continuous_subtype_val) A) f
        (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc y) := rfl

/-- The two actual normalized induced objects have finite group-algebra
length simultaneously. This asserts no finite-length existence result. -/
theorem induction_hasFiniteLength_iff
    (A : SmoothRep.{0, u, uV} ℂ
      (((Dynamic.centralizer ψ).carrier test).subgroupOf
          ((Dynamic.centralizer χ).carrier test))) :
    ((normalizedInductionFunctor (insideDecomposition R χ j hj hc ν ψ hReal)
      (hU.preimage continuous_subtype_val)).obj A).HasFiniteLength ↔
    ((normalizedInductionFunctor (dynamic_isSemidirectDecomposition ν test)
      (unipotentClosed R χ j hj hc ν ψ hReal hU)).obj
      ((SmoothRep.pullbackFunctor (centralizerEquiv R χ j hj hc ν ψ hReal)).obj A)).HasFiniteLength := by
  let I := (normalizedInductionFunctor (insideDecomposition R χ j hj hc ν ψ hReal)
    (hU.preimage continuous_subtype_val)).obj A
  have hpb : I.HasFiniteLength ↔
      ((SmoothRep.pullbackFunctor (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc)).obj I).HasFiniteLength :=
    FiniteLengthAssembly.finiteLength_comp_surjective_iff I.representation
      (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc).toMonoidHom
      (RepresentedDynamicTransport.pointEquiv R (Dynamic.centralizer χ) j hj hc).surjective
  exact hpb.trans ⟨SmoothRep.hasFiniteLength_of_iso
    ((inductionIso R χ j hj hc ν ψ hReal hU).app A),
    SmoothRep.hasFiniteLength_of_iso ((inductionIso R χ j hj hc ν ψ hReal hU).app A).symm⟩

end Functors

end Langlands.Aubert.General.RealizedLeviTransport
