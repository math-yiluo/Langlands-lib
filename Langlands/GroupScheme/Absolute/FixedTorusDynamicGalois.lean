import Langlands.GroupScheme.Absolute.SplitTorusDynamicDescent
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Dynamic.DescentTransport

/-! # Galois action on fixed-torus dynamic presentations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Naturality

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  (T : CommGroupScheme B) {G : GroupScheme B} (j : T.toGrp ⟶ G)
  (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T))

/-- Transport of a torus cocharacter agrees with transport after its ambient inclusion. -/
theorem cocharacterLattice.groupHom_transport_comp :
    CommGroupScheme.groupHom (cocharacterLattice.transport b a ha T ν) ≫
        (GroupScheme.baseChange b).map j =
      transportCocharacter b a ha G
        (CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map j) := by
  rw [cocharacterLattice.groupHom_transport, transportCocharacter_naturality]

/-- If an ambient dynamic subgroup comes from the original base, transport of its
torus cocharacter defines the same subgroup on every test scheme. -/
theorem Dynamic.parabolic_torus_transport_eq_baseChange (F : SubgroupFunctor G)
    (hν : Dynamic.parabolic
      (CommGroupScheme.groupHom ν ≫ (GroupScheme.baseChange b).map j) =
        F.baseChange b) :
    Dynamic.parabolic
      (CommGroupScheme.groupHom (cocharacterLattice.transport b a ha T ν) ≫
        (GroupScheme.baseChange b).map j) = F.baseChange b := by
  rw [cocharacterLattice.groupHom_transport_comp]
  exact Dynamic.parabolic_transportCocharacter_eq_baseChange b a ha G _ F hν

end Naturality

section Galois

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))
  {G P : GroupScheme (Spec (CommRingCat.of k))}
  (j : T.toGrp ⟶ G) (i : P ⟶ G)

/-- Every Galois translate of a fixed-torus dynamic presentation is again a presentation. -/
theorem fixedTorusDynamicPresentation_galois
    (ν : FixedTorusDynamicPresentations
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
    (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.range ((GroupScheme.baseChange (algebraBaseMap k K)).map i) =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν.val) ≫
          (GroupScheme.baseChange (algebraBaseMap k K)).map j) := by
  rw [cocharacterLattice.galoisRepresentation_apply]
  exact (SubgroupFunctor.range_baseChange _ i).symm.trans
    (Dynamic.parabolic_torus_transport_eq_baseChange (algebraBaseMap k K)
      (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T j ν.val
      (SubgroupFunctor.range i)
      (ν.property.symm.trans (SubgroupFunctor.range_baseChange _ i).symm)).symm

/-- The lattice Galois action restricted to actual fixed-torus dynamic presentations. -/
@[instance_reducible]
def fixedTorusDynamicPresentationGaloisAction :
    MulAction (K ≃ₐ[k] K)
      (FixedTorusDynamicPresentations
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map j)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i)) where
  smul σ ν := ⟨cocharacterLattice.galoisRepresentation k K T σ ν.val,
    fixedTorusDynamicPresentation_galois k K T j i ν σ⟩
  one_smul ν := Subtype.ext (by
    change cocharacterLattice.galoisRepresentation k K T 1 ν.val = ν.val
    exact congrArg (fun f => f ν.val) (cocharacterLattice.galoisRepresentation k K T).map_one)
  mul_smul σ τ ν := Subtype.ext (by
    exact congrArg (fun f => f ν.val) ((cocharacterLattice.galoisRepresentation k K T).map_mul σ τ))

end Galois

end Langlands.GroupScheme
