import Langlands.GroupScheme.Rational.RootKernelIdentityAction
import Langlands.GroupScheme.Rational.QuotientActionComparisonProof
import Langlands.GroupScheme.Dynamic.IdentityComponent
import Langlands.GroupScheme.Dynamic.ActionFunctoriality

/-! # Actual relative roots through the full-kernel identity component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G H K : GroupScheme B}

/-- Successive all-test images equal the image under the composite homomorphism. -/
theorem map_comp (F : SubgroupFunctor G) (f : G ⟶ H) (g : H ⟶ K) :
    (F.map f).map g = F.map (f ≫ g) := by
  apply ext
  intro U
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
    change U ⟶ H.X at y
    change U ⟶ G.X at z
    refine ⟨z, hz, ?_⟩
    change z ≫ f.hom.hom ≫ g.hom.hom = x
    change z ≫ f.hom.hom = y at hzy
    change y ≫ g.hom.hom = x at hyx
    rw [← Category.assoc, hzy, hyx]
  · rintro ⟨z, hz, hzx⟩
    change U ⟶ G.X at z
    refine ⟨z ≫ f.hom.hom, ⟨z, hz, rfl⟩, ?_⟩
    change z ≫ f.hom.hom ≫ g.hom.hom = x at hzx
    exact (Category.assoc _ _ _).trans hzx

end SubgroupFunctor

namespace AutomorphicAction.IsEquivariant

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {a₀ : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp
      (identityComponent G)}
    {a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp G}

/-- An equivariant action on the actual identity component has precisely the
same identity-limit functor after inclusion, on every test scheme. -/
theorem unipotent_map_identityComponent
    (hf : a₀.IsEquivariant a (identityComponentι G)) :
    a₀.unipotent.map (identityComponentι G) = a.unipotent := by
  rw [← hf.range_inf_unipotent
    (IdentityComponent.isClosedSubgroup_identityComponentι G)]
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  exact ⟨And.right, fun hx => ⟨a.unipotent_le_identityComponent U hx, hx⟩⟩

end AutomorphicAction.IsEquivariant

namespace RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (a : characterLattice T) (j : C ⟶ G)
    (hj : (kernelCentralizer i a).IsRepresentedBy j)
    [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- The actual component inclusion intertwines both descended actions. -/
theorem kernelCentralizerIdentityQuotientAction_isEquivariant :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).IsEquivariant
      (quotientAction i a j hj) (identityComponentι C) :=
  kernelCentralizerIdentityQuotientAction_act_comp i hT a j hj

/-- The identity-limit functor on the whole centralizer is exactly the image
of that on its actual identity component. -/
theorem kernelCentralizerIdentityQuotientAction_unipotent_map :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent.map
        (identityComponentι C) = (quotientAction i a j hj).unipotent :=
  AutomorphicAction.IsEquivariant.unipotent_map_identityComponent
    (kernelCentralizerIdentityQuotientAction_isEquivariant i hT a j hj)

/-- The actual root functor is the image from the identity component, with the
original character and full scheme-theoretic kernel retained. -/
theorem kernelCentralizerIdentityQuotientAction_comparison
    (hjc : IsClosedSubgroup j) :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent.map
        (identityComponentι C ≫ j) = subgroup i a := by
  rw [← SubgroupFunctor.map_comp,
    kernelCentralizerIdentityQuotientAction_unipotent_map]
  exact (quotientActionComparison _ T G C i a j hj hjc).symm

/-- The canonical map from identity-limit points in the component to actual
root points, on an arbitrary test scheme. -/
def kernelCentralizerIdentityRootPointsMap
    (hjc : IsClosedSubgroup j) (U : Over (Spec (CommRingCat.of k))) :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent.carrier U →*
      (subgroup i a).carrier U where
  toFun x := ⟨x.val ≫ (identityComponentι C ≫ j).hom.hom, by
    rw [← kernelCentralizerIdentityQuotientAction_comparison i hT a j hj hjc]
    exact SubgroupFunctor.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val _)

/-- The actual inclusion identifies the two groups of points, without
connectedness or reducedness hypotheses on the test scheme. -/
def kernelCentralizerIdentityRootPointsEquiv
    (hjc : IsClosedSubgroup j) (U : Over (Spec (CommRingCat.of k))) :
    (kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent.carrier U ≃*
      (subgroup i a).carrier U := by
  have : Mono j.hom.hom := hj.1
  have : Mono (identityComponentι C ≫ j).hom.hom := by
    change Mono ((identityComponentι C).hom.hom ≫ j.hom.hom)
    infer_instance
  refine MulEquiv.ofBijective (kernelCentralizerIdentityRootPointsMap i hT a j hj hjc U)
    ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact (cancel_mono (identityComponentι C ≫ j).hom.hom).mp
      (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈
        ((kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent.map
          (identityComponentι C ≫ j)).carrier U := by
      rw [kernelCentralizerIdentityQuotientAction_comparison i hT a j hj hjc]
      exact x.property
    obtain ⟨y, hy, hyx⟩ := SubgroupFunctor.mem_map.mp hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

@[simp]
theorem kernelCentralizerIdentityRootPointsEquiv_apply
    (hjc : IsClosedSubgroup j) (U : Over (Spec (CommRingCat.of k)))
    (x : (kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent.carrier U) :
    (kernelCentralizerIdentityRootPointsEquiv i hT a j hj hjc U x : U ⟶ G.X) =
      x.val ≫ (identityComponentι C).hom.hom ≫ j.hom.hom := rfl

end RelativeRoot

end Langlands.GroupScheme
