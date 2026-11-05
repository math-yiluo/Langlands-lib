import Langlands.GroupScheme.ReducedSubgroup
import Langlands.GroupScheme.IdentityComponentAction

/-! # Smooth actions on reduced subgroups and their identity components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {k : Type u} [Field k] [PerfectField k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [LocallyOfFiniteType G.X.hom]
    (a : AutomorphicAction H G)

/-- Smoothness of the acting group makes the universal action domain on the
reduced subgroup reduced, even though test schemes need not be reduced. -/
theorem isStable_range_reducedSubgroupι :
    a.IsStable (SubgroupFunctor.range (reducedSubgroupι G)) := by
  let : Smooth (H.X ⊗ (reducedSubgroup G).X).hom := by
    change Smooth (pullback.fst H.X.hom (reducedSubgroup G).X.hom ≫ H.X.hom)
    infer_instance
  let : IsReduced (H.X ⊗ (reducedSubgroup G).X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (H.X ⊗ (reducedSubgroup G).X).hom
  let f : H.X ⊗ (reducedSubgroup G).X ⟶ G.X :=
    (H.X ◁ (reducedSubgroupι G).hom.hom) ≫ a.hom
  let r := ReducedSubgroup.liftOver f
  have hr : r ≫ (reducedSubgroupι G).hom.hom = f :=
    ReducedSubgroup.liftOver_fac f
  intro T h x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2 ⟨lift h y ≫ r, ?_⟩
  rw [Category.assoc, hr]
  change lift h y ≫ ((H.X ◁ (reducedSubgroupι G).hom.hom) ≫ a.hom) = _
  rw [lift_whiskerLeft_assoc]
  rfl

/-- The actual action of a smooth group on the reduced subgroup. -/
def onReducedSubgroup : AutomorphicAction H (reducedSubgroup G) :=
  a.onRepresentedSubgroup (reducedSubgroupι G) ⟨Over.mono_of_mono_left _, rfl⟩
    a.isStable_range_reducedSubgroupι

/-- The reduced inclusion intertwines the actual actions on every test. -/
theorem onReducedSubgroup_act_comp {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (g : T ⟶ (reducedSubgroup G).X) :
    a.onReducedSubgroup.act h g ≫ (reducedSubgroupι G).hom.hom =
      a.act h (g ≫ (reducedSubgroupι G).hom.hom) :=
  a.onRepresentedSubgroup_act_comp _ ⟨Over.mono_of_mono_left _, rfl⟩
    a.isStable_range_reducedSubgroupι h g

variable [IsAffineHom G.X.hom]

/-- The actual action of a smooth group on the reduced identity component. -/
def onReducedIdentityComponent :
    AutomorphicAction H (identityComponent (reducedSubgroup G)) :=
  a.onReducedSubgroup.onIdentityComponent

/-- Equivariance of the reduced identity-component inclusion holds on all tests. -/
theorem onReducedIdentityComponent_act_comp
    {T : Over (Spec (CommRingCat.of k))} (h : T ⟶ H.X)
    (g : T ⟶ (identityComponent (reducedSubgroup G)).X) :
    a.onReducedIdentityComponent.act h g ≫
        (identityComponentι (reducedSubgroup G) ≫ reducedSubgroupι G).hom.hom =
      a.act h (g ≫
        (identityComponentι (reducedSubgroup G) ≫ reducedSubgroupι G).hom.hom) := by
  rw [Grp.comp_hom_hom, ← Category.assoc, onReducedIdentityComponent,
    onIdentityComponent_act_comp, onReducedSubgroup_act_comp, Category.assoc]

end AutomorphicAction

namespace ReducedSubgroup

variable {k : Type u} [Field k] [PerfectField k]
    (N : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType N.X.hom] [IsAffineHom N.X.hom]

/-- The smooth connected reduced identity component of an affine finite-type group. -/
abbrev identityCore : GroupScheme (Spec (CommRingCat.of k)) :=
  identityComponent (reducedSubgroup N)

/-- The actual closed inclusion of the reduced identity component. -/
def identityCoreι : identityCore N ⟶ N :=
  identityComponentι (reducedSubgroup N) ≫ reducedSubgroupι N

instance smooth_identityCore : Smooth (identityCore N).X.hom :=
  IdentityComponent.smooth_identityComponent _

instance connectedSpace_identityCore : ConnectedSpace (identityCore N).X.left :=
  IdentityComponent.connectedSpace_identityComponent _

instance isAffineHom_identityCore : IsAffineHom (identityCore N).X.hom :=
  IdentityComponent.isAffineHom_identityComponent _

instance isClosedImmersion_identityCoreι : IsClosedImmersion (identityCoreι N).hom.hom.left := by
  change IsClosedImmersion ((identityComponentι (reducedSubgroup N)).hom.hom.left ≫
    (reducedSubgroupι N).hom.hom.left)
  infer_instance

variable {N} {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] (i : N ⟶ G) (hi : IsClosedSubgroup i)

include hi in
/-- The reduced identity component of a normal closed subgroup of a smooth group
is normal as a subgroup functor on every test scheme. -/
theorem isNormal_range_identityCoreι_comp
    (hn : (SubgroupFunctor.range i).IsNormal) :
    (SubgroupFunctor.range (identityCoreι N ≫ i)).IsNormal := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  have hnorm : (SubgroupFunctor.range i).IsNormalizedBy (SubgroupFunctor.range (𝟙 G)) :=
    fun T g x _ hx => hn T g x (by trivial) hx
  let a := AutomorphicAction.ofNormalizedConjugation i (𝟙 G) hnorm
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2 ⟨a.onReducedIdentityComponent.act g y, ?_⟩
  change (a.onReducedIdentityComponent.act g y ≫ (identityCoreι N).hom.hom) ≫
    i.hom.hom = _
  dsimp only [identityCoreι]
  rw [AutomorphicAction.onReducedIdentityComponent_act_comp]
  change (lift g (y ≫ (identityCoreι N).hom.hom) ≫
    SubgroupFunctor.normalizedConjugation i (𝟙 G) hnorm) ≫ i.hom.hom = _
  rw [SubgroupFunctor.lift_comp_normalizedConjugation_comp]
  simp only [Grp.id_hom_hom, Category.comp_id, Grp.comp_hom_hom, identityCoreι,
    Category.assoc]

end ReducedSubgroup

end Langlands.GroupScheme
