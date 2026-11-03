import Langlands.GroupScheme.Rational.RootKernelIdentityComparison

/-! # Intrinsic root functors in the full-kernel identity component -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section DescendedAction

variable {B : Scheme.{u}} {S : CommGroupScheme B} {H : GroupScheme B}
    (i : S.toGrp ⟶ H) (a : characterLattice S)
    (b : AutomorphicAction (Gm B).toGrp H)
    (hb : b.restrict (CommGroupScheme.groupHom a) = AutomorphicAction.conjugation i)

include hb

/-- The orbit of an actual descended action pulls back to torus conjugation. -/
theorem whiskerLeft_descendedAction_orbit {U : Over B} (g : U ⟶ H.X) :
    U ◁ (CommGroupScheme.groupHom a).hom.hom ≫ b.orbit g = orbit i g := by
  rw [AutomorphicAction.orbit, AutomorphicAction.naturality,
    whiskerLeft_snd, whiskerLeft_fst_assoc]
  rw [← AutomorphicAction.restrict_act, hb]
  rfl

variable [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]

/-- The same actual affine-line family extends either orbit, because equality
can be checked after locally lifting the acting point through the character. -/
theorem isOrbitExtension_iff_descendedAction {U : Over B} (g : U ⟶ H.X)
    (e : U ⊗ AffineLine.scheme B ⟶ H.X) :
    IsOrbitExtension i a g e ↔ b.IsOrbitExtension g e := by
  constructor
  · intro he
    apply AutomorphicAction.hom_ext_of_local_quotient_lift
      (CommGroupScheme.groupHom a) (snd U (Gm B).X)
    intro V d s hs
    have hd : ∀ {Y : Over B} (f : U ⊗ (Gm B).X ⟶ Y),
        d ≫ f = lift (d ≫ fst U (Gm B).X) s ≫
          U ◁ (CommGroupScheme.groupHom a).hom.hom ≫ f := by
      intro Y f
      rw [← Category.assoc]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp [hs]
    rw [hd (U ◁ AffineLine.unitInclusion B ≫ e), hd (b.orbit g)]
    congr 1
    rw [← Category.assoc, ← whiskerLeft_comp, he,
      whiskerLeft_descendedAction_orbit i a b hb]
  · intro he
    rw [IsOrbitExtension, whiskerLeft_comp, Category.assoc, he,
      whiskerLeft_descendedAction_orbit i a b hb]

/-- A descended conjugation action has exactly the intrinsic root functor as
its identity-limit functor on every test scheme. -/
theorem subgroup_eq_unipotent_of_restrict :
    subgroup i a = b.unipotent := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨e, he, he0⟩
    exact ⟨e, (isOrbitExtension_iff_descendedAction i a b hb g e).mp he, he0⟩
  · rintro ⟨e, he, he0⟩
    exact ⟨e, (isOrbitExtension_iff_descendedAction i a b hb g e).mpr he, he0⟩

end DescendedAction

section IdentityComponent

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

/-- The root functor defined intrinsically by the lifted torus is precisely the
identity-limit functor of the actual descended component action. -/
theorem kernelCentralizerIdentity_subgroup_eq_unipotent :
    subgroup (kernelCentralizerIdentityTorus i hT a j hj) a =
      (kernelCentralizerIdentityQuotientAction i hT a j hj).unipotent :=
  subgroup_eq_unipotent_of_restrict _ a _
    (kernelCentralizerIdentityQuotientAction_restrict i hT a j hj)

/-- Computing the root subgroup inside the actual identity component and then
including it in the ambient group recovers the original actual root functor. -/
theorem kernelCentralizerIdentity_subgroup_map (hjc : IsClosedSubgroup j) :
    (subgroup (kernelCentralizerIdentityTorus i hT a j hj) a).map
        (identityComponentι C ≫ j) = subgroup i a := by
  rw [kernelCentralizerIdentity_subgroup_eq_unipotent]
  exact kernelCentralizerIdentityQuotientAction_comparison i hT a j hj hjc

/-- Intrinsically defined root points inside the actual identity component
are the original root points on every test scheme. -/
def kernelCentralizerIdentityIntrinsicRootPointsEquiv
    (hjc : IsClosedSubgroup j) (U : Over (Spec (CommRingCat.of k))) :
    (subgroup (kernelCentralizerIdentityTorus i hT a j hj) a).carrier U ≃*
      (subgroup i a).carrier U :=
  (MulEquiv.subgroupCongr (congrArg (fun F : SubgroupFunctor (identityComponent C) =>
    F.carrier U) (kernelCentralizerIdentity_subgroup_eq_unipotent i hT a j hj))).trans
      (kernelCentralizerIdentityRootPointsEquiv i hT a j hj hjc U)

@[simp]
theorem kernelCentralizerIdentityIntrinsicRootPointsEquiv_apply
    (hjc : IsClosedSubgroup j) (U : Over (Spec (CommRingCat.of k)))
    (x : (subgroup (kernelCentralizerIdentityTorus i hT a j hj) a).carrier U) :
    (kernelCentralizerIdentityIntrinsicRootPointsEquiv i hT a j hj hjc U x :
        U ⟶ G.X) = x.val ≫ (identityComponentι C).hom.hom ≫ j.hom.hom := rfl

end IdentityComponent

end Langlands.GroupScheme.RelativeRoot
