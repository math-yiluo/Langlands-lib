import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.RepresentedAction

/-! # Automorphic actions on actual identity components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {k : Type u} [Field k]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (a : AutomorphicAction H G)

/-- The ambient action restricted to the identity component in the second variable. -/
def identityComponentActionHom : H.X ⊗ (identityComponent G).X ⟶ G.X :=
  (H.X ◁ (identityComponentι G).hom.hom) ≫ a.hom

theorem lift_identityComponentActionHom {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (g : T ⟶ (identityComponent G).X) :
    lift h g ≫ a.identityComponentActionHom =
      a.act h (g ≫ (identityComponentι G).hom.hom) := by
  rw [identityComponentActionHom, lift_whiskerLeft_assoc]
  rfl

/-- Every fibre of the projection from the action domain is connected and
contains a point whose image is the identity, so the action lands in `G⁰`. -/
theorem range_identityComponentActionHom_subset :
    Set.range a.identityComponentActionHom.left ⊆ IdentityComponent.identitySet G := by
  rintro _ ⟨z, rfl⟩
  let p : (H.X ⊗ (identityComponent G).X).left ⟶ H.X.left :=
    pullback.fst H.X.hom (identityComponent G).X.hom
  let s : H.X ⟶ H.X ⊗ (identityComponent G).X := lift (𝟙 _) 1
  have hF : _root_.IsConnected (p ⁻¹' {p z}) :=
    Scheme.Hom.isConnected_preimage_singleton p (p z)
  have hs : s ≫ a.identityComponentActionHom = 1 := by
    rw [lift_identityComponentActionHom, MonObj.one_comp, a.act_one]
  have hsz : s.left (p z) ∈ p ⁻¹' {p z} := by
    change (s ≫ fst _ _).left (p z) = p z
    rw [lift_fst]
    rfl
  have hconn : _root_.IsConnected
      (a.identityComponentActionHom.left '' (p ⁻¹' {p z})) :=
    hF.image _ a.identityComponentActionHom.left.continuous.continuousOn
  refine hconn.isPreconnected.subset_connectedComponent ⟨_, hsz, ?_⟩
    ⟨z, rfl, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs, CategoryTheory.Hom.one_def,
    Over.comp_left, Scheme.Hom.comp_apply, IdentityComponent.unit_left_apply]

/-- The actual identity-component subgroup is preserved by an arbitrary
group-scheme action by automorphisms, on every test scheme. -/
theorem isStable_range_identityComponentι :
    a.IsStable (SubgroupFunctor.range (identityComponentι G)) := by
  intro T h x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  refine SubgroupFunctor.mem_range.2
    ⟨FiniteEtaleImage.liftOver (identityComponentι G).hom.hom
      (lift h y ≫ a.identityComponentActionHom) ?_, ?_⟩
  · rw [IdentityComponent.range_identityComponentι]
    rintro _ ⟨t, rfl⟩
    exact a.range_identityComponentActionHom_subset
      ⟨(lift h y).left t, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rw [FiniteEtaleImage.liftOver_fac, lift_identityComponentActionHom]

/-- The induced actual automorphic action on the identity component. -/
def onIdentityComponent : AutomorphicAction H (identityComponent G) :=
  a.onRepresentedSubgroup (identityComponentι G) ⟨inferInstance, rfl⟩
    a.isStable_range_identityComponentι

/-- The actual identity-component inclusion intertwines both actions. -/
theorem onIdentityComponent_act_comp {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (g : T ⟶ (identityComponent G).X) :
    a.onIdentityComponent.act h g ≫ (identityComponentι G).hom.hom =
      a.act h (g ≫ (identityComponentι G).hom.hom) :=
  a.onRepresentedSubgroup_act_comp _ ⟨inferInstance, rfl⟩
    a.isStable_range_identityComponentι h g

section Represented

variable {C A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (b : AutomorphicAction H A) {F : SubgroupFunctor A}
    (i : C ⟶ A) (hi : F.IsRepresentedBy i) (hF : b.IsStable F)

include hi hF in
/-- An action preserving a smooth affine represented subgroup also preserves
the actual identity component of that subgroup inside the ambient group. -/
theorem isStable_range_identityComponent_comp :
    b.IsStable (SubgroupFunctor.range (identityComponentι C ≫ i)) := by
  intro T h x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hx
  let c := b.onRepresentedSubgroup i hi hF
  refine SubgroupFunctor.mem_range.2 ⟨c.onIdentityComponent.act h y, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, onIdentityComponent_act_comp,
    onRepresentedSubgroup_act_comp]
  rfl

/-- The actual action induced on the identity component of a stable
represented smooth affine subgroup. -/
def onRepresentedIdentityComponent : AutomorphicAction H (identityComponent C) :=
  (b.onRepresentedSubgroup i hi hF).onIdentityComponent

theorem onRepresentedIdentityComponent_act_comp
    {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (g : T ⟶ (identityComponent C).X) :
    (b.onRepresentedIdentityComponent i hi hF).act h g ≫
        (identityComponentι C ≫ i).hom.hom =
      b.act h (g ≫ (identityComponentι C ≫ i).hom.hom) := by
  rw [Grp.comp_hom_hom, ← Category.assoc, onRepresentedIdentityComponent,
    onIdentityComponent_act_comp, onRepresentedSubgroup_act_comp, Category.assoc]

end Represented

end Langlands.GroupScheme.AutomorphicAction
