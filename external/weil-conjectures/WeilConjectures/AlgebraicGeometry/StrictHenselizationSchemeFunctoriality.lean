/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension

/-!
# Functoriality of the strict henselization scheme

Source: Stacks Project, Tags 04GU and 03Q9.
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

private theorem fullStrictHenselizationCone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    let D := Functor.Elements.π (pointSmallEtale s).fiber ⋙
      Etale.forget S ⋙ Over.forget S
    ∃ π : (Functor.const _).obj (strictLocalization s) ⟶ D,
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      ∀ j, π.app j ≫ j.1.hom = strictLocalizationToBase s := by
  classical
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let Q := N ⋙ Functor.Elements.precomp (AffineEtale.Spec S) (pointSmallEtale s).fiber
  let D := Functor.Elements.π (pointSmallEtale s).fiber ⋙
    Etale.forget S ⋙ Over.forget S
  have : Q.Initial := (strictHenselizationAffineProperties s).1
  let A := Q ⋙ D
  have hAff (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      IsAffine (A.obj j) := by
    change IsAffine (Spec _)
    infer_instance
  let _ : ∀ j, IsAffine (A.obj j) := hAff
  let E := (opOpEquivalence
    (SmallModel.{u} (strictHenselizationNeighbourhoods s))).symm
  let cR := (strictHenselizationAffineCone s).whisker E.functor
  let α : A ⟶ E.functor ⋙ (strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec :=
    Functor.whiskerLeft A ΓSpec.adjunction.unit
  have hIso (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      IsIso (α.app j) := by
    let : IsAffine (A.obj j) := hAff j
    exact inferInstanceAs (IsIso (ΓSpec.adjunction.unit.app (A.obj j)))
  let : IsIso α := NatIso.isIso_of_isIso_app α
  let e := asIso α
  let c := (Cone.postcompose e.inv).obj cR
  have hc : IsLimit c :=
    (IsLimit.postcomposeInvEquiv e _).symm
      ((strictHenselizationAffineProperties s).2.2.some.whiskerEquivalence E)
  have hleg (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      c.π.app j = (strictHenselizationAffineCone s).π.app
        (Opposite.op (Opposite.op j)) ≫ Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv := by
    dsimp [c, cR]
    change _ ≫ (inv α).app j = _
    rw [NatIso.isIso_inv_app]
    change _ ≫ inv (A.obj j).toSpecΓ = _
    congr 1
    change (Spec _).isoSpec.inv = _
    exact isoSpec_Spec_inv _
  have hq (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      c.π.app j ≫ (Q.obj j).1.hom = strictLocalizationToBase s := by
    rw [hleg]
    exact strictHenselizationStructuralMap_eq s j
  let c' := (Functor.Initial.extendCone (F := Q) (G := D)).obj c
  refine ⟨c'.π, ⟨(Functor.Initial.isLimitExtendConeEquiv Q c).symm hc⟩, ?_⟩
  intro j
  change (c.π.app (Functor.Initial.lift Q j) ≫
    D.map (Functor.Initial.homToLift Q j)) ≫ j.1.hom = _
  rw [Category.assoc]
  change c.π.app (Functor.Initial.lift Q j) ≫
    (Functor.Initial.homToLift Q j).1.left ≫ j.1.hom = _
  rw [MorphismProperty.Over.w]
  exact hq _

private noncomputable def pointedPullback
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g) :
    (pointSmallEtale s).fiber.Elements ⥤ (pointSmallEtale t).fiber.Elements := by
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let α : (pointSmallEtale s).fiber ⟶ F ⋙ (pointSmallEtale t).fiber :=
    { app := fun j ↦ ↾(fun v : (pointSmallEtale s).fiber.obj j ↦ Over.homMk
        (pullback.lift v.left t (by exact (Over.w v).trans hst))
        (by simp [F, MorphismProperty.Over.pullback]))
      naturality := by
        intro j k a
        apply ConcreteCategory.ext
        apply TypeCat.Fun.ext
        funext v
        apply Over.OverMorphism.ext
        change pullback.lift (v.left ≫ a.left) t _ =
          pullback.lift v.left t _ ≫ pullback.lift
            (pullback.fst j.hom g ≫ a.left) (pullback.snd j.hom g) _
        apply pullback.hom_ext <;> simp [Category.assoc] }
  exact α.mapElements ⋙ Functor.Elements.precomp F (pointSmallEtale t).fiber

/-- Compatible geometric points admit a morphism of their strict henselization schemes
commuting with the structural maps. No assertion of locality is made here.
Source: Stacks Project, Tag 04GU; Tag 03Q9, inverse-limit description.
(blueprint: lem-weil-pbc-strict-henselization-scheme-functoriality)

Proof: pull back every pointed etale neighbourhood of s along g, pointing the pullback
by t and its compatible lift to the neighbourhood. The canonical cone of the strict
henselization at t extends to all pointed etale neighbourhoods because affine pointed
neighbourhoods are initial. Project its leg at each of these pullbacks to the original
neighbourhood of s. Pullback functoriality and cone naturality make these projections
a cone on the affine pointed-neighbourhood diagram at s. The limit property of the
canonical cone at s gives f. Each cone leg is a morphism over g: the pullback condition
and the structural-map characterization give the displayed equality after composition
with any leg at s. There is at least one such leg, since the index is cofiltered. -/
theorem exists_strictHenselizationSchemeMap
    {S T : Scheme.{u}} {g : T ⟶ S}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω) ⟶ T}
    (hst : s = t ≫ g) :
    ∃ f : strictLocalization t ⟶ strictLocalization s,
      f ≫ strictLocalizationToBase s =
        strictLocalizationToBase t ≫ g := by
  classical
  obtain ⟨πs, ⟨hs⟩, hqs⟩ := fullStrictHenselizationCone s
  obtain ⟨πt, _, hqt⟩ := fullStrictHenselizationCone t
  let PB := pointedPullback hst
  let D := Functor.Elements.π (pointSmallEtale s).fiber ⋙
    Etale.forget S ⋙ Over.forget S
  let π : (Functor.const _).obj (strictLocalization t) ⟶ D :=
    { app := fun j ↦ πt.app (PB.obj j) ≫ pullback.fst j.1.hom g
      naturality := by
        intro j k a
        simp only [Functor.const_obj_map]
        have hn := (Cone.mk _ πt).w (PB.map a)
        change πt.app (PB.obj j) ≫ (PB.map a).1.left = πt.app (PB.obj k) at hn
        have ha : (PB.map a).1.left ≫ pullback.fst k.1.hom g =
            pullback.fst j.1.hom g ≫ a.1.left := by
          change pullback.lift (pullback.fst j.1.hom g ≫ a.1.left)
            (pullback.snd j.1.hom g) _ ≫ pullback.fst k.1.hom g = _
          exact pullback.lift_fst _ _ _
        change πt.app (PB.obj k) ≫ pullback.fst k.1.hom g =
          (πt.app (PB.obj j) ≫ pullback.fst j.1.hom g) ≫ a.1.left
        rw [Category.assoc, ← ha, ← Category.assoc, hn] }
  let c := Cone.mk _ π
  let f := hs.lift c
  refine ⟨f, ?_⟩
  let j : (pointSmallEtale s).fiber.Elements :=
    Classical.choice (IsCofiltered.nonempty (C := (pointSmallEtale s).fiber.Elements))
  rw [← hqs j, ← Category.assoc, hs.fac c j]
  change (πt.app (PB.obj j) ≫ pullback.fst j.1.hom g) ≫ j.1.hom = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ g) (hqt (PB.obj j))

end AlgebraicGeometry.Scheme
