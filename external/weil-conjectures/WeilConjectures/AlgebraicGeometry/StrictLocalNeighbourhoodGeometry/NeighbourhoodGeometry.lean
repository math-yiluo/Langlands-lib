/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedFiberComparison

/-! # Canonical neighbourhood geometry on the small colimit model

Transport upstream's geometry along the canonical spectrum-colimit isomorphism.
Source: Stacks Project, Tag 03Q9, first proof paragraph.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- The canonical comparison of the two strict-local pullbacks, over X.
Source: Stacks Project, Tag 03Q9; final-functor colimit comparison.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport). -/
noncomputable def strictLocalSmallModelPullbackIso {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    pullback f (Scheme.strictHenselizationStructuralMap s) ≅
      pullback f (Scheme.strictLocalizationToBase s) :=
  asIso (pullback.map _ _ _ _ (𝟙 X)
    (Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv) (𝟙 S)
    (by simp) (by simpa using (Scheme.smallStrictHenselizationColimitIso_toBase s).symm))

namespace StrictLocalNeighbourhoodGeometry

/-- Upstream's legs expressed on the small coordinate-ring colimit model.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport). -/
noncomputable def smallModelLegs {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s) :
    (Functor.const (SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s))).obj
      (pullback f (Scheme.strictHenselizationStructuralMap s)) ⟶
        strictLocalNeighbourhoodDiagram f s :=
  (Cone.mk _ Q.legs).extend (strictLocalSmallModelPullbackIso f s).hom |>.π

/-- Transport preserves the limiting property of the cone.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: extend the upstream limiting cone along the pullback comparison isomorphism;
`Cone.extendIso` identifies it with the original limit cone. -/
noncomputable def smallModelIsLimit {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s) : IsLimit (Cone.mk _ Q.smallModelLegs) :=
  Q.isLimit.ofIsoLimit
    (Cone.extendIso (Cone.mk _ Q.legs) (strictLocalSmallModelPullbackIso f s).symm)

/-- The transported legs have the original projection to X.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: compose the upstream projection equation with the comparison and use the
first projection formula for the pullback map. -/
theorem smallModelOver {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ (strictLocalNeighbourhoodProjection f s).app i =
      pullback.fst f (Scheme.strictHenselizationStructuralMap s) := by
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.over]
  simp [strictLocalSmallModelPullbackIso]

/-- The transported base component is exactly the small-model colimit leg.
Source: Stacks Project, Tag 03Q9.
(blueprint: lem-weil-pbc-strict-local-small-model-geometry-transport).
Proof: the inverse final-functor colimit comparison preserves each coprojection.
Apply Spec, compose with the affine Gamma-Spec identification, then use the second
projection formula for the pullback comparison and the upstream first-component equation. -/
theorem smallModelFirst {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
      pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
        (Scheme.strictHenselizationCone s).π.app (op (op i)) ≫
          Spec.map (Scheme.ΓSpecIso
            ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              i).1.left.unop).inv := by
  classical
  let : HasColimit (AlgebraicGeometry.Scheme.strictHenselizationDiagram s) := inferInstance
  let rep := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse
  let incl := Scheme.strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := Scheme.strictHenselizationAffineInclusion_isEquivalence s
  have h := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (AlgebraicGeometry.Scheme.strictHenselizationDiagram s) (op i)
  change colimit.ι (AlgebraicGeometry.Scheme.strictHenselizationDiagram s)
      (op (incl.obj (rep.obj i))) ≫
    (Scheme.smallStrictHenselizationColimitIso s).inv =
      colimit.ι (Scheme.strictHenselizationAffineDiagram s) (op i) at h
  have hh := congrArg Spec.map h
  simp only [Spec.map_comp] at hh
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.first]
  simp only [strictLocalSmallModelPullbackIso, asIso_hom, pullback.map,
    Category.assoc, pullback.lift_snd_assoc]
  change pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
    Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv ≫
      Spec.map (colimit.ι (AlgebraicGeometry.Scheme.strictHenselizationDiagram s)
        (op (incl.obj (rep.obj i)))) ≫ _ = _
  simpa [Category.assoc, Scheme.strictHenselizationCone] using congrArg
    (fun k ↦ pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫ k ≫
      Spec.map (Scheme.ΓSpecIso (rep.obj i).1.left.unop).inv) hh

end StrictLocalNeighbourhoodGeometry
end AlgebraicGeometry.Etale
