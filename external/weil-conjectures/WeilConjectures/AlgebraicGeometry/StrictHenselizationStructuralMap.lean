/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# The structural morphism of the strict henselization

The strict henselization `S_(s)` of a scheme `S` at a geometric point `s` maps to `S` through
every affine pointed étale neighbourhood; this module names that canonical morphism.

Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- There is a morphism `S_(s) ⟶ S` equal, for every representative affine pointed
neighbourhood `(V, v)`, to the limit leg `S_(s) ⟶ Spec Γ(V, ⊤)`, followed by the
identification `Spec Γ(V, ⊤) ≅ V` and the structure morphism `V ⟶ S`.
Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map).

Proof: the representative category is cofiltered (`strictHenselization_properties`), hence
nonempty and connected. The legs of `strictHenselizationCone s` commute with the transition
maps, which are pointed morphisms over `S`, so the composites with the structure morphisms
agree along every arrow, hence for every pair of objects; take their common value. -/
theorem exists_strictHenselizationStructuralMap
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ∃ ρ : strictHenselizationScheme s ⟶ S,
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
            Spec.map (ΓSpecIso
              (((equivSmallModel.{u}
                (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop)).inv ≫
            ((AffineEtale.Spec S).obj
              (((equivSmallModel.{u}
                (strictHenselizationNeighbourhoods s)).inverse.obj j).1)).hom =
          ρ := by
  classical
  let := (strictHenselization_properties s).2.1
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let F : SmallModel.{u} (strictHenselizationNeighbourhoods s) →
      (strictHenselizationScheme s ⟶ S) := fun j ↦
    (strictHenselizationCone s).π.app (Opposite.op (Opposite.op j)) ≫
      Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv ≫
      ((AffineEtale.Spec S).obj (N.obj j).1).hom
  have hF {i j : SmallModel.{u} (strictHenselizationNeighbourhoods s)} (f : i ⟶ j) :
      F i = F j := by
    have h := (strictHenselizationCone s).w (f.op.op)
    dsimp [F]
    let g := (N.map f).1.left.unop
    change (strictHenselizationCone s).π.app (Opposite.op (Opposite.op i)) ≫
      Spec.map (Spec.map g).appTop = _ at h
    have hg := congrArg Spec.map (ΓSpecIso_inv_naturality g)
    simp only [Spec.map_comp] at hg
    have hw : Spec.map g ≫ ((AffineEtale.Spec S).obj (N.obj j).1).hom =
        ((AffineEtale.Spec S).obj (N.obj i).1).hom :=
      (N.map f).1.w
    have hg' := congrArg
      (fun t ↦ (strictHenselizationCone s).π.app (Opposite.op (Opposite.op i)) ≫
        t ≫ ((AffineEtale.Spec S).obj (N.obj j).1).hom) hg
    have hh := congrArg (fun t ↦ t ≫ Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv ≫
      ((AffineEtale.Spec S).obj (N.obj j).1).hom) h
    simp only [Category.assoc, hw] at hg'
    simp only [Category.assoc] at hh
    exact hg'.trans hh
  let j₀ := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  refine ⟨F j₀, fun j ↦ ?_⟩
  exact (hF (IsCofiltered.minToLeft j j₀)).symm.trans
    (hF (IsCofiltered.minToRight j j₀))

/-- The structural morphism `S_(s) ⟶ S` of the strict henselization at a geometric point:
the common composite of the limit legs with the neighbourhood structure morphisms,
characterized by `exists_strictHenselizationStructuralMap`.
Source: Stacks Project, Tag 03Q9, proof
(blueprint: def-weil-pbc-strict-henselization-structural-map). -/
noncomputable def strictHenselizationStructuralMap
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : strictHenselizationScheme s ⟶ S :=
  Classical.choose (exists_strictHenselizationStructuralMap s)

end AlgebraicGeometry.Scheme
