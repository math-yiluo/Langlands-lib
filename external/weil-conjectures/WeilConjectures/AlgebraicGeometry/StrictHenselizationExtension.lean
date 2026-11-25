/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselization


public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Strict henselization from affine pointed neighbourhoods

Source: Weil conjectures blueprint, `sec-curve-estimates/lem-sc-second-kummer-divisors`, definition
`def-weil-pbc-strict-henselization-limit` (blueprint: def-weil-pbc-strict-henselization-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme













/-- Canonical comparison from the small ring-written diagram to upstream's affine diagram. -/
noncomputable def smallStrictHenselizationColimitIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    colimit (strictHenselizationAffineDiagram s) ≅ strictHenselization s := by
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact Functor.Final.colimitIso F.op (strictHenselizationDiagram s)

/-- The small affine diagram's cocone with upstream's strict henselization as vertex. -/
noncomputable def smallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cocone (strictHenselizationAffineDiagram s) :=
  (colimit.cocone (strictHenselizationDiagram s)).whisker
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s).op

noncomputable def isColimitSmallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsColimit (smallStrictHenselizationCocone s) := by
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact (Functor.Final.isColimitWhiskerEquiv F.op _).symm
    (colimit.isColimit (strictHenselizationDiagram s))



/-- The canonical cone has vertex the strict henselization scheme; its legs are
`Spec.map` of the coordinate-ring colimit coprojections.
Source: blueprint `sec-curve-estimates/lem-sc-second-kummer-divisors`, definition of strict
henselization (blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def strictHenselizationAffineCone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Cone ((strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone (smallStrictHenselizationCocone s).op

/-- Cofilteredness and the inverse-limit interpretation of the canonical cone.
Source: blueprint `sec-curve-estimates/lem-sc-second-kummer-divisors`, definition of strict
henselization (blueprint: def-weil-pbc-strict-henselization-limit).

Proof: the affine pointed category is equivalent to the full affine subcategory of
pointed neighbourhoods, using the affine scheme--ring anti-equivalence. That full
subcategory is initial by `lemma-weil-pbc-affine-neighbourhood-cofinal`. The ambient
category is cofiltered by `definition-torsion-sheaves--3`;
`lem-weil-pbc-colimit-initial-full-subcategory` transfers cofilteredness to the affine
subcategory and then to the small representative model.
The opposite of the ring colimit cocone is a limit cone. The spectrum functor is a
right adjoint (`Spec.reflective`), hence carries this cone to a limit cone of schemes.
Its legs are exactly the spectra of the colimit coprojections
(`lem-weil-pbc-spec-small-colimit-limit`). The affine scheme--ring equivalence identifies
each spectrum of global sections with its original affine neighbourhood; transport
along the representative functor `(equivSmallModel _).inverse ⋙
strictHenselizationAffineInclusion s`, an equivalence by
`strictHenselizationAffineInclusion_isEquivalence`, gives the inverse limit over all
affine pointed neighbourhoods. -/
theorem strictHenselizationAffineProperties
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    Functor.Initial ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (pointSmallEtale s).fiber.Elements => IsAffine n.1.left)) ∧
      IsCofiltered (SmallModel.{u} (strictHenselizationNeighbourhoods s)) ∧
      Nonempty (IsLimit (strictHenselizationAffineCone s)) := by
  classical
  have := strictHenselizationAffineInclusion_isEquivalence s
  have : (ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)).Initial :=
    AffinePointedEtaleNeighborhood.initial_ι s
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (pointSmallEtale s).fiber.Elements => IsAffine n.1.left)
  have : F.Initial := by dsimp [F]; infer_instance
  refine ⟨this, ?_, ?_⟩
  · apply IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful F
    intro X
    obtain ⟨Y⟩ := (inferInstance : Nonempty (CostructuredArrow F X))
    exact ⟨Y.left, ⟨Y.hom⟩⟩
  · exact ⟨isLimitOfPreserves Scheme.Spec
      (isColimitSmallStrictHenselizationCocone s).op⟩

/-- Independence of the representative category, via the canonical colimit map.
Here `e` describes a replacement of the chosen representative category and `w`
identifies its coordinate-ring diagram with the transported chosen diagram.
Source: blueprint `sec-curve-estimates/lem-sc-second-kummer-divisors`, definition of strict
henselization (blueprint: def-weil-pbc-strict-henselization-limit).
The equivalence-colimit isomorphism has coprojection formula
`ι k ≫ iso.hom = D.map (e.unit.app k) ≫ w.inv.app _ ≫ ι _`
(`HasColimit.ι_isoOfEquivalence_hom`), so this is the canonical comparison.
It is an isomorphism by the equivalence-colimit lemma cited in the node. -/
noncomputable def strictHenselizationAffineRepresentativeIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {J : Type u} [SmallCategory J]
    (e : J ≌ (SmallModel.{u} (strictHenselizationNeighbourhoods s))ᵒᵖ)
    (D : J ⥤ CommRingCat.{u}) (w : e.functor ⋙ strictHenselizationAffineDiagram s ≅ D) :
    colimit D ≅ strictHenselization s :=
  HasColimit.isoOfEquivalence e w ≪≫ smallStrictHenselizationColimitIso s

end AlgebraicGeometry.Scheme
