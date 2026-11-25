/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.CohomologyGerms
import WeilConjectures.AlgebraicGeometry.DerivedCohomologyGermIso

/-! # Canonical derived sections and strict-local cohomology germs

Source: Stacks Project, Tags 03Q8 and 03Q9. The derived Hom comparison is the
explicit free-abelian-sheaf construction used in AbelianHigherDirectImagePresheaf.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalCohomologySourceColimit.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical strict-local source cocone is colimiting.
Source: Stacks, Tags 03Q8 and 03Q9, first proof paragraph
(blueprint: lem-weil-pbc-strict-local-cohomology-source-colimit).

Proof: initiality of the small affine pointed representatives makes the restricted
presheaf germ cocone colimiting. The derived-sections-to-homology-sheaf map induces
an isomorphism on stalks. Compose it with the strict-local germ restriction and the
exact-inverse-image homology isomorphism. Transport the germ cocone through this
composite isomorphism; its legs are exactly the displayed canonical source legs. -/
theorem smallModel_isColimit_strictLocalCohomologySourceLegs {S : Scheme.{v}}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (IsColimit (Cocone.mk _ (smallModel_strictLocalCohomologySourceLegs s L n))) := by
  let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun q : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine q.1.left)
  have : N.Initial := (Scheme.strictHenselization_properties s).1
  let P := strictLocalCohomologyPresheaf L n
  let c := ((Scheme.pointSmallEtale s).presheafFiberCocone P).whisker N.op
  have hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P)
  let u := (Scheme.pointSmallEtale s).presheafFiber.map
    (strictLocalCohomologyGermMap L n) ≫ (smallModel_strictLocalCohomologySourceIso s L n).hom
  have := isIso_strictLocalCohomologyGermMap s L n
  have : IsIso u := by dsimp [u]; infer_instance
  refine ⟨hc.ofIsoColimit (Cocone.ext (asIso u) (fun j ↦ ?_))⟩
  exact (Category.assoc _ _ _).symm

end AlgebraicGeometry.Etale
