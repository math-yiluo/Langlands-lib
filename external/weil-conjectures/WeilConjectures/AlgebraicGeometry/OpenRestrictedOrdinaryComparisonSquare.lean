/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingIsoNaturality
import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorCoordinateData

/-! # Open restriction of the comparison before the pullback counit

Source: Stacks Project, Tags 0DJ8 and 0098.
(blueprint: lem-pc-open-restricted-ordinary-comparison-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- Open restriction transports the comparison into ordinary tensor pullback.
There is no K-flatness assumption or inverse derived pullback counit in this square.

Proof: write j = U.ι, p = pullback.fst g' j and q = pullback.snd g' j.
The stalk maps of j at qz and p at z are ring isomorphisms. The pullback
condition identifies j(qz) with g'(pz). The equalities stalkMap_comp and
stalkMap_congr_hom identify the base stalk ring, the base-changed stalk ring,
and their algebra maps for the original and restricted squares. The natural
restriction-stalk map sends a restricted section germ to the same original
section germ and is semilinear for the inverse open stalk map. Apply it in
all degrees to the literal restricted complex. Transport the universal
left-derived base scalar extension through the exact ring equivalences.
Uniqueness with its universal counit identifies the two derived tensor
objects. Naturality of the A-action makes the cohomology identification
linear over the identified tensor algebras. Extend to the final stalk rings
and forget scalars to construct l and its inverse. The comparison_eq and
localized_eq equations of the two models identify their comparison maps
with the transported universal counit and its scalar-extension transpose.
Their naturality gives the square for localizedComparison. The same-germ
formula for tensorStalkIso identifies the ordinary tensor-pullback factors
with the adjunction-defined openTensorRestrictionComplexIso. Exact-stalk
homology and exact-restriction homology identify the target transport with
openDerivedStalkIso followed by openRestrictedTensorDerivedIso. Composing
these identities gives the stated equation. This uses no invertibility of
the horizontal comparison, no K-flatness or base flatness, and no bounds.
For an empty open no z exists; top opens, zero complexes and zero rings
satisfy the same functorial identities.
Source: Stacks Project, Tag 0DJ8, locality of equation-bc; Tag 0098, stalks
of pullback; Tag 0D5U, exact restriction; Tag 06Y6, derived tensor functoriality.
(blueprint: lem-pc-open-restricted-ordinary-comparison-square). -/
theorem exists_open_restricted_ordinary_comparison_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let Q := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    let a := F.map (comparisonIntoTensorPullback f f' g g' sq
      (pullback.fst g' U.ι z) P i)
    let b := FU.map (comparisonIntoTensorPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g (pullback.snd g' U.ι) sqU z Q i)
    ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
      a ≫ (openDerivedStalkIso (pullback.fst g' U.ι) z i).hom.app
          (DerivedCategory.Q.obj Pg) =
        l.hom ≫ b ≫ HU.map (openRestrictedTensorDerivedIso g' U P).inv := by
  let Q := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let PgU := ((Scheme.Modules.tensorPullback (pullback.snd g' U.ι)).mapHomologicalComplex
    (.up ℤ)).obj Q
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
    AddCommGrpCat.{u}
  let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z)) AddCommGrpCat.{u}
  let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
  let := leftAlgebra f g' (pullback.fst g' U.ι z)
  let := rightAlgebra f f' g g' sq (pullback.fst g' U.ι z)
  let := (tensorMap f f' g g' sq (pullback.fst g' U.ι z)).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' (pullback.fst g' U.ι z)))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' (pullback.fst g' U.ι z)))
  let := leftAlgebra (U.ι ≫ f) (pullback.snd g' U.ι) z
  let := rightAlgebra (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g (pullback.snd g' U.ι) sqU z
  let := (tensorMap (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g
    (pullback.snd g' U.ι) sqU z).toAlgebra
  let := HasDerivedCategory.standard
    (ModuleCat.{u} (R (U.ι ≫ f) (pullback.snd g' U.ι) z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B (pullback.fst g' U.ι ≫ f') z))
  let M := cohomologyModel f f' g g' sq (pullback.fst g' U.ι z) P
  let MU := cohomologyModel (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g
    (pullback.snd g' U.ι) sqU z Q
  let VU := tensorComplex (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g
    (pullback.snd g' U.ι) sqU z Q
  obtain ⟨eR, eA, eB, eD, q, t, hA, hB, hD, ht, htarget⟩ :=
    exists_openRestricted_tensor_coordinate_data f f' g g' sq U sqU z i P
  obtain ⟨l, hl⟩ := ModuleCat.exists_baseDerivedTensor_ringIso_square.{u, u + 1}
    eR eA eB eD hA hB hD (stalkComplex g' (pullback.fst g' U.ι z) P)
    (stalkComplex (pullback.snd g' U.ι) z Q) q M MU t ht i
  let c := F.mapIso ((VU.sc i).mapHomologyIso
    (ModuleCat.restrictScalars.{u} eD.toRingHom))
  let k := HomologicalComplex.homologyMap
      (tensorStalkIso f f' g g' sq (pullback.fst g' U.ι z) P).hom i ≫
    (comparisonStalkHomologyIso X' (pullback.fst g' U.ι z) Pg i).inv
  let kU := HomologicalComplex.homologyMap
      (tensorStalkIso (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g
        (pullback.snd g' U.ι) sqU z Q).hom i ≫
    (comparisonStalkHomologyIso (pullback g' U.ι) z PgU i).inv
  let j := (openDerivedStalkIso (pullback.fst g' U.ι) z i).hom.app
    (DerivedCategory.Q.obj Pg)
  let d := HU.mapIso (openRestrictedTensorDerivedIso g' U P)
  have hlocal : l.hom ≫ FU.map (MU.localizedComparison i) ≫ c.inv =
      F.map (M.localizedComparison i) ≫ F.map (HomologicalComplex.homologyMap t.hom i) := hl
  have hgeom : F.map (HomologicalComplex.homologyMap t.hom i) ≫ c.hom ≫ FU.map kU =
      F.map k ≫ j ≫ d.hom := htarget
  have h := congrArg (fun m ↦ m ≫ c.hom ≫ FU.map kU ≫ d.inv) hlocal
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  rw [reassoc_of% hgeom] at h
  simp only [Iso.hom_inv_id, Category.comp_id] at h
  refine ⟨l, ?_⟩
  change F.map (M.localizedComparison i ≫ k) ≫ j =
    l.hom ≫ FU.map (MU.localizedComparison i ≫ kU) ≫ d.inv
  simpa only [Functor.map_comp, Category.assoc] using h.symm

end AlgebraicGeometry.SingleComplexBaseChange
