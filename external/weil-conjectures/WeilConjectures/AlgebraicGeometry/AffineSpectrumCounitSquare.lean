/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare

/-! # The affine spectrum derived counit square

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-counit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private theorem isoPullbackComplexCounitIso_hom_app
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    (isoPullbackComplexCounitIso j).hom.app P =
      (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  change (derivedPullback j).map (𝟙 _) ≫
    (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [(derivedPullback j).map_id, DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]

private theorem affine_counit_inverse_square
    {C : Type*} [Category C] {A B C₀ D E F : C}
    (e : A ≅ B) (c : B ≅ C₀) (a : C₀ ≅ D)
    (d : A ≅ E) (b : E ≅ F) (f : F ≅ D)
    (ε : A ⟶ B) (φ : F ⟶ D) (he : e.hom = ε) (hf : f.hom = φ)
    (h : ε ≫ c.hom ≫ a.hom = d.hom ≫ b.hom ≫ φ) :
    b.inv ≫ d.inv = f.hom ≫ a.inv ≫ c.inv ≫ e.inv := by
  rw [← he, ← hf] at h
  apply (cancel_mono (d.hom ≫ b.hom ≫ f.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse pullback counits commute with the canonical affine coordinate comparison.
This is an equation of derived morphisms, independent of f, g, z0 and stalk cohomology.

Proof: let Pg be the termwise gprime-pullback of P and P0 the termwise isoSpec
pullback. Apply affineSpectrum_representative_map_eq with K=Q(P), Kprime=Q(Pg),
coefficient the pinned gprime counit, and Coordinates given by P, Pg, identity
representative isomorphisms and identity chain map. K-flatness is hP and represents
reduces to functoriality of identity. Choose e and eprime to be the inverse exact
iso-pullback complex counits. Their two defining equations are the explicit
quotientCompQhIso and mapHomotopyCategoryFactors formulas; the latter comparison
is identity on each complex. The resulting equation says spectrum counit followed
by Q(alpha.hom) followed by eprime.hom equals derived spectrum pullback of e.hom,
followed by the canonical derived composition comparison, followed by derived
isoSpec pullback of the gprime counit. Cancel the composition comparison and the
last counit. All four counits and alpha are invertible, so composing with their
inverses gives exactly the displayed equation. No stalk-ring comparison, localized
base-derived tensor map, coefficient to an arbitrary target, or point is involved.
For identity coordinate maps this is the identity composition law; zero complexes
and empty schemes use the same counit equations.
Source: Stacks Project, Tag 0D5S, lemma-pullback-composition; Tag 0DJ8, affine
reduction on the canonical representative.
(blueprint: lem-pc-affine-spectrum-counit-square). -/
theorem affineSpectrum_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X'] (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit (Spec.map g'.appTop)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
          (.up ℤ)).obj P)))) :
    let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    (derivedPullback X'.isoSpec.inv).map
        (cast (by rfl)
          (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
          DerivedCategory.Q.obj Pg ⟶ (derivedPullback g').obj (DerivedCategory.Q.obj P)) ≫
      (affineSpectrumDerivedPullbackIso g').inv.app (DerivedCategory.Q.obj P) =
    (isoPullbackComplexCounitIso X'.isoSpec.inv).hom.app Pg ≫
      DerivedCategory.Q.map (affineSpectrumTensorComplexIso g' P).inv ≫
      cast (by rfl) (inv ((counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P0))) ≫
      (derivedPullback (Spec.map g'.appTop)).map
        ((isoPullbackComplexCounitIso X.isoSpec.inv).inv.app P) := by
  have _hFlat := hP
  let := hcP
  let := hcQ
  dsimp only
  let e := (derivedPullback (Spec.map g'.appTop)).mapIso
    ((isoPullbackComplexCounitIso X.isoSpec.inv).app P)
  let c := asIso ((counit (Spec.map g'.appTop)).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex (.up ℤ)).obj P)))
  let a := DerivedCategory.Q.mapIso (affineSpectrumTensorComplexIso g' P)
  let d := (affineSpectrumDerivedPullbackIso g').app (DerivedCategory.Q.obj P)
  let b := (derivedPullback X'.isoSpec.inv).mapIso (asIso
    ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
  let f := (isoPullbackComplexCounitIso X'.isoSpec.inv).app
    (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
  change b.inv ≫ d.inv = f.hom ≫ a.inv ≫ c.inv ≫ e.inv
  exact affine_counit_inverse_square e c a d b f _ _
    (congrArg (derivedPullback (Spec.map g'.appTop)).map
      (isoPullbackComplexCounitIso_hom_app X.isoSpec.inv P))
    (isoPullbackComplexCounitIso_hom_app X'.isoSpec.inv
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P))
    (affineSpectrum_composition_counit_square g' P)

end AlgebraicGeometry.SingleComplexBaseChange
