/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData

import Mathlib.Tactic.CategoryTheory.Slice

/-! # Common counit transpose of the site/scalar direct-image composites

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-direct-image.proof.md, Formal properties and Finite rings paragraphs;
Stacks Tag 07A7, remark-base-change.
(blueprint: lem-sfb-etale-proetale-scalar-counit-transposes).

The comparisons and mates are the existing canonical constructions. The four helpers
below name only the displayed composites and their counit transpose. All categories
are ordinary uncompleted unbounded derived categories of constant-coefficient modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The composite U: scalar extension of beta_A, then the pro-etale scalar mate,
then direct image of delta_X.
Source: scalar-six direct-image proof, Formal properties and Finite rings paragraphs,
Stacks Tag 07A7 (blueprint: lem-sfb-etale-proetale-scalar-counit-transposes). -/
def scalarSiteDirectImageU
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule A X) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ⟶
      R(lowerStar (ModuleCat.{u + 1} B) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
          ((Etale.scalarExtension a X).obj J)) :=
  (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).map
      ((directImageComparisonAmbient A f).app J) ≫
    (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso a f).hom)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj J) ≫
    R(lowerStar (ModuleCat.{u + 1} B) f).map ((pbcComparisonReduction X a).hom.app J)

/-- The composite V: delta_Y, comparison inverse image of the etale scalar mate,
then beta_B.
Source: scalar-six direct-image proof, Formal properties and Finite rings paragraphs,
Stacks Tag 07A7 (blueprint: lem-sfb-etale-proetale-scalar-counit-transposes). -/
def scalarSiteDirectImageV
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule A X) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ⟶
      R(lowerStar (ModuleCat.{u + 1} B) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
          ((Etale.scalarExtension a X).obj J)) :=
  (pbcComparisonReduction Y a).hom.app
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
      ((Etale.scalarMate a f).app J) ≫
    (directImageComparisonAmbient B f).app ((Etale.scalarExtension a X).obj J)

/-- The counit transpose q-flat, for any map with the source and target of U and V.
Source: scalar-six direct-image proof, counit-transpose calculation, Stacks Tag 07A7
(blueprint: lem-sfb-etale-proetale-scalar-counit-transposes). -/
def scalarSiteCounitTranspose
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule A X)
    (q : (pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ⟶
      R(lowerStar (ModuleCat.{u + 1} B) f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
          ((Etale.scalarExtension a X).obj J))) :
    L(upperStar (ModuleCat.{u + 1} B) f).obj
        ((pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J))) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
        ((Etale.scalarExtension a X).obj J) :=
  L(upperStar (ModuleCat.{u + 1} B) f).map q ≫
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
        ((Etale.scalarExtension a X).obj J))

/-- The specified common normal form: p_B(delta_Y), then d_B, then C_X^B of
c^e followed by T_X^e of the etale A-counit.
Source: scalar-six direct-image proof, counit-transpose calculation, Stacks Tag 07A7
(blueprint: lem-sfb-etale-proetale-scalar-counit-transposes). -/
def scalarSiteCounitNormalForm
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule A X) :
    L(upperStar (ModuleCat.{u + 1} B) f).obj
        ((pbcFixedScalarExtension (Scheme.ProEt.topology Y) a).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J))) ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj
        ((Etale.scalarExtension a X).obj J) :=
  L(upperStar (ModuleCat.{u + 1} B) f).map
      ((pbcComparisonReduction Y a).hom.app
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ≫
    (directImageComparisonAmbientPullbackIso B f).hom.app
      ((Etale.scalarExtension a Y).obj
        (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
      ((Etale.scalarPullbackIso a f).hom.app
          (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
        (Etale.scalarExtension a X).map
          ((Etale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} A) f).counit.app J))

/-- Both counit transposes have the specified common normal form, assuming the cube
identity only at P = r_A J.
Source: blueprint main-20261015 scalar-six direct-image proof, Formal properties and
Finite rings paragraphs; Stacks Tag 07A7, remark-base-change
(blueprint: lem-sfb-etale-proetale-scalar-counit-transposes).

Proof, following the node's seven steps:
1. Put E = epsilon^e_A,J, K = C_X^A J, h = beta^A_J, D = delta_X,J.
   Expand U-flat. Naturality of the pro-etale B-counit moves s_B(D) past it.
   The mate-counit equation for gamma^p leaves D after T_X^p(epsilon^p_A,K),
   c^p at s_A K, and p_B T_Y^p(h).
2. Naturality of c^p moves h across c^p. The mate-counit equation for beta^A
   replaces p_A(h) followed by epsilon^p_A,K by d_A followed by C_X^A(E).
   Functoriality combines their images under T_X^p.
3. Naturality of delta_X moves C_X^A(E) past delta_X. Apply the assumed cube
   identity at P and combine the two adjacent images under C_X^B. This is
   precisely scalarSiteCounitNormalForm.
4. Expand V-flat. The mate-counit equation for beta^B replaces p_B(beta^B)
   followed by the B-counit with d_B followed by C_X^B of the etale B-counit.
5. Naturality of d_B at gamma^e_J moves that map across d_B. Combine the
   adjacent images under C_X^B.
6. The mate-counit equation for gamma^e replaces l_B(gamma^e_J) followed by
   the etale B-counit with c^e_P followed by T_X^e(E). This is the same normal form.
7. Every arrow lies in D(X_proet,B), so is B-linear. The calculation uses only
   functoriality, naturality, mate-counit identities and the assumed cube; no
   direct-image mate is inverted and no geometric or boundedness condition is used. -/
theorem etaleProEtale_scalar_counit_transposes
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Etale.DerivedCategoryModule A X)
    (_hCube :
      (scalarPullbackProEtaleIso a f).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ≫
        (pbcFixedScalarExtension (Scheme.ProEt.topology X) a).map
          ((directImageComparisonAmbientPullbackIso A f).hom.app
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ≫
        (pbcComparisonReduction X a).hom.app
          (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) =
      L(upperStar (ModuleCat.{u + 1} B) f).map
          ((pbcComparisonReduction Y a).hom.app
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ≫
        (directImageComparisonAmbientPullbackIso B f).hom.app
          ((Etale.scalarExtension a Y).obj
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J)) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
          ((Etale.scalarPullbackIso a f).hom.app
            (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj J))) :
    scalarSiteCounitTranspose a f J (scalarSiteDirectImageU a f J) =
        scalarSiteCounitNormalForm a f J ∧
      scalarSiteCounitTranspose a f J (scalarSiteDirectImageV a f J) =
        scalarSiteCounitNormalForm a f J := by
  let pA := L(upperStar (ModuleCat.{u + 1} A) f)
  let pB := L(upperStar (ModuleCat.{u + 1} B) f)
  let rA := R(Etale.lowerStar (ModuleCat.{u + 1} A) f)
  let sB := R(lowerStar (ModuleCat.{u + 1} B) f)
  let CA := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let CB := (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory
  let TX := pbcFixedScalarExtension (Scheme.ProEt.topology X) a
  let TY := pbcFixedScalarExtension (Scheme.ProEt.topology Y) a
  let EX := Etale.scalarExtension a X
  let dA := (directImageComparisonAmbientPullbackIso A f).hom
  let dB := (directImageComparisonAmbientPullbackIso B f).hom
  let cp := (scalarPullbackProEtaleIso a f).hom
  let ce := (Etale.scalarPullbackIso a f).hom
  let dx := (pbcComparisonReduction X a).hom
  let dy := (pbcComparisonReduction Y a).hom
  let bA := directImageComparisonAmbient A f
  let bB := directImageComparisonAmbient B f
  let gp := (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ cp))
  let ge := Etale.scalarMate a f
  let epA := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit
  let epB := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit
  let eeA := (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit
  let eeB := (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit
  have hbA : pA.map (bA.app J) ≫ epA.app (CA.obj J) =
      dA.app (rA.obj J) ≫ CA.map (eeA.app J) :=
    mateEquiv_counit
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ dA) J
  have hbB : pB.map (bB.app (EX.obj J)) ≫ epB.app (CB.obj (EX.obj J)) =
      dB.app _ ≫ CB.map (eeB.app (EX.obj J)) :=
    mateEquiv_counit
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (TwoSquare.mk _ _ _ _ dB) (EX.obj J)
  have hgp : pB.map (gp.app (CA.obj J)) ≫ epB.app (TX.obj (CA.obj J)) =
      cp.app _ ≫ TX.map (epA.app (CA.obj J)) :=
    mateEquiv_counit
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (TwoSquare.mk _ _ _ _ cp) (CA.obj J)
  have hge : L(Etale.upperStar (ModuleCat.{u + 1} B) f).map (ge.app J) ≫
      eeB.app (EX.obj J) = ce.app (rA.obj J) ≫ EX.map (eeA.app J) :=
    mateEquiv_counit
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (TwoSquare.mk _ _ _ _ ce) J
  change cp.app _ ≫ TX.map (dA.app _) ≫ dx.app _ =
    pB.map (dy.app _) ≫ dB.app _ ≫ CB.map (ce.app _) at _hCube
  constructor
  · change pB.map (TY.map (bA.app J) ≫ gp.app (CA.obj J) ≫
        sB.map (dx.app J)) ≫ epB.app _ =
      pB.map (dy.app _) ≫ dB.app _ ≫ CB.map (ce.app _ ≫ EX.map (eeA.app J))
    simp only [Functor.map_comp, Category.assoc]
    slice_lhs 3 4 => exact epB.naturality (dx.app J)
    slice_lhs 2 3 => exact hgp
    slice_lhs 1 2 => exact cp.naturality (bA.app J)
    simp only [Functor.comp_map, Category.assoc]
    slice_lhs 2 3 => rw [← TX.map_comp, hbA, TX.map_comp]
    slice_lhs 3 4 => exact dx.naturality (eeA.app J)
    slice_lhs 1 3 => exact _hCube
    simp only [Functor.comp_map, Category.assoc]
    rfl
  · change pB.map (dy.app _ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
          (ge.app J) ≫ bB.app (EX.obj J)) ≫ epB.app _ =
      pB.map (dy.app _) ≫ dB.app _ ≫ CB.map (ce.app _ ≫ EX.map (eeA.app J))
    simp only [Functor.map_comp, Category.assoc]
    rw [hbB]
    slice_lhs 2 3 => exact dB.naturality (ge.app J)
    simp only [Functor.comp_map, Category.assoc]
    slice_lhs 3 4 => rw [← CB.map_comp, hge]
    rw [CB.map_comp]
    rfl

end AlgebraicGeometry.ProEtale
