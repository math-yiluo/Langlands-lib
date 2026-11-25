/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-!
# Coefficient conversion and the extension-by-zero counit

Source: Stacks Project, Lemma 095L (lemma-ses-associated-to-open), the counit arrow,
and Lemma 0GJA (lemma-restrict-to-open), the coefficient convention in its application.
(blueprint: lem-pbc-n2-lower-shriek-coefficient-counit).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient conversion identifies the two extension-by-zero objects and their counits.
Source: Stacks Project, Lemma 095L (lemma-ses-associated-to-open), the first arrow of
its sequence; Lemma 0GJA (lemma-restrict-to-open), its use of that arrow.
(blueprint: lem-pbc-n2-lower-shriek-coefficient-counit).

Proof: The forgetful equivalence from integer modules to abelian groups and the ring
isomorphism ULift Z -> Z give an equivalence E of coefficient categories. Applied
objectwise it gives equivalences of sheaf categories, with inverse obtained by forgetting
scalars and the unit and counit obtained objectwise. Restriction along the localization
functor of the open immersion is precomposition, so it commutes with E. Identify upperStar
with this restriction using upperStarIsoOpenImmersionRestriction. Transport the abelian
adjunction j_! ⊣ j^* through these equivalences. Its right adjoint is then the module
upperStar, and uniqueness of left adjoints gives the displayed isomorphism e. Choose the
isomorphism supplied by the adjunction comparison, rather than an arbitrary isomorphism.
Compatibility of the counits of the two adjunctions says precisely that e.hom followed
by the converted abelian counit equals the module counit. The construction requires no
curve, density, constructibility, or torsion hypotheses. For an empty open both lower
shriek objects are zero; for the whole scheme both counits are isomorphisms, and the same
adjunction comparison applies in both cases. -/
theorem exists_lowerShriek_coefficient_counit {X : Scheme.{u}}
    (U : X.Opens) (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let T := sheafCompose X.smallEtaleTopology E
    ∃ e : (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).obj (T.obj A)) ≅
      T.obj ((openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
        ((upperStar AddCommGrpCat.{u + 1} U.ι).obj A)),
      e.hom ≫ T.map
          ((openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} U.ι).counit.app A)
        = (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).counit.app (T.obj A) := by
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let TX := sheafCompose X.smallEtaleTopology E
  let TU := sheafCompose U.toScheme.smallEtaleTopology E
  have : E.IsEquivalence := inferInstance
  have : TX.IsEquivalence := isEquivalence_sheafCompose_of_isEquivalence _ E
  have : TU.IsEquivalence := isEquivalence_sheafCompose_of_isEquivalence _ E
  let SX := sheafCompose X.smallEtaleTopology E.inv
  let SU := sheafCompose U.toScheme.smallEtaleTopology E.inv
  let ax := (E.adjunction.whiskerRight X.Etaleᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (L := TX) (R := SX) (Iso.refl _) (Iso.refl _)
  let au := (E.adjunction.whiskerRight U.toScheme.Etaleᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (L := TU) (R := SU) (Iso.refl _) (Iso.refl _)
  let a₁ := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).comp au
  let a₂ := ax.comp (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι)
  let r : upperStar AddCommGrpCat.{u + 1} U.ι ⋙ TU ≅
      TX ⋙ upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι :=
    (conjugateIsoEquiv a₂ a₁).symm (Iso.refl _)
  let b₁ := openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} U.ι
  let b₂ := openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι
  let m := (mateEquiv b₁ b₂).symm r.hom
  have : IsIso m := isIso_inverseMate_of_equivalences b₁ b₂ r
  let e := (openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).mapIso (r.app A).symm ≪≫
      (asIso m).app ((upperStar AddCommGrpCat.{u + 1} U.ι).obj A)
  refine ⟨e, ?_⟩
  change _ ≫ TX.map (b₁.counit.app A) = b₂.counit.app (TX.obj A)
  change (openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι).map (r.inv.app A) ≫
    m.app ((upperStar AddCommGrpCat.{u + 1} U.ι).obj A) ≫
    TX.map (b₁.counit.app A) = b₂.counit.app (TX.obj A)
  rw [← mateEquiv_counit_symm b₁ b₂ r.hom A,
    ← Functor.map_comp_assoc]
  simp

end AlgebraicGeometry.Etale
