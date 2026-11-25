/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-!
# Extension by zero on the small pro-etale site

We use the recorded extension-by-zero functor with fixed module coefficients. Its
termwise extension is Mathlib's `mapHomologicalComplex`. The scalar comparison is
specified as the mate of the identity on restricted sections, so its normalization
is fixed before invertibility is asserted.

## References

* Stacks Project, Tags 09AE, 03DI, 03DJ and 03CY
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The degreewise extension of the recorded `j_!`: terms are `j_!(K.X n)` and
its differentials are `j_!(K.d n m)`, including for unbounded complexes. -/
abbrev openExtensionCochain (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)

/-- Scalar restriction on fixed-module-valued sheaves is additive, section by section. -/
instance openExtensionScalarRestriction_additive {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    (sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ)).Additive :=
  sheafCompose_additive.{u, u + 1, u + 1, u + 1, u + 2, u + 2}
    (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ)

/-- The canonical map `j_!^A Res_U ⟶ Res_X j_!^B`, the mate of the identity-on-sections
scalar square along the two extension/restriction adjunctions. -/
def openExtensionScalarMap {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} φ) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} φ) :=
  ((mateEquiv
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)).symm
      (TwoSquare.mk _ _ _ _ (eqToHom (by rfl))))

private theorem scalarMap_isIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (openExtensionScalarMap φ j) := by
  have : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isRightAdjoint
  let aU := sheafComposeAdjunction (Scheme.ProEt.topology U)
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let aX := sheafComposeAdjunction (Scheme.ProEt.topology X)
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let aB := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j
  let aA := openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j
  let γ := TwoSquare.mk
    (sheafCompose (Scheme.ProEt.topology X)
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ))
    (openImmersionRestriction (ModuleCat.{u + 1} A) j)
    (openImmersionRestriction (ModuleCat.{u + 1} B) j)
    (sheafCompose (Scheme.ProEt.topology U)
      (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)) (eqToHom (by rfl))
  have hβ : (mateEquiv aX aU).symm γ =
      TwoSquare.mk (openImmersionRestriction (ModuleCat.{u + 1} B) j)
        (sheafCompose (Scheme.ProEt.topology X) (ModuleCat.restrictScalars φ))
        (sheafCompose (Scheme.ProEt.topology U) (ModuleCat.restrictScalars φ))
        (openImmersionRestriction (ModuleCat.{u + 1} A) j) (eqToHom (by rfl)) := by
    apply NatTrans.ext
    funext F
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (ModuleCat.restrictScalars φ).map
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).unit.app
          (F.obj.obj _)) ≫
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).counit.app _ = 𝟙 _
    exact (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).left_triangle_components _
  have h := iterated_mateEquiv_conjugateEquiv_symm aB aA aU aX γ
  rw [hβ] at h
  have hi : IsIso ((conjugateEquiv (aB.comp aX) (aU.comp aA)).symm γ) := by
    exact inferInstance
  change IsIso (((mateEquiv aB aA).symm
    (TwoSquare.mk _ _ _ _ (eqToHom (by rfl)))))
  rw [h]
  exact hi

end AlgebraicGeometry.ProEtale
