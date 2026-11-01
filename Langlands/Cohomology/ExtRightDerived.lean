import Langlands.Cohomology.DerivedPlus
import Langlands.Cohomology.LeftExactHomology
import Langlands.Cohomology.SmoothExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Linear.Yoneda

/-!
# Ext as right derived functors of Hom

For objects `X` and `Y` of an abelian category `C` with injective resolutions,
Mathlib's `Abelian.Ext X Y n` (morphisms in the derived category) is identified,
as an abelian group, with the `n`-th right derived functor of Hom out of `X`,
evaluated at `Y`.

* `coyonedaHomComplexIso`, `coyonedaHomologyAddEquiv`: Hom out of `X` applied
  termwise to a cochain complex `L` is the Hom complex from `X` placed in degree
  zero to `L`; its cohomology is the group of cohomology classes.
* `resolutionHomologyIso`, `extAddEquivHomology`: for an injective resolution
  `R` of `Y`, `Ext X Y n` is the degree `n` cohomology of Hom out of `X` into
  `R.cocomplex`.
* `extAddEquivRightDerived`: `Ext X Y n ≃+ ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y`.
* `linearRightDerivedIso`, `extAddEquivLinearRightDerived`: the same for
  `S`-linear Hom, after forgetting the `S`-module structure.
* `hasExt_smoothRep`, `smoothExtAddEquiv`: for smooth representations, Mathlib's
  `Ext` exists in the universe of the representations, and `SmoothExt.ext` is
  Mathlib's `Ext` in the abelian category of smooth representations.

All comparisons are additive equivalences; no linearity over `S` and no
naturality in `X` or `Y` is stated.
-/

noncomputable section

namespace Langlands.Cohomology.ExtRightDerived

open CategoryTheory CategoryTheory.Limits Opposite Abelian
open CochainComplex HomComplex

universe w v u

section HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Hom out of `X` applied termwise to `L` is the Hom complex from `X` placed in
degree zero to `L`. -/
def coyonedaHomComplexIso (X : C) (L : CochainComplex C ℤ) :
    ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅
      HomComplex ((CochainComplex.singleFunctor C 0).obj X) L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (X := X) (K := L) (zero_add n)).symm.toAddCommGrpIso)
    (fun i j _ => by
      ext f
      exact Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j))

/-- The cohomology of Hom out of `X` into `L` is the group of cohomology classes
from `X` placed in degree zero to `L`. -/
def coyonedaHomologyAddEquiv (X : C) (L : CochainComplex C ℤ) (n : ℤ) :
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      L).homology n ≃+ CohomologyClass ((CochainComplex.singleFunctor C 0).obj X) L n :=
  (HomologicalComplex.homologyMapIso (coyonedaHomComplexIso X L) n).addCommGroupIsoToAddEquiv.trans
    (HomComplex.homologyAddEquiv _ _ n)

end HomComplex

section Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cohomology of Hom into the integer-indexed complex of an injective
resolution is the cohomology of Hom into the resolution itself. -/
def resolutionHomologyIso (X : C) {Y : C} (R : InjectiveResolution Y) (n : ℕ) :
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      R.cochainComplex).homology n ≅
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      R.cocomplex).homology n :=
  HomologicalComplex.homologyMapIso (DerivedPlus.mapExtendIso (preadditiveCoyoneda.obj (op X))
    R.cocomplex ComplexShape.embeddingUpNat).symm n ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat rfl

variable [HasExt.{w} C]

/-- `Ext X Y n` is the cohomology of Hom out of `X` into any injective resolution
of `Y`. -/
def extAddEquivHomology (X : C) {Y : C} (R : InjectiveResolution Y) (n : ℕ) :
    Ext.{w} X Y n ≃+
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        R.cocomplex).homology n :=
  (R.extAddEquivCohomologyClass (X := X) (n := n)).trans
    ((coyonedaHomologyAddEquiv X R.cochainComplex n).symm.trans
      (resolutionHomologyIso X R n).addCommGroupIsoToAddEquiv)

variable [HasInjectiveResolutions C]

/-- `Ext X Y n` is the `n`-th right derived functor of Hom out of `X`, evaluated
at `Y`. -/
def extAddEquivRightDerived (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y :=
  (extAddEquivHomology X (injectiveResolution Y) n).trans
    ((injectiveResolution Y).isoRightDerivedObj (preadditiveCoyoneda.obj (op X))
      n).symm.addCommGroupIsoToAddEquiv

end Resolution

section Linear

variable (S : Type*) [Ring S] {C : Type u} [Category.{v} C] [Abelian C] [Linear S C]
  [HasInjectiveResolutions C]

/-- The underlying group of the `S`-linear right derived functor of Hom out of
`X` is the right derived functor of Hom with values in abelian groups. -/
def linearRightDerivedIso (X Y : C) (n : ℕ) :
    (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}).obj
        ((((linearCoyoneda S C).obj (op X)).rightDerived n).obj Y) ≅
      ((preadditiveCoyoneda.obj (op X)).rightDerived n).obj Y :=
  (asIso ((LeftExactHomology.derivedNatTrans (forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v})
    ((linearCoyoneda S C).obj (op X)) n).app Y)).symm

variable [HasExt.{w} C]

/-- `Ext X Y n` is the underlying group of the `n`-th right derived functor of
`S`-linear Hom out of `X`, evaluated at `Y`. -/
def extAddEquivLinearRightDerived (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ (((linearCoyoneda S C).obj (op X)).rightDerived n).obj Y :=
  (extAddEquivRightDerived X Y n).trans (linearRightDerivedIso S X Y n).symm.addCommGroupIsoToAddEquiv

end Linear

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Mathlib's `Ext` groups of smooth representations exist in the universe `u`,
since the smooth category has enough injectives. This is not an instance, following
Mathlib's convention for `hasExt_of_enoughInjectives`. -/
theorem hasExt_smoothRep : HasExt.{u} (SmoothRep.{u, u, u} R G) :=
  hasExt_of_enoughInjectives.{u} _

/-- Smooth Ext, the right derived functors of equivariant Hom, has the
underlying groups of Mathlib's `Ext` in the abelian category of smooth
representations. -/
def smoothExtAddEquiv [HasExt.{w} (SmoothRep.{u, u, u} R G)] (V W : SmoothRep.{u, u, u} R G)
    (n : ℕ) : ((SmoothExt.ext R G V n).obj W) ≃+ Ext.{w} V W n :=
  (extAddEquivLinearRightDerived R V W n).symm

end Smooth

end Langlands.Cohomology.ExtRightDerived
