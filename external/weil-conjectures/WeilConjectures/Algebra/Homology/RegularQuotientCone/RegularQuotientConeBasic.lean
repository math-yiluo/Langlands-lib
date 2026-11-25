/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
/-! # Normalized principal-quotient cone augmentation

Source: Stacks Project, sites-cohomology.tex, Tags 06YP, 06YS, 06YT, 06YY and 07A6.
(blueprint: def-cbc-regular-quotient-cone-basic).

The cone is Mathlib's cone, with unshifted summand second in its biproduct API.
The ordinary extension is the existing sheafified tensor, whose pure tensors have
scalar first. All computation maps below use the universal derived counit.
-/

@[expose] public section
set_option autoImplicit false

universe u v r wR wS
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]

/-- The recorded module category, as a transparent abbreviation.
Source: Stacks 06YY (blueprint: def-cbc-regular-quotient-cone-basic). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- The recorded restriction functor, as a transparent abbreviation.
Source: Stacks 03D7 (blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)

/-- Multiplication by the compatible family of local scalars defining a global section.
Source: Stacks 06YP, principal-resolution construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def scalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (Modules R) ⟶ 𝟭 (Modules R) where
  app M := { val := {
    app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (t.val U))
    naturality := by
      intro U V f
      ext x
      have h := M.val.map_smul f (t.val U) x
      rw [show (derivedChangeRingIndependentCoefficients J R).obj.map f (t.val U) =
        t.val V from t.property f] at h
      exact h.symm } }
  naturality {M N} f := by
    ext U x
    exact ((f.val.app U).hom.map_smul (t.val U) x).symm

/-- The map of unit modules induced by the ring-sheaf map.
Source: Stacks 06YP, principal-resolution construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def ringMap {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    unit (derivedChangeRingIndependentCoefficients J R) ⟶
      (restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  ((restriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk (fun U ↦ (1 : S.obj.obj U))
      (fun {_ _} f ↦ map_one (S.obj.map f).hom))

/-- Multiplication by the global section on an unbounded cochain complex.
Source: Stacks 06YP, principal-resolution construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def complexScalar (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ 𝟭 (CochainComplex (Modules R) ℤ) where
  app P := {
    f := fun n ↦ (scalar R t).app (P.X n)
    comm' := fun i j _ ↦ ((scalar R t).naturality (P.d i j)).symm }
  naturality {_P _Q} f := by
    ext n : 1
    exact (scalar R t).naturality (f.f n)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The strict cone functor, with diagonal action on chain maps.
Source: Stacks 06YP, principal quotient construction
(blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def cone (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ where
  obj P := CochainComplex.mappingCone ((complexScalar R t).app P)
  map {_P _Q} h := CochainComplex.mappingCone.map _ _ h h
    ((complexScalar R t).naturality h).symm
  map_id _P := CochainComplex.mappingCone.map_id _
  map_comp _f _g := CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _

/-- The canonical inclusion into the unshifted summand of the cone.
Source: Stacks 06YP (blueprint: def-cbc-regular-quotient-cone-basic). -/
noncomputable def inclusion (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    𝟭 (CochainComplex (Modules R) ℤ) ⟶ cone R t where
  app P := CochainComplex.mappingCone.inr ((complexScalar R t).app P)
  naturality {P Q} h := by
    ext n : 1
    simp [cone, CochainComplex.mappingCone.map]

end SheafOfModules.RegularQuotientCone
