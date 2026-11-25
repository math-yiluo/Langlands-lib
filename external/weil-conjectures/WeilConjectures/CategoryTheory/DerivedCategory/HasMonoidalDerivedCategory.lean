/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Monoidal.Linear
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Algebra.Homology.BifunctorLinear
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear

/-!

# The monoidal structure on the derived category of a monoidal Grothendieck abelian category

The K-flat machinery migrated from mathlib PR #25848 equips the derived category
`DerivedCategory A` with a monoidal structure as soon as the localization functor
`Qh : K(A) ⥤ D(A)` satisfies `Functor.HasDerivedMonoidalCategory` with respect to
quasi-isomorphisms; see `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.

Verifying that hypothesis by hand at every use site is impractical, because it is phrased in
terms of the derived bifunctor, trifunctors and quadrifunctor of the tensor product. This
file packages it once and for all as an instance, deduced from conditions that are
checkable in practice:

* `A` is a monoidal Grothendieck abelian category (`IsGrothendieckAbelian`,
  `MonoidalCategory`, `MonoidalPreadditive`, `BraidedCategory`);
* the tensor product is closed (`MonoidalClosed`), so that `- ⊗ X` and `X ⊗ -` are left
  adjoints and hence preserve all colimits;
* `A` admits functorial flat resolutions (`Abelian.HasFunctorialFlatResolution`).

Together these give the K-flat left derivability structure, which is what
`CategoryTheory.MorphismProperty.kFlat_derivesMonoidal` turns into
`Functor.HasDerivedMonoidalCategory`. The file also records that the resulting derived tensor
product is additive, and `Λ`-linear if the tensor product of `A` is, in each variable.

## Main results

- `DerivedCategory.hasDerivedMonoidalCategory` : the instance
  `Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))`, from which
  `MonoidalCategory (DerivedCategory A)` follows by
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.
- `DerivedCategory.monoidalPreadditive`, `DerivedCategory.monoidalLinear`: the derived tensor
  product is additive, and `Λ`-linear if the tensor product of `A` is, in each variable.

## Implementation notes

`hasDerivedMonoidalCategory` is the K-flat route of
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`: the hypotheses above give
`(HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure`
(`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`), once `- ⊗ X` is known to preserve
`ℤ`-indexed colimits, which follows from the closedness and the braiding.

The additivity and linearity are proved on K-flat representatives. For a K-flat complex `P`,
the functor `Qh.obj P ⊗ᴸ -` is induced through the localization `Qh` by `(P ⊗ -) ⋙ Qh`
(`DerivedCategory.isIso_tensorLeftCounit`). The functor `P ⊗ -` on the homotopy category is
additive (it is triangulated) and `Λ`-linear (`WeilConjectures.Algebra.Homology.BifunctorLinear`),
so `Qh.obj P ⊗ᴸ -` is additive and `Λ`-linear by `Localization.functor_additive_iff` and
`Localization.functor_linear_iff`. Every object of `D(A)` is isomorphic to `Qh.obj P` for a
K-flat `P` (`DerivedCategory.exists_kFlat_iso`), and the same holds for `- ⊗ᴸ K`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A]

/-- For a monoidal closed Grothendieck abelian category `A` admitting functorial flat
resolutions, the localization functor `Qh : K(A) ⥤ D(A)` admits a derived monoidal
structure with respect to quasi-isomorphisms. Consequently `DerivedCategory A` is monoidal,
with tensor product the derived tensor product `- ⊗ᴸ -`. -/
instance hasDerivedMonoidalCategory [Abelian.HasFunctorialFlatResolution A] :
    Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  exact ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).kFlat_derivesMonoidal
    Qh).hasDerivedMonoidalCategory

variable {A} [Abelian.HasFunctorialFlatResolution A]

/-- The derived tensor product `K ⊗ᴸ -` is additive. -/
lemma additive_tensorLeft (K : DerivedCategory A) :
    ((curriedTensor (DerivedCategory A)).obj K).Additive := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso K
  have := isIso_tensorLeftCounit P hP
  have : (Qh ⋙ (curriedTensor (DerivedCategory A)).obj (Qh.obj P)).Additive :=
    Functor.additive_of_iso (asIso (tensorLeftCounit P)).symm
  have : ((curriedTensor (DerivedCategory A)).obj (Qh.obj P)).Additive :=
    (Localization.functor_additive_iff Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      _).2 this
  exact Functor.additive_of_iso ((curriedTensor _).mapIso e)

/-- The derived tensor product `- ⊗ᴸ K` is additive. -/
lemma additive_tensorRight (K : DerivedCategory A) :
    ((curriedTensor (DerivedCategory A)).flip.obj K).Additive := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso K
  have := isIso_tensorRightCounit P hP
  have : (Qh ⋙ (curriedTensor (DerivedCategory A)).flip.obj (Qh.obj P)).Additive :=
    Functor.additive_of_iso (asIso (tensorRightCounit P)).symm
  have : ((curriedTensor (DerivedCategory A)).flip.obj (Qh.obj P)).Additive :=
    (Localization.functor_additive_iff Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      _).2 this
  exact Functor.additive_of_iso ((curriedTensor _).flip.mapIso e)

/-- The derived tensor product is additive in each variable. -/
instance monoidalPreadditive : MonoidalPreadditive (DerivedCategory A) where
  whiskerLeft_zero {K _ _} := by
    have := additive_tensorLeft K
    exact ((curriedTensor (DerivedCategory A)).obj K).map_zero _ _
  zero_whiskerRight {K _ _} := by
    have := additive_tensorRight K
    exact ((curriedTensor (DerivedCategory A)).flip.obj K).map_zero _ _
  whiskerLeft_add {K _ _} _ _ := by
    have := additive_tensorLeft K
    exact ((curriedTensor (DerivedCategory A)).obj K).map_add
  add_whiskerRight {K _ _} _ _ := by
    have := additive_tensorRight K
    exact ((curriedTensor (DerivedCategory A)).flip.obj K).map_add

variable (Λ : Type*) [Ring Λ] [Linear Λ A] [MonoidalLinear Λ A]

/-- If the tensor product of `A` is `Λ`-linear, then the derived tensor product `K ⊗ᴸ -` is
`Λ`-linear. -/
lemma linear_tensorLeft (K : DerivedCategory A) :
    ((curriedTensor (DerivedCategory A)).obj K).Linear Λ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso K
  have := isIso_tensorLeftCounit P hP
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((curriedTensor _).obj P ⋙ Qh) ((curriedTensor _).obj (Qh.obj P)) :=
    ⟨asIso (tensorLeftCounit P)⟩
  have : ((curriedTensor (HomotopyCategory A (.up ℤ))).obj P ⋙ Qh).Linear Λ :=
    show (((curriedTensor A).bifunctorMapHomotopyCategory
      (.up ℤ) (.up ℤ) (.up ℤ)).obj P ⋙ Qh (C := A)).Linear Λ from inferInstance
  have : ((curriedTensor (DerivedCategory A)).obj (Qh.obj P)).Linear Λ :=
    (Localization.functor_linear_iff Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) Λ
      ((curriedTensor _).obj P ⋙ Qh) _).1 this
  exact Functor.linear_of_iso _ ((curriedTensor _).mapIso e)

/-- If the tensor product of `A` is `Λ`-linear, then the derived tensor product `- ⊗ᴸ K` is
`Λ`-linear. -/
lemma linear_tensorRight (K : DerivedCategory A) :
    ((curriedTensor (DerivedCategory A)).flip.obj K).Linear Λ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_iso K
  have := isIso_tensorRightCounit P hP
  let : Localization.Lifting Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      ((curriedTensor _).flip.obj P ⋙ Qh) ((curriedTensor _).flip.obj (Qh.obj P)) :=
    ⟨asIso (tensorRightCounit P)⟩
  have : ((curriedTensor (HomotopyCategory A (.up ℤ))).flip.obj P ⋙ Qh).Linear Λ :=
    show (((curriedTensor A).bifunctorMapHomotopyCategory
      (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj P ⋙ Qh (C := A)).Linear Λ from inferInstance
  have : ((curriedTensor (DerivedCategory A)).flip.obj (Qh.obj P)).Linear Λ :=
    (Localization.functor_linear_iff Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) Λ
      ((curriedTensor _).flip.obj P ⋙ Qh) _).1 this
  exact Functor.linear_of_iso _ ((curriedTensor _).flip.mapIso e)

/-- If the tensor product of `A` is `Λ`-linear in each variable, so is the derived tensor
product on `D(A)`. -/
instance monoidalLinear : MonoidalLinear Λ (DerivedCategory A) where
  whiskerLeft_smul K _ _ r f := by
    have := linear_tensorLeft Λ K
    exact ((curriedTensor (DerivedCategory A)).obj K).map_smul r f
  smul_whiskerRight r _ _ f K := by
    have := linear_tensorRight Λ K
    exact ((curriedTensor (DerivedCategory A)).flip.obj K).map_smul r f

end DerivedCategory
