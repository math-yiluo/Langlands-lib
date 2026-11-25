/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageSingleRawClassVanishing
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly

/-! # Eventual vanishing of finitely many raw cartesian derived classes

Source: Stacks Project, Tag 0EYM, second proof, injectivity of the cohomology comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

noncomputable local instance cartesianHigherImageFiniteRawClassHasShift (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

noncomputable local instance cartesianHigherImageFiniteRawClassHasZeroMorphisms (T : Scheme.{u}) :
    HasZeroMorphisms (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  inferInstance

/-- Finitely many raw derived classes killed by cartesian exchange are killed at a
common later stage. This is the cohomological part of affine-section injectivity;
it does not concern arbitrary homology sections or the sheafification comparison.

Source: Stacks Project, Tag 0EYM, second proof, part (2); Tags 0EYL and 0GIT.
(blueprint: lem-sc-cartesian-higher-image-finite-raw-class-vanishing).

Proof: Descend each affine etale test object and its derived class to an etale
chart above a sufficiently late stage. The inverse-image site description and
exact inverse-image/single/shift comparisons identify the class with restricted
cohomology on the cartesian chart. Descend the finitely many objects, arrows and
coefficient comparisons to one common stage. The pulled-back chart schemes form
qcqs inverse systems with affine transitions, with coefficients pulled back from
F. Derived cohomology continuity gives an injective colimit comparison. Under
its canonical map the given classes have zero image by the hypothesis and
exchange naturality. The filtered-colimit equality criterion therefore kills
each class at a later stage. Cofiltered wide spans equalize the finitely many
arrows from these stages to the initial stage. Functoriality of the cohomology
pullbacks transports every zero to this common stage. The raw Hom/cohomology
comparison and exchange pasting identify these maps with the displayed
transitions. The argument includes an empty family, empty affine objects and
q = 0. All complexes have the common lower bound zero; no preservation of
injectives by inverse image is assumed. -/
theorem exists_cartesianHigherImage_finite_raw_classes_eq_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (J : Type u) [Finite J]
    (V : J → c.pt.left.Etale) [∀ t, IsAffine (V t).left]
    (z : ∀ t, (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj (V t)) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (hz : ∀ t, z t ≫ (shiftFunctor _ (q : ℤ)).map
      (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
        (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) = 0) :
    ∃ (j : I) (a : j ⟶ i), ∀ t,
      z t ≫ (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app j).left (D.map a).left (c.π.app i).left
          (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
          (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
              (D.map a).left (Over.w (D.map a)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) = 0 := by
  classical
  apply exists_cartesianHigherImage_finite_raw_assembly D c f F q i J V z
  intro t
  exact exists_cartesianHigherImage_single_raw_class_eq_zero D c hc f F q i
    (V t) (z t) (hz t)

end AlgebraicGeometry.Etale
