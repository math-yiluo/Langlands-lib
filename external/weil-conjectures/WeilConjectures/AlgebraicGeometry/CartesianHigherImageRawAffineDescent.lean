/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageAffineComplexPresentation
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Affine derived classes for cartesian higher images

Source: Stacks Project, Tag 0EYM, second proof, left vertical arrow.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

noncomputable local instance cartesianHigherImageRawAffineDescentHasShift (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

/-- A raw derived class on an affine etale test object factors through a pulled-back
stage derived image. No assertion about arbitrary homology sections or germs is made.
Source: Stacks Project, Tag 0EYM, second proof, left vertical arrow; Tags 0EYL and 09YQ.
(blueprint: lem-sc-cartesian-higher-image-raw-affine-descent).

Proof: Reindex by a coinitial directed poset. The affine etale test object U is
finitely presented over the qcqs limiting base. Descend it to an affine etale
object U_i at a stage using 0EYL. On the tail at i, set U_j = U_i times_{S_i} S_j
and Y_j = U_j times_{S_j} (X times_k S_j). These Y_j are qcqs, their transitions
are affine, and their limit is U times_S (X times_k S). Their coefficient sheaves
are the inverse images of F along Y_j to X. Derived adjunction and the free-sheaf
sections adjunction identify the given raw morphism with degree-q cohomology on
this limit. Cohomology continuity 09YQ represents it by a class on one Y_j. The
same adjunction identifies that class with a morphism from Z[U_j][0] to the shifted
stage derived image. Pull back this morphism to S, identify the free sheaf on the
pullback of U_j with Z[U], and use exact pullback's single and shift comparisons.
This gives t. Naturality of derived adjunction identifies its composite with the
shift of cartesianDerivedImageMap with z, since that map is the exchange of the
same cartesian square followed by coefficient composition. Finally return the
stage j to the original index category. All equalities here are in D-plus, before
homology or sheafification. Zero coefficients, q=0 and empty U are included. -/
theorem exists_cartesianHigherImage_raw_affine_factorization
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj U) ⟶
        (cartesianDerivedImage f c.pt.hom
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))⟦(q : ℤ)⟧) :
    ∃ (i : I)
      (t : (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((abelianComparisonFree c.pt.left).obj U) ⟶
          ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
            (cartesianDerivedImage f (D.obj i).hom
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧),
      t ≫ (shiftFunctor _ (q : ℤ)).map
        (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
          (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) = z := by
  classical
  obtain ⟨J, _, _, H, B, a, lift, e, hB, hcompat⟩ :=
    exists_cartesianHigherImage_affine_complex_presentation D c hc f F q U
  obtain ⟨hcolim⟩ := EtaleComplexCohomologyPresentation.isColimit hB
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  obtain ⟨j, x, hx⟩ := Concrete.isColimit_exists_rep H hcolim (e.inv z)
  refine ⟨a j.unop, lift j.unop x, ?_⟩
  rw [hcompat, hx]
  exact ConcreteCategory.congr_hom e.inv_hom_id z

end AlgebraicGeometry.Etale
