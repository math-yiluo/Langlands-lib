/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationAffineCoordinates
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationCounit
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSpecializationUnitComparison

/-!
# Sections on a closed specialization neighbourhood in the pro-etale site

## References

* Stacks Project, Tag 09AC
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The adjunction unit on sections of a weakly contractible affine specialization
neighbourhood is a natural isomorphism of abelian groups. Whiskering the unit with
sections at `V` retains its naturality in the abelian sheaf. Its target at `F` is
`(i⁻¹ F)((proEtaleBaseChange i).obj V)`, i.e. sections on `V ×[X] Z`. -/
theorem isIso_proEtaleUnit_sections_of_specialization
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z)) :
    IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
      ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V))) := by
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
  let B := AffineProEt.ofEtale (𝟙 (Spec A))
  obtain ⟨hB, hspecB⟩ := specialization_affine_coordinates i V hweak hspec
  obtain ⟨_, _, _, _, _, ⟨adj⟩, _, _⟩ :=
    AffineProEt.affine_closed_site_functor_properties A I
  have hcounit : IsIso (adj.counit.app B) :=
    AffineProEt.isIso_closedSiteCounit_of_specialization A I adj B hB hspecB
  exact isIso_proEtaleUnit_sections_of_closedSiteCounit i V hB adj hcounit

end AlgebraicGeometry.Scheme
