/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedTensorRepresentativeComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResolutionDerivedSquare
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResolutionSigmaNaturality
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleResolutionRepresentativeSquare
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The coefficient-resolution square for pro-etale tensor pullback

The ordinary comparison, localization factors and derived comparison are the canonical
constructions. The bottom-right complex is written as the tensor with F(N[0]);
the canonical termwise single-complex identification identifies this with FP tensor FN.

## References

* Stacks Project, Cohomology on Sites, Tags 07A4 and 06YU
* Stacks, Tag 06YM
* Stacks, Tags 06YP and 06YU
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The existing direct-sum total tensor, including its cochain signs. -/
abbrev proEtaleResolutionTotal (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :=
  Functor.uncurry.obj ((proEtaleOrdinaryTensor Z R).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The formula for alpha from a resolution and the localized tensor-resolution iso.
The inverse here is the specified inverse of Q(1 tensor q), supplied as e. This is an
actual composite, with no choice of a comparison map or of a coefficient resolution. -/
def proEtaleCoefficientResolutionAlpha (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) (a : ProEtaleTensorModel Z R)
    (P M H : CochainComplex (proEtaleRingModules Z R) ℤ)
    (hP : proEtaleFlatRepresentatives Z R P) (hH : proEtaleFlatRepresentatives Z R H)
    (q : H ⟶ M)
    (e : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z R).obj (P, H)) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z R).obj (P, M))) :
    DerivedCategory.Q.obj ((proEtaleResolutionTotal Z R).obj (P, M)) ⟶
      a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj M) :=
  e.inv ≫ a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩) ≫
    a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The arrow 1 tensor q on the existing direct-sum total tensor. -/
abbrev proEtaleResolutionTensorMap (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (P : CochainComplex (proEtaleRingModules Z R) ℤ)
    {H M : CochainComplex (proEtaleRingModules Z R) ℤ} (q : H ⟶ M) :=
  (proEtaleResolutionTotal Z R).map (Prod.mkHom (𝟙 P) q)

attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  HomologicalComplex₂.total

private theorem resolutionTensor_quasiIso
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (P : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    {H M : CochainComplex (proEtaleRingModules Z RZ) ℤ} (q : H ⟶ M)
    (hq : QuasiIso q) : QuasiIso (proEtaleResolutionTensorMap Z RZ P q) := by
  obtain ⟨_, ht⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated RZ
  have hp := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1
  have hh := (ht P hp hP.2).1 H M q hq |>.1
  let T := (proEtaleOrdinaryTensor Z RZ).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have he : proEtaleResolutionTensorMap Z RZ P q = (T.obj P).map q := by
    change (T.map (𝟙 P)).app H ≫ (T.obj P).map q = _
    rw [T.map_id, NatTrans.id_app, Category.id_comp]
  rw [he]
  exact hh

attribute [local irreducible] proEtaleCoefficientResolutionAlpha

end AlgebraicGeometry.Scheme
