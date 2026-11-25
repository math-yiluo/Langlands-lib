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
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Sites.PreservesLimits
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerRepresentation

/-!
# Preservation of finite constant ring towers on the pro-etale site

## References

* Stacks Project, Tags 098T (2), 097D, 04D3 and 00YV
* Stacks Project, Tags 098T (2) and 097D
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def representableInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleBaseChange f ⋙ (ProEt.topology X).uliftYoneda.{u + 1} ≅
      (ProEt.topology Y).uliftYoneda.{u + 1} ⋙
        proEtaleSheafInverseImage f (Type (u + 1)) := by
  let e := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1}
    (proEtaleBaseChange f)
  exact Functor.isoWhiskerLeft
    (proEtaleBaseChange f ⋙ (ProEt.topology X).uliftYoneda.{u + 1})
    (sheafificationNatIso (ProEt.topology X) (Type (u + 1))) ≪≫
    Functor.isoWhiskerRight e (presheafToSheaf (ProEt.topology X) (Type (u + 1)))

private noncomputable def ringForgetInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1}) ≅
    sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1}) ⋙
      proEtaleSheafInverseImage f (Type (u + 1)) := by
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : (CategoryTheory.forget CommRingCat.{u + 1}).PreservesLeftKanExtensions
      (proEtaleBaseChange f).op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget CommRingCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (CategoryTheory.forget CommRingCat.{u + 1}) P (proEtaleBaseChange f).op V := by
      intro V
      infer_instance
    infer_instance
  exact sheafPullbackForgetIso (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) (CategoryTheory.forget CommRingCat.{u + 1})

private theorem preservesFiniteTower_of_representable
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (D : ℕᵒᵖ ⥤ Y.ProEt) (c : Cone D) (hc : IsLimit c)
    (hfc : IsLimit ((proEtaleBaseChange f).mapCone c))
    (e : D ⋙ (ProEt.topology Y).uliftYoneda.{u + 1} ≅
      Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
        sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})) :
    PreservesLimit (Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1})
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}) := by
  let F := proEtaleBaseChange f
  let Ly := (ProEt.topology Y).uliftYoneda.{u + 1}
  let Lx := (ProEt.topology X).uliftYoneda.{u + 1}
  let P := proEtaleSheafInverseImage f (Type (u + 1))
  let Ry := sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})
  let Rx := sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})
  let T := Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}
  let : PreservesLimit D F := preservesLimit_of_preserves_limit_cone hc hfc
  let : PreservesLimit D (F ⋙ Lx) := inferInstance
  let : PreservesLimit D (Ly ⋙ P) :=
    preservesLimit_of_natIso D (representableInverseImageIso f)
  let : PreservesLimit (D ⋙ Ly) P :=
    preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Ly hc)
      (isLimitOfPreserves (Ly ⋙ P) hc)
  let Iy := sheafToPresheaf (ProEt.topology Y) (Type (u + 1))
  let Ix := sheafToPresheaf (ProEt.topology X) (Type (u + 1))
  let : PreservesLimitsOfShape ℕᵒᵖ (Ry ⋙ Iy) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Ry :=
    preservesLimitsOfShape_of_reflects_of_preserves Ry Iy
  let : PreservesLimitsOfShape ℕᵒᵖ (Rx ⋙ Ix) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology X) CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Rx :=
    preservesLimitsOfShape_of_reflects_of_preserves Rx Ix
  let : ReflectsLimitsOfShape ℕᵒᵖ Rx := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimit (T ⋙ Ry) P := preservesLimit_of_iso_diagram P e
  let : PreservesLimit T (Ry ⋙ P) := inferInstance
  let : PreservesLimit T
      (proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙ Rx) :=
    preservesLimit_of_natIso T (ringForgetInverseImageIso f).symm
  exact preservesLimit_of_reflects_of_preserves
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}) Rx

/-- Inverse image preserves the limit of a countable tower of finite constant rings.
No surjectivity of the transition maps is required.
-/
theorem proEtaleSheafInverseImage_preserves_finite_tower
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    PreservesLimit (Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1})
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}) := by
  obtain ⟨D, c, ⟨hc⟩, ⟨hfc⟩, ⟨e⟩⟩ := proEtaleFiniteTower_representableLimit f Q
  exact preservesFiniteTower_of_representable f Q D c hc hfc e

end AlgebraicGeometry.Scheme
