/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
import WeilConjectures.AlgebraicGeometry.OpenPinnedTensorCounitTransport

/-! # Pinned counit restriction on homotopy complexes
Source: Stacks Project, Tags 08DW, 08HY and 0D5S.
(blueprint: lem-pc-open-pinned-counit-homotopy-restriction). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

private theorem counit_path_glue {C : Type*} [Category C]
    {A B C₀ D E I J H K : C}
    (s : A ⟶ B) (c : B ⟶ C₀) (e : C₀ ⟶ D) (a : E ≅ D)
    (v : E ⟶ I) (ε : D ⟶ J) (b : J ⟶ H) (z : H ⟶ I)
    (δ : C₀ ⟶ K) (l : K ⟶ I) (out : A ⟶ I)
    (ht : v = a.hom ≫ ε ≫ b ≫ z)
    (hc : e ≫ ε ≫ b ≫ z = δ ≫ l)
    (hs : s ≫ c ≫ δ ≫ l = out) :
    s ≫ c ≫ e ≫ a.inv ≫ v = out := by
  rw [ht]
  simp only [Iso.inv_hom_id_assoc]
  rw [hc]
  exact hs

/-- The pinned counit restriction equation for an arbitrary homotopy complex.
Source: Stacks Project, Tags 08DW, 08HY and 0D5S.
(blueprint: lem-pc-open-pinned-counit-homotopy-restriction).
Proof: expand the two composition comparisons in the restricted coefficient.
Their left-derived factorization equations identify their composites with the
pinned counits with the localized underived tensor composition comparisons.
The open-pullback comparison is leftDerivedUnique, so its factorization equation
identifies the open counit with the exact restriction factorization followed by
the underived open tensor comparison. Substituting these identities cancels the
inverse open and composition comparisons. What remains is the image in the
homotopy category of the four factors of openPinnedTensorRestrictionIso.
One can check these equalities on K-flat resolutions, where the counits are
invertible, and descend by their left-derived universal property. No flatness
of P is needed, and empty opens and zero complexes use the same identities. -/
theorem open_pinned_counit_homotopy_restriction
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    singleComplexRestrictedCoefficient k (DerivedCategory.Qh.obj P)
        ((derivedPullback k).obj (DerivedCategory.Qh.obj P)) (𝟙 _) U U' j hj ≫
      (schemeOpenRestriction X' U').mapDerivedCategory.map
        ((pinnedPullbackCounit.{u, w} k).app P) ≫
      (schemeOpenRestriction X' U').mapDerivedCategoryFactorsh.hom.app
        ((Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
      DerivedCategory.Qh.map ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u, w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P)  := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have ht := open_pinned_target_counit_triangle.{u, w} k U' P
  have hs := open_pinned_source_counit_triangle.{u, w} U j P
  have hc := open_pinned_tensor_counit_transport.{u, w} k U U' j hj P
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at ht hs hc
  have ht' := congrArg (fun f ↦ f ≫ DerivedCategory.Qh.map
    ((openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P)) ht
  simp only [Category.assoc] at ht'
  have h := counit_path_glue
    ((derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
      (DerivedCategory.Qh.obj P)))
    ((pinnedPullbackComposition.{u, w} j U.ι).hom.app (DerivedCategory.Qh.obj P))
    (eqToHom (congrArg (fun f ↦ (derivedPullback f).obj (DerivedCategory.Qh.obj P)) hj))
    ((pinnedPullbackComposition.{u, w} U'.ι k).app (DerivedCategory.Qh.obj P))
    _ _ _ _ _ _ _ ht' hc hs
  simpa only [singleComplexRestrictedCoefficient, pinnedPullbackComposition, Iso.app_inv,
    CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc] using h

end AlgebraicGeometry
