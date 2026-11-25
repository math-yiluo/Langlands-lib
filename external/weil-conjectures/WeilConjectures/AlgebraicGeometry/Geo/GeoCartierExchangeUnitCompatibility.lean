/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
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
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantMapComposition

/-!
# Supported-unit compatibility of the Cartier exchange

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
pullback paragraph: unit compatibility of `geoCartierExchange`
(blueprint: lem-sfb-cartier-exchange-unit-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The hom-equivalence calculation for a square of adjoint functors.
This is the formal naturality and injectivity calculation in Steps 1, 3 and 4
of the item's existing proof (blueprint: lem-sfb-cartier-exchange-unit-compatibility).
Proof: substitute the two adjunct identities, transpose, and move the first map
through the natural square comparison,
and use the assumed equality of the resulting constant structure maps. -/
private theorem exchange_unit_of_transposes {C₁ C₂ C₃ C₄ : Type (u + 2)}
    [Category.{u + 1} C₁] [Category.{u + 1} C₂]
    [Category.{u + 1} C₃] [Category.{u + 1} C₄]
    (L : C₁ ⥤ C₂) (R : C₂ ⥤ C₁) (L' : C₃ ⥤ C₄) (R' : C₄ ⥤ C₃)
    (H : C₁ ⥤ C₃) (W : C₂ ⥤ C₄) (adj : L ⊣ R) (adj' : L' ⊣ R')
    (e : H ⋙ L' ≅ L ⋙ W) {S : C₁} {S' : C₃} {F : C₂} {F' : C₄}
    (ρ : S ⟶ R.obj F) (ρ' : S' ⟶ R'.obj F')
    (ch : H.obj S ⟶ S') (cw : W.obj F ⟶ F')
    (ci : L.obj S ⟶ F) (ci' : L'.obj S' ⟶ F')
    (hci : ci = L.map ρ ≫ adj.counit.app F)
    (hci' : ci' = L'.map ρ' ≫ adj'.counit.app F')
    (hs : e.hom.app S ≫ W.map ci ≫ cw = L'.map ch ≫ ci') :
    H.map ρ ≫ adj'.homEquiv _ _
        (e.hom.app (R.obj F) ≫ W.map (adj.counit.app F) ≫ cw) = ch ≫ ρ' := by
  subst ci
  subst ci'
  apply (adj'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := e.hom.naturality ρ
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simpa only [Functor.map_comp, Category.assoc] using hs

/-- Write the existing constant map with the canonical inverse-image functor in its type.
This is only a definitional bridge between the two inverse-image presentations. -/
private def constant_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).obj (geoCartierConstant A Y) ⟶
      geoCartierConstant A X := by
  unfold upperStar
  exact Scheme.proEtaleConstantInverseImageMap f
    (ModuleCat.{u + 1} A) (ModuleCat.of A A)

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Scheme.proEtaleConstantInverseImageMap constantSheaf upperStarComp

/-- The bridge is the original map, definitionally. -/
private theorem constant_pullback_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constant_pullback A f = Scheme.proEtaleConstantInverseImageMap f
      (ModuleCat.{u + 1} A) (ModuleCat.of A A) := by
  rfl

/-- The two inverse-image presentations act identically on the constant map. -/
private theorem constant_pullback_map_eq (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) f).map (constant_pullback A g) =
      (Scheme.proEtaleSheafInverseImage f (ModuleCat.{u + 1} A)).map
        (Scheme.proEtaleConstantInverseImageMap g
          (ModuleCat.{u + 1} A) (ModuleCat.of A A)) := by
  unfold upperStar
  rfl

/-- The bridge satisfies the already stated composition law. -/
private theorem constant_pullback_comp (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    constant_pullback A (f ≫ g) =
      (upperStarComp (ModuleCat.{u + 1} A) f g).hom.app (geoCartierConstant A Z) ≫
        (upperStar (ModuleCat.{u + 1} A) f).map (constant_pullback A g) ≫
          constant_pullback A f := by
  rw [constant_pullback_eq A (f ≫ g), constant_pullback_map_eq A f g,
    constant_pullback_eq A f]
  exact Scheme.proEtaleConstantInverseImageMap_comp f g A

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

/-- The bridge is the adjoint of the constant direct-image map, by definition. -/
private theorem constant_pullback_counit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    constant_pullback A f =
      (upperStar (ModuleCat.{u + 1} A) f).map
        (Scheme.proEtaleConstantDirectImageMap f
          (ModuleCat.{u + 1} A) (ModuleCat.of A A)) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app
          (geoCartierConstant A X) := by
  unfold constant_pullback
  dsimp only [id]
  unfold Scheme.proEtaleConstantInverseImageMap
  rfl

section ConstantSquare

attribute [local irreducible] upperStar lowerStar
  upperStarLowerStarAdjunction Scheme.proEtaleConstantDirectImageMap
attribute [local semireducible] geoCartierPullbackSquare

/-- Transport of a constant structure map along equality of scheme morphisms.
Proof: eliminate the equality, then compose with the identity. -/
private theorem constant_pullback_transport (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f g : X ⟶ Y) (e : f = g) :
    (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) e)).hom.app
        (geoCartierConstant A Y) ≫ constant_pullback A g = constant_pullback A f := by
  cases e
  simp

/-- The definition of the square comparison, before taking components. -/
private theorem pullback_square_eq (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (h : Z' ⟶ Z) (w : D' ⟶ D) (sq : CommSq w i' i h) :
    geoCartierPullbackSquare A i i' h w sq =
      (upperStarComp (ModuleCat.{u + 1} A) i' h).symm ≪≫
        eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm) ≪≫
        upperStarComp (ModuleCat.{u + 1} A) w i := by
  rfl

/-- The component formula of the defined square comparison.
Proof: unfold the comparison and the components of composite natural isomorphisms. -/
private theorem pullback_square_component (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (h : Z' ⟶ Z) (w : D' ⟶ D) (sq : CommSq w i' i h) :
    (geoCartierPullbackSquare A i i' h w sq).hom.app (geoCartierConstant A Z) =
      (upperStarComp (ModuleCat.{u + 1} A) i' h).inv.app (geoCartierConstant A Z) ≫
        (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm)).hom.app
          (geoCartierConstant A Z) ≫
        (upperStarComp (ModuleCat.{u + 1} A) w i).hom.app (geoCartierConstant A Z) := by
  rw [pullback_square_eq A i i' h w sq]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]

/-- The square comparison preserves the constant structure maps.
Source: the two composition laws and equality transport in Step 2
(blueprint: lem-sfb-cartier-exchange-unit-compatibility).
Proof: apply the composition law to `(w, i)` and `(i', h)`, transport the constant
map along `sq.w.symm`, and cancel the first comparison isomorphism. -/
private theorem constant_square
    (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (h : Z' ⟶ Z) (w : D' ⟶ D) (sq : CommSq w i' i h) :
    (geoCartierPullbackSquare A i i' h w sq).hom.app (geoCartierConstant A Z) ≫
        (upperStar (ModuleCat.{u + 1} A) w).map
          (constant_pullback A i) ≫
        constant_pullback A w =
      (upperStar (ModuleCat.{u + 1} A) i').map
          (constant_pullback A h) ≫
        constant_pullback A i' := by
  rw [pullback_square_component A i i' h w sq]
  simp only [Category.assoc]
  rw [← constant_pullback_comp A w i]
  rw [constant_pullback_transport A (i' ≫ h) (w ≫ i) sq.w.symm]
  rw [constant_pullback_comp A i' h]
  simp only [Iso.inv_hom_id_app_assoc]

/-- Specialize the abstract transpose calculation to the constant-map square. -/
private theorem unit_compatibility_bridge
    (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (h : Z' ⟶ Z) (w : D' ⟶ D) (sq : CommSq w i' i h) :
    (upperStar (ModuleCat.{u + 1} A) h).map
          (Scheme.proEtaleConstantDirectImageMap i
            (ModuleCat.{u + 1} A) (ModuleCat.of A A)) ≫
        geoCartierExchange A i i' h w sq =
      constant_pullback A h ≫
        Scheme.proEtaleConstantDirectImageMap i'
          (ModuleCat.{u + 1} A) (ModuleCat.of A A) := by
  unfold geoCartierExchange
  exact exchange_unit_of_transposes
    (upperStar (ModuleCat.{u + 1} A) i) (lowerStar (ModuleCat.{u + 1} A) i)
    (upperStar (ModuleCat.{u + 1} A) i') (lowerStar (ModuleCat.{u + 1} A) i')
    (upperStar (ModuleCat.{u + 1} A) h) (upperStar (ModuleCat.{u + 1} A) w)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i')
    (geoCartierPullbackSquare A i i' h w sq)
    (S := geoCartierConstant A Z) (S' := geoCartierConstant A Z')
    (F := geoCartierConstant A D) (F' := geoCartierConstant A D')
    (Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A) (ModuleCat.of A A))
    (Scheme.proEtaleConstantDirectImageMap i' (ModuleCat.{u + 1} A) (ModuleCat.of A A))
    (constant_pullback A h) (constant_pullback A w)
    (constant_pullback A i) (constant_pullback A i')
    (constant_pullback_counit A i) (constant_pullback_counit A i')
    (constant_square A i i' h w sq)

end ConstantSquare

/-- The closed exchange carries the constant direct-image unit to the pulled-back
constant unit.  This is the unit-compatibility square for `geoCartierExchange`.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-lem-geo-cartier/sk-lem-geo-cartier.proof.md, pullback paragraph
(blueprint: lem-sfb-cartier-exchange-unit-compatibility).
Proof: expand `geoCartierExchange` as the mate of the inverse-image square
comparison.  Naturality of that comparison with the constant direct-image map,
the defining constant-map composition law, and the equality in the commuting
square identify the transpose of the left composite with
`c^i' ≫ i'^*(c^h)`.  The transpose of the right composite is the same by the
adjunction definition of the constant inverse-image map.  Injectivity of the
adjunction hom bijection gives the equality. This uses hom-equivalence naturality,
the inverse-image/direct-image interface, and the constant-map composition statement.
-/
theorem geoCartierExchange_unit_compatibility
    (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (h : Z' ⟶ Z) (w : D' ⟶ D) (sq : CommSq w i' i h) :
    (upperStar (ModuleCat.{u + 1} A) h).map
          (Scheme.proEtaleConstantDirectImageMap i
            (ModuleCat.{u + 1} A) (ModuleCat.of A A)) ≫
        geoCartierExchange A i i' h w sq =
      Scheme.proEtaleConstantInverseImageMap h
          (ModuleCat.{u + 1} A) (ModuleCat.of A A) ≫
        Scheme.proEtaleConstantDirectImageMap i'
          (ModuleCat.{u + 1} A) (ModuleCat.of A A) := by
  exact unit_compatibility_bridge A i i' h w sq

end AlgebraicGeometry.ProEtale
