/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenCounitSquareSection

/-! # The ordinary open counit square

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-ordinary-open-counit-square).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry


/-- Counit compatibility for the fixed comparisons on ordinary sheaves of modules.
Source: Stacks Project, Cohomology, Tag 08FE (the underived sectionwise identity in
its proof), and Tag 08BV (the open restriction maps in the Mayer--Vietoris sequence).
Proof: put V = h inverse image U and g = h restricted to U. First replace each
schemeOpenRestriction by restrictFunctor along the open inclusion using
Scheme.Modules.overFunctorEquiv. The transported counit is overFunctorEquiv.hom
followed by restrictAdjunction.counit. Naturality of overFunctorEquiv moves the
Y identification past the composition comparison. Its X inverse and hom cancel
on the right, leaving the square for restrictFunctor itself.
Evaluate on any open W of U and any section of M. The composition comparison
uses pushforwardComp (identity on sections), pushforwardCongr for
j_X followed by h = g followed by j_Y (restriction along the equality of preimages),
and inverse pushforwardComp (again identity on sections). The Y counit restricts
along j_Y inverse image (j_Y image W) = W. The restriction comparison uses
image_morphismRestrict_preimage to identify h inverse image (j_Y image W) with
j_X image (g inverse image W); its pushforwardCongr₂ component is restriction
along that equality. The subsequent image of the X counit restricts along
j_X inverse image (j_X image (g inverse image W)) = g inverse image W.
Thus both composites are M.presheaf.map applied to the same equality morphism
from their common preimage open to g inverse image W. Functoriality of M.presheaf
combines the restrictions; thinness of the category of opens identifies the
composite arrows. Extensionality on W and sections proves the module-map equality.
Transport back through overFunctorEquiv proves the displayed equation. This holds
also for empty and full opens, with the same preimage equalities, and requires no
injectivity or derived hypothesis. This statement concerns ordinary modules only;
applying it in each degree and then applying the homotopy quotient is proved in
the importing module, rather than assumed here.
(blueprint: lem-pc-mayer-vietoris-ordinary-open-counit-square). -/
theorem schemeMVOrdinaryOpenCounit_square
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U : Y.Opens)
    (M : SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace)) :
    (schemeOpenRestriction Y U).map
        ((schemeMVUnderivedOpenComposition h U).hom.app M) ≫
        (schemeOpenModuleAdjunction Y U).counit.app
          ((RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).obj M) =
      (schemeMVUnderivedOpenRestriction h U).hom.app
          ((RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj M) ≫
        (RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom).map
          ((schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)).counit.app M) := by
  ext W
  exact congrFun (congrArg (fun q => q.hom)
    (schemeMVOrdinaryOpenCounit_square_app X Y h U M W)) _
end AlgebraicGeometry
