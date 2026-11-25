/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.CategoryTheory.Projection.ProjectionMateSquareCoherence
import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback

/-!
# Operator and base-change naturality of the projection formula

Source: blueprint, proper base change, order 1274; Stacks Tags 0B56, 0944 and 0E48
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Naturality in the first variable of the specified counit mate for an arbitrary coefficient.
Source: Stacks 0B56 and blueprint order 1274, paragraph 1
(blueprint: lemma-weil-pbc-projection-formula-base-change-naturality).
Proof: transpose both composites under adj. Naturality of alpha identifies the second
transpose with counit tensor identity followed by u tensor identity. Naturality of the
counit identifies it with the first transpose. Injectivity of the Hom equivalence
proves equality. This applies to every u and in particular to endomorphisms. -/
theorem derivedProjectionFormulaMate_naturality
    {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (L : A ⥤ B) (V : B ⥤ A) (adj : L ⊣ V)
    (TR : A × A ⥤ A) (TS : B × B ⥤ B)
    (alpha : TR ⋙ L ≅ (L.prod L) ⋙ TS)
    (E E' : B) (Q : A) (q : E ⟶ E') :
    derivedProjectionFormulaMate L V adj TR TS alpha E Q ≫
        V.map (TS.map (Prod.mkHom q (𝟙 (L.obj Q)))) =
      TR.map (Prod.mkHom (V.map q) (𝟙 Q)) ≫
        derivedProjectionFormulaMate L V adj TR TS alpha E' Q := by
  exact (congrArg (fun t ↦ t.app Q)
    ((adj.rightAdjointProjectionMap (T_C := Functor.curry.obj TS)
      (T_D := Functor.curry.obj TR)
      (Functor.curry.map alpha.hom ≫ (Functor.curryObjProdComp L L TS).hom)).naturality q)).symm

end CategoryTheory

namespace SheafOfModules

end SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- The projection arrow for arbitrary coefficients on the small ringed pro-etale sites.
It is exactly the existing counit mate using the uniquely normalized tensor comparison.
Source: Stacks 0B56 (blueprint: lemma-weil-pbc-projection-formula-base-change-naturality). -/
noncomputable def proEtaleProjectionFormulaMate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (K : DerivedCategory (proEtaleRingModules X S))
    (Q : DerivedCategory (proEtaleRingModules Y R)) :=
  derivedProjectionFormulaMate (proEtaleRingDerivedPullback f R S c)
    (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
    a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b) K Q

end AlgebraicGeometry.Scheme
