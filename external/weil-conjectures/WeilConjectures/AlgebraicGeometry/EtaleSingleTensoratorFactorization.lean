/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible

/-! # Factorization of the canonical degree-zero tensor comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : AlgebraicGeometry.Scheme.{u}}

/-- The flat single tensorator is the composite of the explicit cochain tensorator,
the homotopy quotient tensorator and the localization tensorator.
Source: Stacks, Cohomology on Sites, Tags 06YQ and 06YU, derived tensor construction.
(auxiliary; not a blueprint node).
Proof: expand the defining composite of singleFunctorObjTensorIso. The hom component
of an isomorphism composite is the composite of its hom components; the hom of asIso
is its original map. The homotopy quotient and localization tensorator formula for
a composite functor then identifies the middle two arrows. Functoriality combines
the two maps defining singleCochainTensorIso, and the final inverse is unchanged. -/
theorem singleFunctorObjTensorIso_factorization
    (A C : Sheaf X.smallEtaleTopology B) (hA : ObjectProperty.flat A) :
    let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
    let F := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ) ⋙
      DerivedCategory.Qh
    (singleFunctorObjTensorIso A C hA).hom =
      ((singleFunctorObjIsoQh A).hom ⊗ₘ (singleFunctorObjIsoQh C).hom) ≫
        Functor.LaxMonoidal.μ F (sg.obj A) (sg.obj C) ≫
        F.map (singleCochainTensorIso A C).hom ≫ (singleFunctorObjIsoQh (A ⊗ C)).inv := by
  dsimp only
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, singleFunctorObjTensorIso,
    Iso.trans_hom, Iso.symm_hom, tensorIso_hom, asIso_hom,
    Functor.LaxMonoidal.μNatTrans_app_app, Functor.mapIso_hom,
    Functor.Monoidal.μIso_hom, singleCochainTensorIso, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Etale
