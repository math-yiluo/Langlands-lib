/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization

/-! # The homotopy factorization of the flat single tensorator -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

section Cochain

variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C]

private lemma map_quotient_tensorator
    {E : Type*} [Category* E] (F : HomotopyCategory C (.up ℤ) ⥤ E)
    (K M : CochainComplex C ℤ) :
    F.map (Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ)) K M) =
      𝟙 (F.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K ⊗
        (HomotopyCategory.quotient C (.up ℤ)).obj M)) := by
  change F.map (𝟙 _) = _
  exact F.map_id _

end Cochain

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : AlgebraicGeometry.Scheme.{u}}

/-- Factor the flat single tensorator directly through homotopy single complexes.
Source: Stacks, Cohomology on Sites, Tags 06YQ and 06YU; the explicit factorization
singleFunctorObjTensorIso_factorization.
(auxiliary; not a blueprint node).
Proof: expand the composite-functor lax tensorator in the existing factorization.
The homotopy quotient's strong tensorator is the identity. Every functor maps this
identity to an identity, so the intervening Qh map cancels. This leaves exactly the
Qh lax tensorator followed by Qh of the homotopy single tensorator, between the
original single/Qh isomorphisms. Flatness is used only by the existing factorization. -/
theorem singleFunctorObjTensorIso_homotopy_factorization
    (L M : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L) :
    let q := HomotopyCategory.quotient (Sheaf X.smallEtaleTopology B) (.up ℤ)
    let s := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
    (singleFunctorObjTensorIso L M hL).hom =
      ((singleFunctorObjIsoQh L).hom ⊗ₘ (singleFunctorObjIsoQh M).hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj (s.obj L)) (q.obj (s.obj M)) ≫
        DerivedCategory.Qh.map (q.map (singleCochainTensorIso L M).hom) ≫
        (singleFunctorObjIsoQh (L ⊗ M)).inv := by
  rw [singleFunctorObjTensorIso_factorization]
  dsimp only
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map,
    map_quotient_tensorator, Category.comp_id]

end AlgebraicGeometry.Etale
