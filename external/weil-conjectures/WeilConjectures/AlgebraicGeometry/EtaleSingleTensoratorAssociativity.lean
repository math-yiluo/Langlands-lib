/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal

/-! # Associativity of the canonical degree-zero tensor comparison -/

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

@[irreducible]
private noncomputable def singleIsoQh :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0 ≅
      HomologicalComplex.single _ (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ (.up ℤ) ⋙
        DerivedCategory.Qh :=
  DerivedCategory.singleFunctorIsoCompQ _ 0 ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm

private lemma singleTensorator_eq_transport
    (ms : (HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0).Monoidal)
    (hms : ∀ L M : Sheaf X.smallEtaleTopology B, letI := ms
      Functor.LaxMonoidal.μ
          (HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0) L M =
        (singleCochainTensorIso L M).hom)
    (A C : Sheaf X.smallEtaleTopology B) (hA : ObjectProperty.flat A) :
    letI := ms
    let e := singleIsoQh (B := B) (X := X)
    letI := Functor.LaxMonoidal.transport e.symm
    (singleFunctorObjTensorIso A C hA).hom =
      Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor _ 0) A C := by
  dsimp only
  let := ms
  let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
  let e := singleIsoQh (B := B) (X := X)
  let ls := Functor.LaxMonoidal.transport e.symm
  rw [Functor.LaxMonoidal.transport_μ e.symm]
  simp only [Functor.LaxMonoidal.comp_μ, hms, Category.assoc]
  change (singleFunctorObjTensorIso A C hA).hom =
    (e.hom.app A ⊗ₘ e.hom.app C) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (sg.obj A))
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (sg.obj C)) ≫
      DerivedCategory.Qh.map (Functor.LaxMonoidal.μ
        (HomotopyCategory.quotient _ (.up ℤ)) (sg.obj A) (sg.obj C)) ≫
      (HomotopyCategory.quotient _ (.up ℤ) ⋙ DerivedCategory.Qh).map
        (singleCochainTensorIso A C).hom ≫ e.inv.app (A ⊗ C)
  dsimp [singleFunctorObjTensorIso, singleFunctorObjIsoQh,
    singleCochainTensorIso, e, singleIsoQh, sg]
  simp [singleCochainTensorIso, singleIsoQh, Functor.map_comp, Category.assoc]

/-- The canonical flat single tensorators preserve the associator.
Source: Stacks, Cohomology on Sites, Tags 06YQ and 06YU, single/total tensor calculation.
(auxiliary; not a blueprint node).
Proof: expand the single tensorator through the degree-zero cochain functor, the
strong monoidal homotopy quotient, and the lax monoidal localization Qh. On complexes,
precompose in each degree with the triple-summand inclusions. A summand with any
nonzero index has a zero factor. The (0,0,0) summand is the original associator.
The quotient and Qh associativity axioms carry this equation to the derived category;
the natural single/quotient isomorphism cancels at intermediate objects. Flatness
makes the two tensorators whose left factors are L and L tensor M invertible;
no flatness of N is used. This calculation also covers zero sheaves and empty sites. -/
theorem singleFunctorObjTensorIso_associativity
    (L M N : Sheaf X.smallEtaleTopology B)
    (hL : ObjectProperty.flat L) (hM : ObjectProperty.flat M) :
    (singleFunctorObjTensorIso L M hL).hom ▷
        ((DerivedCategory.singleFunctor _ 0).obj N) ≫
      (singleFunctorObjTensorIso (L ⊗ M) N (ObjectProperty.prop_tensor hL hM)).hom ≫
      (DerivedCategory.singleFunctor _ 0).map (α_ L M N).hom =
    (derivedTensorAssociator B X _ _ _).hom ≫
      (DerivedCategory.singleFunctor _ 0).obj L ◁
        (singleFunctorObjTensorIso M N hM).hom ≫
      (singleFunctorObjTensorIso L (M ⊗ N) hL).hom := by
  obtain ⟨ms, hms⟩ := exists_singleCochainMonoidal (C := Sheaf X.smallEtaleTopology B)
  let := ms
  let sg := HomologicalComplex.single (Sheaf X.smallEtaleTopology B) (.up ℤ) 0
  let e := singleIsoQh (B := B) (X := X)
  let ls := Functor.LaxMonoidal.transport e.symm
  have fac (A C : Sheaf X.smallEtaleTopology B) (hA : ObjectProperty.flat A) :
      (singleFunctorObjTensorIso A C hA).hom =
        Functor.LaxMonoidal.μ (DerivedCategory.singleFunctor _ 0) A C :=
    singleTensorator_eq_transport ms hms A C hA
  rw [fac L M hL, fac (L ⊗ M) N (ObjectProperty.prop_tensor hL hM),
    fac M N hM, fac L (M ⊗ N) hL, derivedTensorAssociator_eq]
  exact Functor.LaxMonoidal.associativity _ L M N

end AlgebraicGeometry.Etale
