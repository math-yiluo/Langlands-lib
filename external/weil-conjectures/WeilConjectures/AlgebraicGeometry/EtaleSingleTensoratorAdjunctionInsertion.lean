/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Exact.NormalizedTensorAdjunctionInsertion
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization

/-! # Normalized tensor insertions against the flat single tensorators, over general coefficients

The generic normalized tensor calculation
`SheafExactDegreeZero.normalizedTensor_adjointInsertion`, specialized to étale sheaves with
general coefficient categories and restated with the flat single tensorators
`singleFunctorObjTensorIso` and the site tensor normalization
`ExceptionalCoefficients.SiteTensorNormalizationAux`.

Stating it over general coefficient categories keeps the instance paths of the sheaf categories
those of `singleFunctorObjTensorIso`, `derivedTensor` and `SiteTensorNormalizationAux`. A
specialization to module coefficients then only differs from these by small instance subterms,
which keeps its kernel check cheap.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), finite-level scalar/tensor reduction.
(blueprint: lem-pur-tate-tensor-adjunction-insertion)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance 10000] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] sheafBraidedCategory

/-- The flat single tensorator is the localization tensorator of the two single complexes,
followed by the explicit cochain tensorator of single complexes.
(auxiliary; not a blueprint node).

Proof: expand the factorization of `singleFunctorObjTensorIso` through the homotopy category;
the comparison of the single functor with `Q` cancels against the comparison of `Q` with the
homotopy quotient followed by `Qh`. -/
theorem singleFunctorObjTensorIso_hom_eq
    {B : Type v} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {T : Scheme.{u}} (L M : Sheaf T.smallEtaleTopology B)
    (hL : ObjectProperty.flat L) :
    (singleFunctorObjTensorIso L M hL).hom =
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L)
        ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map (singleCochainTensorIso L M).hom := by
  rw [singleFunctorObjTensorIso_factorization]
  simp only [singleFunctorObjIsoQh, DerivedCategory.singleFunctorIsoCompQ,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  simp only [Functor.LaxMonoidal.transport_μ, Functor.LaxMonoidal.comp_μ,
    Category.assoc]
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality]
  simp only [Category.id_comp, Functor.comp_map]
  erw [Category.comp_id]

variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [SymmetricCategory D] [MonoidalClosed D] [Abelian.HasFunctorialFlatResolution D]
  {T : Scheme.{u}}
  (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
  (U : Sheaf T.smallEtaleTopology D ⥤ Sheaf T.smallEtaleTopology C) [F.Additive] [U.Additive]
  [F.OplaxMonoidal] [U.LaxMonoidal] [F.IsLeftAdjoint]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (a : F ⊣ U) [a.IsMonoidal]
  (E : DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
    DerivedCategory (Sheaf T.smallEtaleTopology D)) (ad : E ⊣ U.mapDerivedCategory)

/-- For a site-normalized derived tensor comparison `δ`, the tensor of two exact-single
adjunction insertions, followed by the flat single tensorator, is the image of the flat single
tensorator followed by the insertion of the lax tensor of the two maps. The insertions are given
as morphisms `i₁ i₂ i₁₂` equal to `adjointInsertion`.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/sk-thm-purity-transport.proof.md,
Step 1 (compatibility with the finite reductions), finite-level scalar/tensor reduction.
(blueprint: lem-pur-tate-tensor-adjunction-insertion)

Proof: the flat single tensorators are the localization tensorators followed by the cochain
tensorators of single complexes (`singleFunctorObjTensorIso_hom_eq`). The site normalization is
the representative tensor square, so `normalizedTensor_adjointInsertion` applies. -/
theorem siteNormalizedTensor_adjointInsertion
    (rep : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      E.obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hrep : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      rep P = (ad.homEquiv _ _).symm
        (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          U.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (derivedTensor D T))
    (ht : ExceptionalCoefficients.SiteTensorNormalizationAux C D T F E rep δ)
    {M N : Sheaf T.smallEtaleTopology C} {P Q : Sheaf T.smallEtaleTopology D}
    (hM : ObjectProperty.flat M) (hP : ObjectProperty.flat P)
    (f : M ⟶ U.obj P) (g : N ⟶ U.obj Q)
    (i₁ : E.obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj P)
    (hi₁ : i₁ = SheafExactDegreeZero.adjointInsertion U ad f)
    (i₂ : E.obj ((DerivedCategory.singleFunctor _ 0).obj N) ⟶
      (DerivedCategory.singleFunctor _ 0).obj Q)
    (hi₂ : i₂ = SheafExactDegreeZero.adjointInsertion U ad g)
    (i₁₂ : E.obj ((DerivedCategory.singleFunctor _ 0).obj (M ⊗ N)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj (P ⊗ Q))
    (hi₁₂ : i₁₂ = SheafExactDegreeZero.adjointInsertion U ad
      ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ U P Q)) :
    δ.hom.app ((DerivedCategory.singleFunctor _ 0).obj M,
        (DerivedCategory.singleFunctor _ 0).obj N) ≫ (i₁ ⊗ₘ i₂) ≫
        (singleFunctorObjTensorIso P Q hP).hom =
      E.map (singleFunctorObjTensorIso M N hM).hom ≫ i₁₂ := by
  subst hi₁ hi₂ hi₁₂
  rw [singleFunctorObjTensorIso_hom_eq P Q hP, singleFunctorObjTensorIso_hom_eq M N hM]
  exact SheafExactDegreeZero.normalizedTensor_adjointInsertion F U a E ad rep hrep δ ht M N P Q f g

end AlgebraicGeometry.Etale
