/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteOrdinaryInverseTransport
import all WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTensorCoherence
import WeilConjectures.CategoryTheory.Derived.DerivedSquareIndependentUniverses
import WeilConjectures.CategoryTheory.SixFunctors.IndependentLocalizedCube
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-! # Derived inverse-image faces of strict coefficient transport

Source: Stacks Project, Tags 0D6D and 0G7E; Zheng, Construction 4.1.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf
  CategoryTheory.sheafCompose siteCoefficientTensor
  coefficientQuotientSheaf coefficientQuotientMap siteCoefficientTensorAdj siteScalarUnderlyingIso

namespace TransportCube
universe q
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory.{q} C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory.{q} D]
  {E : Type*} [Category E] [Abelian E] [HasDerivedCategory.{q} E]
  {F : Type*} [Category F] [Abelian F] [HasDerivedCategory.{q} F]
  {G : Type*} [Category G] [Abelian G] [HasDerivedCategory.{q} G]
  {H : Type*} [Category H] [Abelian H] [HasDerivedCategory.{q} H]
  {I : Type*} [Category I] [Abelian I] [HasDerivedCategory.{q} I]
  {J : Type*} [Category J] [Abelian J] [HasDerivedCategory.{q} J]
  (a : C ⥤ D) [a.Additive]
  (b : D ⥤ E) [b.Additive]
  (c : E ⥤ F) [c.Additive]
  (d : C ⥤ G) [d.Additive]
  (e : G ⥤ E) [e.Additive]
  (f : G ⥤ H) [f.Additive]
  (g : H ⥤ F) [g.Additive]
  (h : C ⥤ I) [h.Additive]
  (i : I ⥤ H) [i.Additive]
  (j : D ⥤ J) [j.Additive]
  (k : J ⥤ F) [k.Additive]
  (m : I ⥤ J) [m.Additive]
  (aD : DerivedCategory C ⥤ DerivedCategory D)
  (bD : DerivedCategory D ⥤ DerivedCategory E)
  (cD : DerivedCategory E ⥤ DerivedCategory F)
  (dD : DerivedCategory C ⥤ DerivedCategory G)
  (eD : DerivedCategory G ⥤ DerivedCategory E)
  (fD : DerivedCategory G ⥤ DerivedCategory H)
  (gD : DerivedCategory H ⥤ DerivedCategory F)
  (hD : DerivedCategory C ⥤ DerivedCategory I)
  (iD : DerivedCategory I ⥤ DerivedCategory H)
  (jD : DerivedCategory D ⥤ DerivedCategory J)
  (kD : DerivedCategory J ⥤ DerivedCategory F)
  (mD : DerivedCategory I ⥤ DerivedCategory J)
  (φa : DerivedCategory.Q ⋙ aD ⟶ a.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φb : DerivedCategory.Q ⋙ bD ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φc : DerivedCategory.Q ⋙ cD ⟶ c.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φd : DerivedCategory.Q ⋙ dD ⟶ d.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φe : DerivedCategory.Q ⋙ eD ⟶ e.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φf : DerivedCategory.Q ⋙ fD ⟶ f.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φg : DerivedCategory.Q ⋙ gD ⟶ g.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φh : DerivedCategory.Q ⋙ hD ⟶ h.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φi : DerivedCategory.Q ⋙ iD ⟶ i.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φj : DerivedCategory.Q ⋙ jD ⟶ j.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φk : DerivedCategory.Q ⋙ kD ⟶ k.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (φm : DerivedCategory.Q ⋙ mD ⟶ m.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

end TransportCube

private theorem cancel_transport_square
    {C : Type*} [Category C] {X Y Z W V : C}
    (a : X ≅ Y) (b : Z ≅ W) (c : V ≅ Z) (t : X ⟶ V) (s : Y ⟶ W)
    (h : t ≫ c.hom ≫ b.hom = a.hom ≫ s) :
    s ≫ b.inv ≫ c.inv = a.inv ≫ t := by
  apply (cancel_epi a.hom).1
  apply (cancel_mono (c.hom ≫ b.hom)).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id, Category.comp_id] using h.symm

section Ordinary
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  {a : StrictEtaleCoefficientChange O O' ell mu phi index}
  {T S : Scheme.{u}} {g : T ⟶ S}
  {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
  {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
  (UT : StrictEtaleCoefficientTransport a T PTA PTB)
  (US : StrictEtaleCoefficientTransport a S PSA PSB)
  (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)

private abbrev transport_underlying (V : Scheme.{u}) (n : ℕ) :
    restrictScalars ((sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf V n)) ⋙
        coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n) ≅
      coefficientUnderlying (J := V.smallEtaleTopology) O' mu n :=
  isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf V n))
    (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))

private theorem transport_insertion_formula (V : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel V O ell (index n)) :
    (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) M) =
      (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map
          ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n)).unit.app M) ≫
        (transport_underlying (a := a) V n).hom.app
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).obj M) := by
  dsimp only [siteTensorUnitUnderlying, transport_underlying, coefficientUnderlying,
    CategoryTheory.Functor.comp_map, isoWhiskerRight_hom, whiskerRight_app]
  simp only [CategoryTheory.Functor.map_comp]

private theorem transport_insertion_naturality
    (V : Scheme.{u}) (n : ℕ) {M N : strictEtaleLevel V O ell (index n)} (f : M ⟶ N) :
    (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map f ≫
        (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) N) =
      (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) M) ≫
        (coefficientUnderlying (J := V.smallEtaleTopology) O' mu n).map
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).map f) := by
  have hu := congrArg
    ((coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map)
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n)).unit.naturality f)
  have hq := (transport_underlying (a := a) V n).hom.naturality
    ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).map f)
  simp only [transport_insertion_formula, CategoryTheory.Functor.map_comp, Category.assoc] at hu ⊢
  dsimp only [coefficientUnderlying, CategoryTheory.Functor.comp_map,
    CategoryTheory.Functor.id_map] at hu hq ⊢
  rw [reassoc_of% hu, hq]

private theorem transport_transpose (V : Scheme.{u}) (n : ℕ)
    (M : strictEtaleLevel V O ell (index n)) (N : strictEtaleLevel V O' mu n)
    (f : (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf V n)).obj M ⟶ N) :
    (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n)).map
        ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n)).homEquiv M N f) ≫
        (transport_underlying (a := a) V n).hom.app N =
      (sheafCompose V.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf V n) M) ≫
        (coefficientUnderlying (J := V.smallEtaleTopology) O' mu n).map f := by
  rw [transport_insertion_formula]
  simpa only [Category.assoc] using
    transpose_underlying (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf V n))
      (coefficientUnderlying (J := V.smallEtaleTopology) O ell (index n))
      (coefficientUnderlying (J := V.smallEtaleTopology) O' mu n)
      (transport_underlying (a := a) V n) M N f

-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem scalar_insertion_ext (n : ℕ)
    (M : strictEtaleLevel S O ell (index n)) (N : strictEtaleLevel T O' mu n)
    (f k : (B.lift n).modules.obj
      ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) ⟶ N)
    (he : (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map f =
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map k) : f = k := by
  apply ((B.levelAdj n).homEquiv _ N).injective
  apply ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf S n)).homEquiv M _).injective
  apply (coefficientUnderlying (J := S.smallEtaleTopology) O ell (index n)).map_injective
  apply (cancel_mono ((transport_underlying (a := a) S n).hom.app
    ((B.right n).obj N) ≫ (B.rightUnderlying n).hom.app N)).1
  have hf := transport_transpose (a := a) S n M ((B.right n).obj N)
    ((B.levelAdj n).homEquiv _ _ f)
  have hk := transport_transpose (a := a) S n M ((B.right n).obj N)
    ((B.levelAdj n).homEquiv _ _ k)
  erw [reassoc_of% hf, reassoc_of% hk]
  have tf := B.levelTranspose n ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) N f
  have tk := B.levelTranspose n ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) N k
  dsimp only [coefficientUnderlying, CategoryTheory.Functor.comp_map] at tf tk
  erw [tf, tk]
  erw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left]
  apply congrArg ((strictEtaleSetAdjunction g).homEquiv _ _)
  exact he

-- Nested coefficient and inverse-image transposes require additional elaboration.
private theorem ordinary_evaluation
    {DA : CoefficientDerivedImage A.inverse A.rightSystem A.systemAdj}
    {DB : CoefficientDerivedImage B.inverse B.rightSystem B.systemAdj}
    (square : StrictEtaleInverseTransport UT US A B DA DB) (n : ℕ)
    (e : siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
      (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))
    (he : ∀ M : strictEtaleLevel S O ell (index n),
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M)) ≫
        (B.lift n).moduleUnderlying.inv.app _ ≫
        (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map (e.hom.app M) =
      (A.lift (index n)).moduleUnderlying.inv.app M ≫
        (sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
            ((A.lift (index n)).modules.obj M)))
    (M : strictEtaleCoefficientSystem S O ell) :
    (B.lift n).modules.map ((US.val.evaluation n).inv.app M) ≫
      (B.inverseEvaluation n).inv.app (US.ordinary.obj M) ≫
      (coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n).map
        (square.val.1.hom.app M) =
    e.hom.app (M.level (index n)) ≫
      (siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).map
        ((A.inverseEvaluation (index n)).inv.app M) ≫
      (UT.val.evaluation n).inv.app (A.inverse.obj M) := by
  apply scalar_insertion_ext B n (M.level (index n))
  have hs := square.property.1 n M
  have hUS := US.property.2.1 n M
  have hUT := UT.property.2.1 n (A.inverse.obj M)
  have hnB := (B.lift n).moduleUnderlying.inv.naturality
    ((US.val.evaluation n).inv.app M)
  let U := coefficientUnderlying (J := T.smallEtaleTopology) O' mu n
  have hs' := cancel_transport_square
    ((strictEtaleInverseUnderlying A (index n)).app M)
    ((strictEtaleInverseUnderlying B n).app (US.ordinary.obj M))
    ((coefficientEvaluation (J := T.smallEtaleTopology) (O := O') (ell := mu) n ⋙ U).mapIso
      (square.val.1.app M).symm)
    ((UT.setUnit n).app (A.inverse.obj M))
    ((Scheme.etaleSetPullback g).map ((US.setUnit n).app M)) hs
  dsimp only [strictEtaleInverseUnderlying, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    Iso.symm_hom, Iso.symm_inv,
    Iso.trans_inv, NatTrans.comp_app, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    whiskerRight_app, whiskerLeft_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.comp_map] at hs'
  simp only [Category.comp_id, Category.assoc] at hs'
  have hnat' := transport_insertion_naturality (a := a) T n
    ((A.inverseEvaluation (index n)).inv.app M)
  simp only [CategoryTheory.Functor.map_comp]
  dsimp only [underlying, coefficientUnderlying, CategoryTheory.Functor.comp_map] at hnB ⊢
  -- Focus on each composition so rewriting does not unfold unrelated sheaf maps.
  conv_lhs =>
    arg 2
    erw [← reassoc_of% hnB]
  conv_lhs =>
    rw [← (Scheme.etaleSetPullback g).map_comp_assoc]
    rw [← CategoryTheory.Functor.map_comp, ← hUS]
  conv_rhs =>
    erw [reassoc_of% he (M.level (index n))]
    arg 2
    erw [← reassoc_of% hnat']
  have hUT' := congrArg
    ((sheafCompose T.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map) hUT
  simp only [CategoryTheory.Functor.map_comp] at hUT'
  conv_rhs =>
    arg 2; arg 2
    erw [← hUT']
  exact hs'

-- Nested coefficient and inverse-image transposes require additional elaboration.
-- Nested coefficient and inverse-image transposes require additional elaboration.
-- Nested coefficient and inverse-image transposes require additional elaboration.
attribute [local semireducible] siteCoefficientTensor

end Ordinary

-- Keep the two localization calculations abstract from the chosen comparisons.
end AlgebraicGeometry
