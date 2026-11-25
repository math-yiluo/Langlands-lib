/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorCoherence
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.Derived.DerivedResolvingPairRestriction
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Tensor descent under exact ringed forgetting

Source: Stacks 06YU, 0G7D, 0FPT
(blueprint: lem-sf-ringed-forget-tensor-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

-- Keep the chosen internal-Hom and localization constructions behind their APIs.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

section TotalComparison

variable {B : Type b} [Category.{vb} B] [Preadditive B]
  {A : Type a} [Category.{va} A] [Preadditive A]
  (V : B ⥤ B ⥤ B) [V.PreservesZeroMorphisms]
  [∀ X, (V.obj X).PreservesZeroMorphisms]
  (W : A ⥤ A ⥤ A) [W.PreservesZeroMorphisms]
  [∀ X, (W.obj X).PreservesZeroMorphisms]
  (F : B ⥤ A) [F.Additive]
  (e : Functor.uncurry.obj V ⋙ F ≅ (F.prod F) ⋙ Functor.uncurry.obj W)

private def curryComparison :
    (Functor.postcompose₂.obj F).obj V ≅
      (((Functor.whiskeringLeft₂ A).obj F).obj F).obj W :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun Y ↦ e.app (X, Y)) (by
    intro Y Y' g
    simpa using e.hom.naturality (X := (X, Y)) (Y := (X, Y')) (𝟙 X, g))) (by
    intro X X' f
    apply NatTrans.ext
    funext Y
    simpa using e.hom.naturality (X := (X, Y)) (Y := (X', Y)) (f, 𝟙 Y))

variable [∀ P Q : CochainComplex B ℤ, P.HasMapBifunctor Q V]
  [∀ P Q : CochainComplex A ℤ, P.HasMapBifunctor Q W]
  [∀ I : Type, PreservesColimitsOfShape (Discrete I) F]

private def totalComparison (P Q : CochainComplex B ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (CochainComplex.mapBifunctor P Q V) ≅
      CochainComplex.mapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) W :=
  asIso (HomologicalComplex.mapBifunctorComparison
    (curryComparison V W F e).hom (.up ℤ) P Q)

private theorem totalComparison_summand (P Q : CochainComplex B ℤ)
    (p q n : ℤ) (h : p + q = n) :
    F.map (CochainComplex.ιMapBifunctor P Q V p q n h) ≫
        (totalComparison V W F e P Q).hom.f n =
      e.hom.app (P.X p, Q.X q) ≫
        CochainComplex.ιMapBifunctor ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) W p q n h :=
  HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (curryComparison V W F e).hom (.up ℤ) P Q p q n h

private theorem totalComparison_naturality
    {P P' Q Q' : CochainComplex B ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g V (.up ℤ)) ≫
        (totalComparison V W F e P' Q').hom =
      (totalComparison V W F e P Q).hom ≫
        HomologicalComplex.mapBifunctorMap
          ((F.mapHomologicalComplex (.up ℤ)).map f)
          ((F.mapHomologicalComplex (.up ℤ)).map g) W (.up ℤ) :=
  HomologicalComplex.mapBifunctorComparison_naturality
    (curryComparison V W F e).hom (.up ℤ) f g

private def totalComparisonNatIso :
    Functor.uncurry.obj (V.map₂CochainComplex) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj (W.map₂CochainComplex) :=
  NatIso.ofComponents (fun X ↦ totalComparison V W F e X.1 X.2) (by
    intro X Y f
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
      Functor.map₂CochainComplex, Functor.map₂HomologicalComplex,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
      Functor.map₂HomologicalComplex_obj_map, Functor.map₂HomologicalComplex_map_app]
    rw [Functor.map_comp]
    rw [Category.assoc, totalComparison_naturality, ← Category.assoc,
      totalComparison_naturality, Category.assoc]
    simp)

end TotalComparison

private def uncurryTensorIso {B : Type b} [Category.{vb} B] [MonoidalCategory B] :
    Functor.uncurry.obj (curriedTensor B) ≅ MonoidalCategory.tensor B :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      MonoidalCategory.tensor_map, Iso.refl_hom, Category.id_comp,
      Category.comp_id]
    exact (MonoidalCategory.tensorHom_def f.1 f.2).symm)

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

private def flatModels :
    ObjectProperty (CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) :=
  fun P ↦ P.IsKFlatIndependentCoefficients ∧
    ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)

private theorem flatModels_fullyFaithful
    [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
    (E : Type a) [Category.{va} E] :
    let P := flatModels.{c, v, r} J R
    Nonempty (((Functor.whiskeringLeft (P.FullSubcategory × P.FullSubcategory)
      (DerivedCategory (RingedTensorModules.{c, v, r} J R) ×
        DerivedCategory (RingedTensorModules.{c, v, r} J R)) E).obj
          ((P.ι ⋙ DerivedCategory.Q.{wb}).prod
            (P.ι ⋙ DerivedCategory.Q.{wb}))).FullyFaithful) := by
  apply derivedResolvingPairRestriction E (flatModels.{c, v, r} J R)
  intro X
  obtain ⟨M, a, hM, hf, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
  refine ⟨M, a, ⟨hM, ?_⟩, ha⟩
  intro n
  unfold SheafOfModules.IsFlatOnSite
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (M.X n)).symm (hf n)

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

section

attribute [local irreducible] coefficientTotalTensor tensorSummand

/-- The tensor-only comparison, before comparing closed adjunctions.
Source: Stacks 06YU, 0FPT
(blueprint: lem-sf-ringed-forget-tensor-descent). -/
structure TensorComparison where
  /-- The sum of the specified underived comparisons, on actual total tensor complexes. -/
  chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
    ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
      coefficientTotalTensor.{s, d, vd} J' R'
  /-- Every summand is the specified underived tensor comparison. -/
  summand (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n) :
    U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
      u.tensor.hom.app (P.X p, Q.X q) ≫
        tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq
  /-- The natural derived isomorphism μ, in the orientation of the node. -/
  derived : SB.tensor ⋙ U.mapDerivedCategory ≅
    (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor
  /-- The extension agrees with the total comparison on all flat-term K-flat models. -/
  representative : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
    J R J' R' U SB TB SA TA chain derived.hom
  /-- μ preserves units, associators and the specified signed symmetry. -/
  coherence : TensorCoherence SB.monoidal SA.monoidal βB βA U.mapDerivedCategory derived
  /-- Its unit is the localization of the given underived unit comparison. -/
  unit_normalization :
    coherence.unit.hom ≫ cA.unitIso.hom =
      U.mapDerivedCategory.map cB.unitIso.hom ≫
        U.mapDerivedCategoryFactors.hom.app (ringedTensorUnitComplex.{c, v, r} J R) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map (u.coherence.unit).hom)

end

omit [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes] in
private theorem derivedComparison_exists
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p))) :
    ∃ μ : SB.tensor ⋙ U.mapDerivedCategory ≅
        (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor,
      RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
        J R J' R' U SB TB SA TA chain μ.hom := by
  let P := flatModels.{c, v, r} J R
  let K := P.ι
  let KB := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)) K
    (fun X ↦ X.property.1)
  obtain ⟨FF⟩ := flatModels_fullyFaithful.{_, _, c, v, r, wb} J R
    (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
  obtain ⟨μ, hμ, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q (U.mapHomologicalComplex (.up ℤ))
    U.mapDerivedCategory U.mapDerivedCategoryFactors.hom P
    (CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R'))
    (fun X hX ↦ (hU X hX.1 hX.2).1) FF
    (coefficientTotalTensor.{r, c, v} J R) (coefficientTotalTensor.{s, d, vd} J' R')
    SB.tensor SA.tensor (Functor.isoWhiskerLeft (KB.prod KB) TB.comparison)
    TA.comparison chain (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  refine ⟨μ, ?_⟩
  intro X Y hX hY hUX hUY hfX hfY
  exact hμ X Y ⟨hX, hfX⟩ ⟨hY, hfY⟩

omit [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes] in
private theorem representative_unique
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (μ ν : SB.tensor ⋙ U.mapDerivedCategory ⟶
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ)
    (hν : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain ν) : μ = ν := by
  obtain ⟨FF⟩ := flatModels_fullyFaithful.{_, _, c, v, r, wb} J R
    (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
  apply FF.map_injective
  apply NatTrans.ext
  funext X
  change μ.app (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj) =
    ν.app (DerivedCategory.Q.obj X.1.obj, DerivedCategory.Q.obj X.2.obj)
  have hX := X.1.property
  have hY := X.2.property
  have hUX := (hU X.1.obj hX.1 hX.2).1
  have hUY := (hU X.2.obj hY.1 hY.2).1
  apply (cancel_epi (U.mapDerivedCategory.map
    (TB.iso J R SB X.1.obj X.2.obj hX.1 hY.1).hom)).1
  have : IsIso (Prod.mkHom (U.mapDerivedCategoryFactors.hom.app X.1.obj)
      (U.mapDerivedCategoryFactors.hom.app X.2.obj)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  apply (cancel_mono (SA.tensor.map
    (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj X.1.obj),
      U.mapDerivedCategory.obj (DerivedCategory.Q.obj X.2.obj)))
    (Y := (DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj X.1.obj),
      DerivedCategory.Q.obj ((U.mapHomologicalComplex (.up ℤ)).obj X.2.obj)))
    (U.mapDerivedCategoryFactors.hom.app X.1.obj,
      U.mapDerivedCategoryFactors.hom.app X.2.obj))).1
  simpa only [Category.assoc] using
    (hμ X.1.obj X.2.obj hX.1 hY.1 hUX hUY hX.2 hY.2).trans
      (hν X.1.obj X.2.obj hX.1 hY.1 hUX hUY hX.2 hY.2).symm

/-- The summandwise underived comparison extends uniquely and coherently to derived tensors.
This assertion concerns tensors only; it has no internal-Hom comparison or transpose law.

Source: Stacks 06YU, 0G7D, 0FPT; steps 1--4 of
lem-sf-ringed-forget-tensor-transposition
(blueprint: lem-sf-ringed-forget-tensor-descent).

Proof: take coproducts of the given tensor comparison in total degree n. The coproduct
inclusions show that the resulting maps commute with both tensor differentials:
naturality handles d tensor 1 and 1 tensor d, and additivity preserves (-1)^p.
The inverse maps give a natural chain isomorphism. Restrict to flat-term K-flat pairs;
the image pairs are K-flat by the displayed hypothesis. Transport the localized chain
comparison across the two specified tensor-model isomorphisms. The transformation
extension bijection in site-derived-tensor-descent extends it uniquely. Extend its
inverse as well; injectivity proves the composites are identities. On triple summands,
underived associativity gives derived associativity. Unit diagrams are the given unit
diagrams in each degree. Symmetry is the underived swap times (-1)^(pq), preserved by
additivity. Tensor closure of flat-term K-flat complexes makes these tests legitimate;
K-flat resolutions and naturality extend the coherence equations to all objects.
The degree-zero unit comparison is exactly the two single-complex factors displayed
in unit_normalization. Finally the same extension bijection gives uniqueness even
among arbitrary natural transformations, not only among isomorphisms. -/
theorem ringed_forget_tensor_descent
    [∀ I : Type (max c v r), PreservesColimitsOfShape (Discrete I) U]
    (_preserves_flat_models :
      ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
        P.IsKFlatIndependentCoefficients →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R) (P.X p)) →
        CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
          ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
            (R := R') (U.obj (P.X p))) :
    ∃ m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
        J R J' R' U u SB TB βB cB SA TA βA cA,
      ∀ μ' : SB.tensor ⋙ U.mapDerivedCategory ⟶
          (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor,
        RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
          J R J' R' U SB TB SA TA m.chain μ' → μ' = m.derived.hom := by
  let B := RingedTensorModules.{c, v, r} J R
  let A := RingedTensorModules.{d, vd, s} J' R'
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let : MonoidalCategory B := SheafOfModules.monoidalCategory R
  let : MonoidalCategory A := SheafOfModules.monoidalCategory R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  have (I : Type) : PreservesColimitsOfShape (Discrete I) U :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift.{max c v r, 0} : ULift.{max c v r} I ≃ I)) U
  let e : Functor.uncurry.obj (curriedTensor B) ⋙ U ≅
      (U.prod U) ⋙ Functor.uncurry.obj (curriedTensor A) :=
    Functor.isoWhiskerRight uncurryTensorIso U ≪≫ u.tensor ≪≫
      Functor.isoWhiskerLeft (U.prod U) uncurryTensorIso.symm
  have he (X Y : B) : e.hom.app (X, Y) = u.tensor.hom.app (X, Y) := by
    change U.map (𝟙 _) ≫ u.tensor.hom.app (X, Y) ≫ 𝟙 _ = _
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]
  let chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R' :=
    totalComparisonNatIso (curriedTensor B) (curriedTensor A) U e
  have hsummand : ∀ (P Q : CochainComplex B ℤ) (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq := by
    intro P Q p q n h
    change U.map (CochainComplex.ιMapBifunctor P Q (curriedTensor B) p q n h) ≫
      (totalComparison (curriedTensor B) (curriedTensor A) U e P Q).hom.f n =
      u.tensor.hom.app (P.X p, Q.X q) ≫
        CochainComplex.ιMapBifunctor ((U.mapHomologicalComplex (.up ℤ)).obj P)
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor A) p q n h
    rw [totalComparison_summand, he]
  obtain ⟨μ, hμ⟩ := derivedComparison_exists J R J' R' U SB TB SA TA chain _preserves_flat_models
  obtain ⟨hc, hunit⟩ := ringed_forget_tensor_coherence J R J' R' U u SB TB βB cB SA TA βA cA
    _preserves_flat_models chain hsummand μ hμ
  let m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA :=
    { chain := chain
      summand := hsummand
      derived := μ
      representative := hμ
      coherence := hc
      unit_normalization := hunit }
  refine ⟨m, ?_⟩
  intro ν hν
  exact representative_unique J R J' R' U SB TB SA TA chain _preserves_flat_models
    ν μ.hom hν hμ

end CategoryTheory.RingedForgetTensorTransposition
