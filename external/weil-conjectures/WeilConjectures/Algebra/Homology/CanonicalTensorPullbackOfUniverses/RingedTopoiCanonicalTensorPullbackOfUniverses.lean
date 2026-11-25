/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
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
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedResolvingPairRestriction
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.DerivedPullbackRepresentativeComputationSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Canonical tensor pullback with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).

This is the general canonical representative interface, with a site-object universe s and an
independent site-morphism universe h. Rings and modules live in max s h, as in the
published K-flat interface. Both sites retain their actual Hom universe. The ring map is arbitrary,
  including coefficient quotients, and
the geometric morphism can be the etale-to-pro-etale comparison. The pure-tensor,
unit and signed total-complex normalizations are retained verbatim. Public imports
retain both earlier interfaces for existing callers.
-/

@[expose] public section

set_option autoImplicit false

universe s h w

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.CanonicalTensorPullbackOfUniverses

set_option backward.isDefEq.respectTransparency false

-- The essentially-small sheafification instance leaves its universe unconstrained here.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v u' v'

private theorem tensorMap_factor
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor A) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

private theorem tensorPullbackTotal_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap
      ((L.mapHomologicalComplex (.up ℤ)).map f)
      ((L.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor B) (.up ℤ) ≫
        tensorPullbackTotal L e he P' Q' =
      tensorPullbackTotal L e he P Q ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)) := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (L.map a ⊗ₘ L.map b) ≫ (e X' Y').inv =
        (e X Y).inv ≫ L.map (a ⊗ₘ b) := by
    apply (cancel_mono (e X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  change (L.map (f.f a) ▷ L.obj (Q.X b)) ≫
    (L.obj (P'.X a) ◁ L.map (g.f b)) ≫ _ = _
  rw [← tensorHom_def_assoc]
  change (L.map (f.f a) ⊗ₘ L.map (g.f b)) ≫ (e (P'.X a) (Q'.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) a b n hab) =
    (e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n hab) ≫
        L.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).f n)
  rw [← Category.assoc, hi, Category.assoc, ← L.map_comp]
  congr 2
  rw [← L.map_comp]
  congr 1
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, Category.assoc]
  rfl

set_option synthInstance.maxSize 2048 in
-- Elaborate the full two-variable representative square.
/-- Canonical derived comparison, uniquely characterized on K-flat flat-term representatives.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: resolve both inputs by K-flat flat-term complexes; pullback preserves that class
by 0G7E. Their total tensor is K-flat by reassociating an acyclic test tensor and applying
K-flatness twice, and has flat terms by tensor-flatness and countable flat sums.
The left-derived comparison computes pullback on these representatives. Compose it
with the inverse image of the explicit chain comparison k.totalIso and rS. The displayed
square records exactly this construction relative to rR. Naturality of the summand
comparisons handles both differentials and their signs. Two-variable tensor descent
extends the square to all derived objects and makes its extension unique. The ordinary
unit normalization is canonicalRingedTensorComparison_unit, forced by k.pure. -/
theorem ringedTopoiCanonicalDerivedTensorPullback
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {S RI : Sheaf JD CommRingCat.{max s h}}
    (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))
    (hobj : ∀ M : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R), uStar.obj M =
        changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)} (a : M ⟶ N),
        uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) (ComplexShape.up
        ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S) (P.X n))
    (TR : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am :
      uStar ⊣ V) :
    (∀ P : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
        CochainComplex.IsAcyclicTensorKFlat
          ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          ∀ n : ℤ,
            IsFlatOnSite (J := JD) (R := S)
              (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n)) ∧
    ∃! alpha : TR ⋙ LF ≅ (LF.prod LF) ⋙ TS,
      ∀ (P Q : CochainComplex (SheafOfModules.{max s h} ((sheafCompose JC (forget₂
        CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) ℤ) (hp : PR P) (hq : PR Q),
        ∃ (hp' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hq' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          LF.map (rR.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
                TS.map (CategoryTheory.Prod.mkHom
                  (derivedPullbackComplexComparison uStar LF epsilon P)
                  (derivedPullbackComplexComparison uStar LF epsilon Q)) =
            derivedPullbackComplexComparison uStar LF epsilon
              (CochainComplex.mapBifunctor P Q
                (@curriedTensor (SheafOfModules.{max s h} ((sheafCompose JC (forget₂
                  CommRingCat.{max s h}
      RingCat.{max s h})).obj R)) _ (monoidalCategory R))) ≫
              (DerivedCategory.Q.mapIso
                (k.totalIso R S RI uInv I c uStar hobj V am P Q)).inv ≫
                  rS.hom.app
                    (⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, hp'⟩,
                      ⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q, hq'⟩) := by
  have hpres : ∀ P : CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat →
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) →
      CochainComplex.IsAcyclicTensorKFlat
        ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S)
        (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n) := by
    intro P hp hf
    exact isKFlat_ringedToposPullback uInv uPush adj I c uStar hobj hmap P hp hf
  let A := SheafOfModules.{max s h}
    ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)
  let B := SheafOfModules.{max s h}
    ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)
  let F := uStar.mapHomologicalComplex (.up ℤ)
  let tR := Functor.uncurry.obj ((@curriedTensor A _ (monoidalCategory R)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((@curriedTensor B _ (monoidalCategory S)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let eps : DerivedCategory.Q ⋙ LF ⟶ F ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv LF ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) epsilon ≫
      Functor.whiskerRight (uStar.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso B).hom
  have hF : ∀ P, PR P → PS (F.obj P) := by
    intro P hp
    exact (hPS _).2 (hpres P ((hPR _).1 hp).1 ((hPR _).1 hp).2)
  set_option backward.isDefEq.respectTransparency true in
    have hc := derivedPullback_kflat_tensor_computation.{s, h, w}
      (C := C) (D := D) (JC := JC) (JD := JD) (R := R) (S := S) (RI := RI)
      uInv uPush adj I c uStar hobj hmap LF epsilon hLF
  obtain ⟨he, het⟩ := hc
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun X ↦ k.totalIso R S RI uInv I c uStar hobj V am X.1 X.2)
    (by
      intro X Y f
      let := monoidalCategory R
      let := monoidalCategory S
      let := ringedTensorPreadditive R
      let := ringedTensorPreadditive S
      dsimp only [F, tR, tS, Functor.comp_map, Functor.prod_map,
        CanonicalRingedTensorComparison.totalIso, CanonicalRingedTensorComparison.total]
      simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
        asIso_hom, tensorMap_factor]
      exact
        (tensorPullbackTotal_naturality uStar k.mu k.naturality f.1 f.2))
  let b := b0.symm
  have hres : ∀ X : CochainComplex A ℤ,
      ∃ (P : CochainComplex A ℤ) (f : P ⟶ X), PR P ∧ QuasiIso f := by
    intro X
    obtain ⟨P, f, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X
    have hflat : ∀ n, IsFlatOnSite (J := JC) (R := R) (P.X n) := by
      intro n
      exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
    exact ⟨P, f, (hPR P).2 ⟨hp, hflat⟩, hq⟩
  set_option backward.isDefEq.respectTransparency true in
    have hff := CategoryTheory.derivedResolvingPairRestriction (DerivedCategory B) PR hres
  obtain ⟨ff'⟩ := hff
  set_option backward.isDefEq.respectTransparency true in
    have hdes := CategoryTheory.tensorComparisonDescent
      (K := CochainComplex A ℤ) (H := CochainComplex B ℤ)
      (D := DerivedCategory A) (E := DerivedCategory B)
      DerivedCategory.Q DerivedCategory.Q F LF eps PR PS hF ff' tR tS TR TS rR rS b
      (fun P hp ↦ he P ((hPR _).1 hp).1 ((hPR _).1 hp).2)
      (fun P Q hp hq ↦ het P Q ((hPR _).1 hp).1 ((hPR _).1 hp).2
        ((hPR _).1 hq).1 ((hPR _).1 hq).2)
  obtain ⟨alpha, ha, hu⟩ := hdes
  have heps (P : CochainComplex A ℤ) :
      eps.app P = derivedPullbackComplexComparison uStar LF epsilon P := rfl
  have hb (P Q : CochainComplex A ℤ) :
      DerivedCategory.Q.map (b.hom.app (P, Q)) =
        (DerivedCategory.Q.mapIso
          (k.totalIso R S RI uInv I c uStar hobj V am P Q)).inv := rfl
  refine ⟨hpres, alpha, ?_, ?_⟩
  · intro P Q hp hq
    refine ⟨hF P hp, hF Q hq, ?_⟩
    have hh := ha P Q hp hq
    simp only [heps, hb] at hh
    exact hh
  · intro alpha' ha'
    apply hu alpha'
    intro P Q hp hq
    set_option backward.isDefEq.respectTransparency true in
      obtain ⟨hp', hq', hh⟩ := ha' P Q hp hq
    simp only [heps, hb]
    exact hh

set_option synthInstance.maxSize 2048 in
-- Keep both tensor representative interfaces explicit.
/-- The canonical derived comparison selected by its unique representative characterization.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
The theorem specifies the natural isomorphism uniquely, so only its proof is postponed. -/
noncomputable def ringedTopoiCanonicalDerivedTensorComparison
    {C D : Type s} [Category.{h} C] [Category.{h} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{max s h}} {S RI : Sheaf JD CommRingCat.{max s h}}
    (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
    (uPush : Sheaf JD (Type (max s h)) ⥤ Sheaf JC (Type (max s h)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))
    (hobj : ∀ M : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R), uStar.obj M =
        changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)} (a : M ⟶ N),
        uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) (ComplexShape.up
        ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n))
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, IsFlatOnSite (J := JD) (R := S) (P.X n))
    (TR : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ×
        (DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S))) ⥤
        DerivedCategory
      (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JC (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max s h}
      ((sheafCompose JD (forget₂ CommRingCat.{max s h} RingCat.{max s h})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
      RingCat.{max s h})).obj S) ⥤
      SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj R)) (am :
      uStar ⊣ V) :
    TR ⋙ LF ≅ (LF.prod LF) ⋙ TS :=
  Classical.choose (ringedTopoiCanonicalDerivedTensorPullback uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).2.exists

end SheafOfModules.CanonicalTensorPullbackOfUniverses
