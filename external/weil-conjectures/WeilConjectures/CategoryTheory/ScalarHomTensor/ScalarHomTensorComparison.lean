/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarHomExtensionKFlat
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Normalized scalar tensor comparison on unbounded derived categories

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
open SheafOfModules WeilConjectures
namespace CategoryTheory.ScalarHomTensor
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

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory scalarPairComplexComparison
  CoefficientTensorModels.iso

/-- The normalized strong tensor comparison for scalar extension.
Source: Stacks 07A4 (blueprint: lem-sfb-scalar-tensor-comparison).

Proof: use the normalized ordinary tensor comparison in each bidegree and sum its
inverse over the total coproduct. Naturality commutes with both differentials and
additivity preserves the signs. Left adjoints preserve the coproducts, giving a chain
isomorphism whose summand formula is the required generator formula. Scalar extension
preserves all K-flat complexes by tensor cancellation. The universal derived comparison
is invertible on them and their total tensors. Fully faithful restriction to resolving
K-flat representatives descends the chain comparison and gives exactly the recorded
normalization square. -/
theorem scalarHomTensorComparison_exists : Nonempty (ScalarHomTensorComparison M a) := by
  classical
  let s := M.scalar a
  let A := scalarModules J R
  let B := scalarModules J S
  let := monoidalCategory R
  let := monoidalCategory S
  let := symmetricCategory R
  let := symmetricCategory S
  let := s.extension_additive
  have (X : A) : (tensorLeft X).Additive := tensorLeft_additive_independent R X
  have (X : A) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  have (X : B) : (tensorLeft X).Additive := tensorLeft_additive_independent S X
  have (X : B) : (tensorRight X).Additive :=
    Functor.additive_of_iso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y)
        (fun f ↦ BraidedCategory.braiding_naturality_right X f))
  let : MonoidalPreadditive A :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let : MonoidalPreadditive B :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  obtain ⟨e, he, hgen⟩ :=
    SheafOfModules.ScalarHomOrdinary.scalarOrdinaryTensorComparison_exists a s
  let F := scalarComplex s.extension s.extension_additive
  let tR := coefficientTotalTensor.{r, c, v} J R
  let tS := coefficientTotalTensor.{r, c, v} J S
  have hiso (P Q : CochainComplex A ℤ) :
      IsIso (tensorPullbackTotal s.extension e he P Q) :=
    tensorPullbackTotal_isIso s.extension e he (scalarRestriction a) s.ordinaryAdjunction P Q
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (tensorPullbackTotal s.extension e he X.1 X.2)
      (hiso X.1 X.2)) (by
        intro X Y f
        dsimp only [F, tR, tS, scalarComplex, Functor.comp_map, Functor.prod_map]
        simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
          Functor.map₂HomologicalComplex, asIso_hom, tensorMap_factor]
        exact tensorPullbackTotal_naturality s.extension e he f.1 f.2)
  let b := b0.symm
  have hg (P Q : CochainComplex A ℤ) (p q k : ℤ) (h : p + q = k)
      (V : Cᵒᵖ) (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
      ((b.app (P, Q)).hom.f k).val.app V
          (scalarHomUnitSection M a _ V
            (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
        coefficientTensorGenerator.{r, c, v} J S (F.obj P) (F.obj Q) p q k h V
          (scalarHomUnitSection M a _ V x) (scalarHomUnitSection M a _ V y) := by
    let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor A) p q k h
    let ι' := CochainComplex.ιMapBifunctor (F.obj P) (F.obj Q) (curriedTensor B) p q k h
    let z := (HomologicalComplex.eval B (.up ℤ) k).mapIso (b0.app (P, Q))
    have hz : ι' ≫ z.hom = (e (P.X p) (Q.X q)).inv ≫ s.extension.map ι := by
      change ι' ≫ tensorPullbackTotalComponent s.extension e P Q k = _
      exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
    have hi : s.extension.map ι ≫ z.inv = (e (P.X p) (Q.X q)).hom ≫ ι' := by
      apply (cancel_mono z.hom).mp
      erw [Category.assoc, z.inv_hom_id, Category.comp_id, Category.assoc, hz,
        Iso.hom_inv_id_assoc]
    have hu := congrArg (fun f ↦ f.val.app V
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))
      (s.ordinaryAdjunction.unit.naturality ι)
    have hh := congrArg (fun f ↦ f.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) hi
    change z.inv.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V)
        (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y))) = _
    change ((s.ordinaryAdjunction.unit.app _).val.app V)
      (ι.val.app V (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) =
      (s.extension.map ι).val.app V (((s.ordinaryAdjunction.unit.app _).val.app V)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) V x y)) at hu
    erw [hu]
    exact hh.trans (congrArg (ι'.val.app V) (hgen _ _ V x y))
  let PR : ObjectProperty (CochainComplex A ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
  let PS : ObjectProperty (CochainComplex B ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
  have hF : ∀ P, PR P → PS (F.obj P) :=
    fun P hp ↦ scalarExtension_preservesKFlat a s P hp
  let eps : DerivedCategory.Q ⋙ s.derived ⟶ F ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv s.derived ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) s.counit ≫
      Functor.whiskerRight (s.extension.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso B).hom
  have heps (P : CochainComplex A ℤ) : eps.app P =
      scalarPairComplexComparison s.extension s.extension_additive s.derived s.counit P := by
    change s.derived.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
      s.counit.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ (DerivedCategory.quotientCompQhIso B).hom.app
        (F.obj P) = _
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    unfold scalarPairComplexComparison
    rfl
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, _, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  have hff := resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  obtain ⟨ff⟩ := hff
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  obtain ⟨alpha, ha, _⟩ := tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F s.derived eps PR PS hF ff' tR tS
    (M.closed R).tensor (M.closed S).tensor (M.model R).comparison (M.model S).comparison b
    (fun P hp ↦ by rw [heps]; exact s.computes P hp)
    (fun P Q hp hq ↦ by
      rw [heps]
      exact s.computes _ (coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hp hq))
  refine ⟨{ preservesKFlat := hF
            complexIso := fun P Q ↦ b.app (P, Q)
            generators := hg
            iso := alpha
            normalization := ?_ }⟩
  intro P Q hp hq
  have hh := ha P Q hp hq
  rw [heps, heps, heps] at hh
  simpa only [CoefficientTensorModels.iso, Iso.app_hom] using hh

end CategoryTheory.ScalarHomTensor
