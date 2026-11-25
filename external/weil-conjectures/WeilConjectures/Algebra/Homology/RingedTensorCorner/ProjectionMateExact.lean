/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
import WeilConjectures.Mathlib.CategoryTheory.Shift.Localization

/-!
# Exact projection mates for ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56;
Derived Categories, Tag 0A8D (blueprint: lem-weil-pbc-ringed-projection-mate-exact).
-/

@[expose] public section

universe u w

set_option Elab.async true
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MonoidalCategory

namespace SheafOfModules

section

/-- The module category of a recorded corner; this is a transparent interface abbreviation.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateModules (A : RingedTensorCorner.{u, w}) :=
  ringedSiteModules.{u, u, u, u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

/-- The existing derived category, with the size chosen in the corner.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateDerived (A : RingedTensorCorner.{u, w}) :=
  DerivedCategory A.mateModules

/-- The degree-zero ring complex, the tensor unit before localization.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateUnitComplex (A : RingedTensorCorner.{u, w}) :=
  letI := monoidalCategory A.ring
  HomologicalComplex.tensorUnit A.mateModules (.up ℤ)

/-- The degree-zero ring in the derived category, rather than an arbitrary unit object.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateUnit (A : RingedTensorCorner.{u, w}) :=
  DerivedCategory.Q.obj A.mateUnitComplex

/-- The ordinary tensor bifunctor already used by the representative presentation.
Source: Stacks Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
noncomputable abbrev RingedTensorCorner.mateTensor (A : RingedTensorCorner.{u, w}) :=
  KFlatFixedTensor.ordinaryTensor A.ring

/-- Flat-term K-flat representatives, with the same predicate as `RingedTensorModel`.
Source: Stacks Tags 06YS, 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
abbrev RingedTensorCorner.mateFlat (A : RingedTensorCorner.{u, w}) :
    ObjectProperty (CochainComplex A.mateModules ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

attribute [local instance 4000] KFlatFixedTensor.tensorAdditive
  KFlatFixedTensor.tensorObjAdditive KFlatFixedTensor.tensorHasMapBifunctor

/-- Canonical representative shift equations for a tensor localized from cochain complexes.
This is the same unsigned first shift and signed second shift used by ringed tensor models.
Source: Stacks, Tag 06YU (blueprint: lem-weil-pbc-ringed-projection-mate-exact). -/
def MateCanonicalShiftData
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (T : D × D ⥤ D) [(Functor.curryObj T).CommShift₂Int]
    (flat : ObjectProperty (CochainComplex C ℤ))
    (r : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q)) : Prop :=
  (∀ (P : CochainComplex C ℤ) (n : ℤ), flat P → flat (P⟦n⟧)) ∧
  (∀ (P Q : CochainComplex C ℤ) (hP : flat P) (hQ : flat Q)
      (n : ℤ) (hPn : flat (P⟦n⟧)),
    (r (P⟦n⟧) Q hPn hQ).hom ≫
        T.map (Prod.mkHom ((q.commShiftIso n).hom.app P)
          (𝟙 (q.obj Q))) ≫
        (((Functor.curryObj T).flip.obj (q.obj Q)).commShiftIso n).hom.app
          (q.obj P) =
      q.map (CochainComplex.mapBifunctorShift₁Iso P Q F n).hom ≫
        (q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q F) ≫
        (shiftFunctor D n).map ((r P Q hP hQ).hom)) ∧
  (∀ (P Q : CochainComplex C ℤ) (hP : flat P) (hQ : flat Q)
      (n : ℤ) (hQn : flat (Q⟦n⟧)),
    (r P (Q⟦n⟧) hP hQn).hom ≫
        T.map (Prod.mkHom (𝟙 (q.obj P))
          ((q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curryObj T).obj (q.obj P)).commShiftIso n).hom.app
          (q.obj Q) =
      q.map (CochainComplex.mapBifunctorShift₂Iso P Q F n).hom ≫
        (q.commShiftIso n).hom.app
          (CochainComplex.mapBifunctor P Q F) ≫
        (shiftFunctor D n).map ((r P Q hP hQ).hom))


attribute [-instance] cochainModulesMonoidal cochainModulesSymmetric

set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 512

attribute [local irreducible] monoidalCategory siteDerivedTensorIndependentCoefficients
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  CochainComplex.IsAcyclicTensorKFlat CochainComplex.IsKFlatIndependentCoefficients
  KFlatFixedTensor.representativeIso HomologicalComplex₂.total
  MorphismProperty.Q'

-- Diagnose conversion without expanding the tensor definitions.
-- Elaboration must compare the large two-variable localization interfaces.
-- Elaboration must compare the large two-variable localization interfaces.
private def mateCurryIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C × D ⥤ E} (z : F ≅ G) : Functor.curryObj F ≅ Functor.curryObj G :=
  Functor.curry.mapIso z

private def mateFlipCurryIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F G : C × D ⥤ E} (z : F ≅ G) :
    (Functor.curryObj F).flip ≅ (Functor.curryObj G).flip :=
  (flipFunctor _ _ _).mapIso (mateCurryIso z)

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateTensorShiftOfIso {C : Type*} [Category* C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (S T : C × C ⥤ C)
    [(Functor.curryObj T).CommShift₂Int] (z : S ≅ T) :
    ∃ s : (Functor.curryObj S).CommShift₂Int,
      let := s;
      (∀ U, NatTrans.CommShift ((mateCurryIso z).hom.app U) ℤ) ∧
      (∀ V, NatTrans.CommShift
        ((mateFlipCurryIso z).hom.app V) ℤ) := by
  classical
  let W := MorphismProperty.isomorphisms C
  let F := Functor.curryObj T
  let G := Functor.curryObj S
  let lifting : Localization.Lifting₂ (𝟭 C) (𝟭 C) W W F G :=
    ⟨Functor.curry.mapIso z⟩
  let s := Functor.commShift₂OfLocalization (𝟭 C) (𝟭 C) W W F G
    (.int)
  let := s
  refine ⟨s, ?_, ?_⟩
  · intro U
    let d := Functor.CommShift₂OfLocalization.liftingIsoApp
      (𝟭 C) (𝟭 C) W W F G U
    have hd : NatTrans.CommShift d ℤ :=
      Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ)
        (𝟭 C) (𝟭 C) W W F G U
    let := hd
    have hc : NatTrans.CommShift ((Functor.leftUnitor (G.obj U)).inv ≫ d) ℤ :=
      inferInstance
    have he : (Functor.leftUnitor (G.obj U)).inv ≫ d =
        (mateCurryIso z).hom.app U := by
      ext V
      exact Category.id_comp _
    rw [he] at hc
    exact hc
  · intro V
    let d := Functor.CommShift₂OfLocalization.liftingIsoApp
      (𝟭 C) (𝟭 C) W W F.flip G.flip V
    have hd : NatTrans.CommShift d ℤ :=
      Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ)
        (𝟭 C) (𝟭 C) W W F.flip G.flip V
    let := hd
    have hc : NatTrans.CommShift ((Functor.leftUnitor (G.flip.obj V)).inv ≫ d) ℤ :=
      inferInstance
    have he : (Functor.leftUnitor (G.flip.obj V)).inv ≫ d =
        (mateFlipCurryIso z).hom.app V := by
      ext U
      exact Category.id_comp _
    rw [he] at hc
    exact hc

private theorem mateShiftTransportEquation {C : Type*} [Category* C] (F : C ⥤ C)
    {X Y Z A0 A1 A2 B0 B1 B2 : C}
    (rS : X ⟶ A1) (rT : X ⟶ B1) (r0 : Y ⟶ A0) (rT0 : Y ⟶ B0)
    (z1 : A1 ⟶ B1) (z2 : A2 ⟶ B2) (z0 : A0 ⟶ B0) [IsIso z0]
    (f : A1 ⟶ A2) (g : B1 ⟶ B2) (h : A2 ⟶ F.obj A0) (i : B2 ⟶ F.obj B0)
    (l : X ⟶ Z) (k : Z ⟶ F.obj Y)
    (hRS : rS ≫ z1 = rT) (hR0 : r0 ≫ z0 = rT0)
    (hN : f ≫ z2 = z1 ≫ g) (hS : h ≫ F.map z0 = z2 ≫ i)
    (hT : rT ≫ g ≫ i = l ≫ k ≫ F.map rT0) :
    rS ≫ f ≫ h = l ≫ k ≫ F.map r0 := by
  apply (cancel_mono (F.map z0)).1
  simp only [Category.assoc]
  rw [hS, ← Category.assoc f z2, hN]
  simp only [Category.assoc]
  rw [← Category.assoc rS z1, hRS, hT, ← F.map_comp, hR0]

set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
private theorem mateCanonicalShiftTransport
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (F : C ⥤ C ⥤ C) [F.Additive] [∀ U : C, (F.obj U).Additive]
    [∀ P Q : CochainComplex C ℤ, CochainComplex.HasMapBifunctor P Q F]
    (q : CochainComplex C ℤ ⥤ D) [q.CommShift ℤ]
    (S T : D × D ⥤ D) (flat : ObjectProperty (CochainComplex C ℤ))
    (a : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ S.obj (q.obj P, q.obj Q))
    (b : ∀ (P Q : CochainComplex C ℤ) (_hp : flat P) (_hq : flat Q),
      q.obj (CochainComplex.mapBifunctor P Q F) ≅ T.obj (q.obj P, q.obj Q))
    (z : S ≅ T)
    (hz : ∀ (P Q : flat.FullSubcategory),
      (a P.obj Q.obj P.property Q.property).hom ≫ z.hom.app
        (q.obj P.obj, q.obj Q.obj) = (b P.obj Q.obj P.property Q.property).hom)
    [(Functor.curryObj S).CommShift₂Int] [(Functor.curryObj T).CommShift₂Int]
    (hcL : ∀ U, NatTrans.CommShift ((mateCurryIso z).hom.app U) ℤ)
    (hcR : ∀ V, NatTrans.CommShift ((mateFlipCurryIso z).hom.app V) ℤ)
    (hb : MateCanonicalShiftData F q T flat b) : MateCanonicalShiftData F q S flat a := by
  refine ⟨hb.1, ?_, ?_⟩
  · intro P Q hp hq n hpn
    let := hcR (q.obj Q)
    have hs := NatTrans.shift_app_comm
      ((mateFlipCurryIso z).hom.app
        (q.obj Q)) n (q.obj P)
    change (((Functor.curryObj S).flip.obj (q.obj Q)).commShiftIso
        n).hom.app (q.obj P) ≫
        (shiftFunctor D n).map
          (z.hom.app (q.obj P, q.obj Q)) =
      z.hom.app ((q.obj P)⟦n⟧, q.obj Q) ≫
        (((Functor.curryObj T).flip.obj (q.obj Q)).commShiftIso
          n).hom.app (q.obj P) at hs
    have hn := z.hom.naturality (Prod.mkHom
      ((q.commShiftIso n).hom.app P) (𝟙 (q.obj Q)))
    apply mateShiftTransportEquation (shiftFunctor D n) _ _ _ _
      (z.hom.app (q.obj (P⟦n⟧), q.obj Q))
      (z.hom.app ((q.obj P)⟦n⟧, q.obj Q))
      (z.hom.app (q.obj P, q.obj Q)) _ _ _ _ _ _
    · exact hz ⟨P⟦n⟧, hpn⟩ ⟨Q, hq⟩
    · exact hz ⟨P, hp⟩ ⟨Q, hq⟩
    · exact hn
    · exact hs
    · exact hb.2.1 P Q hp hq n hpn
  · intro P Q hp hq n hqn
    let := hcL (q.obj P)
    have hs := NatTrans.shift_app_comm
      ((mateCurryIso z).hom.app (q.obj P)) n (q.obj Q)
    change (((Functor.curryObj S).obj (q.obj P)).commShiftIso
        n).hom.app (q.obj Q) ≫
        (shiftFunctor D n).map
          (z.hom.app (q.obj P, q.obj Q)) =
      z.hom.app (q.obj P, (q.obj Q)⟦n⟧) ≫
        (((Functor.curryObj T).obj (q.obj P)).commShiftIso
          n).hom.app (q.obj Q) at hs
    have hn := z.hom.naturality (Prod.mkHom (𝟙 (q.obj P))
      ((q.commShiftIso n).hom.app Q))
    apply mateShiftTransportEquation (shiftFunctor D n) _ _ _ _
      (z.hom.app (q.obj P, q.obj (Q⟦n⟧)))
      (z.hom.app (q.obj P, (q.obj Q)⟦n⟧))
      (z.hom.app (q.obj P, q.obj Q)) _ _ _ _ _ _
    · exact hz ⟨P, hp⟩ ⟨Q⟦n⟧, hqn⟩
    · exact hz ⟨P, hp⟩ ⟨Q, hq⟩
    · exact hn
    · exact hs
    · exact hb.2.2 P Q hp hq n hqn

section
-- The unit of this monoidal structure is definitionally the ring module.
attribute [local semireducible] monoidalCategory

-- Keep the monoidal unit behind the cochain unitor API.
end

attribute [local semireducible] monoidalCategory

set_option maxHeartbeats 50000 in
-- Specialize the published unique comparison to the edge's normalized models.
attribute [local irreducible] monoidalCategory

-- Compare the normalized fixed-factor computation maps before transporting exactness.
set_option maxHeartbeats 50000 in
-- Elaboration must compare the large two-variable localization interfaces.
attribute [local semireducible] monoidalCategory

-- The formal mate assembly needs extra elaboration for the large normalized interface.

-- Normalize the two-variable localization interfaces and transport all exact structures.
-- Elaboration must compare the large two-variable localization interfaces.
end

end SheafOfModules
