/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # Derived scalar extension and upper truncations

Source: Stacks Project, Cohomology on Sites, Tag 077J, and Modules on Sites,
Tags 03DB and 03EP. This is the colimit step of the cohomological-bounds argument.
-/

@[expose] public section

set_option autoImplicit false

universe w r u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace SheafOfModules

private theorem lower_bound_colimit
    {A I : Type*} [Category* A] [Abelian A] [Category* I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    (D : I ⥤ CochainComplex A ℤ) (c : Cocone D) (hc : IsColimit c)
    (a : ℤ) (hD : ∀ j, (D.obj j).IsGE a) : c.pt.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  let T : ShortComplex (I ⥤ A) :=
    (ShortComplex.functorEquivalence I A).inverse.obj
      (D ⋙ HomologicalComplex.shortComplexFunctor A (.up ℤ) i)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro j
    have := hD j
    exact IsZero.of_iso ((D.obj j).exactAt_of_isGE a i hi).isZero_homology
      (T.mapHomologyIso ((CategoryTheory.evaluation I A).obj j)).symm
  have hc₁ := isColimitOfPreserves
    (HomologicalComplex.eval A (.up ℤ) ((ComplexShape.up ℤ).prev i)) hc
  have hc₂ := isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) i) hc
  have hc₃ := isColimitOfPreserves
    (HomologicalComplex.eval A (.up ℤ) ((ComplexShape.up ℤ).next i)) hc
  exact colim.exact_mapShortComplex hT hc₁ hc₂ hc₃
    (c.pt.d _ i) (c.pt.d i _)
    (fun j ↦ (c.ι.app j).comm _ _) (fun j ↦ (c.ι.app j).comm _ _)

/-- A scalar-extension functor computed on K-flat complexes inherits a lower bound
from all finite upper truncations of a complex.
Source: Stacks Project, Cohomology on Sites, Tag 077J; Modules on Sites,
Tags 03DB and 03EP. Agent consequence, not a verbatim assertion of those tags.
(blueprint: lem-sbc-derived-scalar-truncation-continuity).

Proof: use the reduced functorial flat resolution to resolve every good upper
truncation of G compatibly. The integer-indexed degreewise colimit P of these
bounded-above flat resolutions maps quasi-isomorphically to G: exact filtered
colimits commute with cohomology, and in every degree the truncation cohomology
is eventually that of G. Each stage is K-flat, and filtered colimits of K-flat
complexes are K-flat because tensor commutes with them and exact colimits preserve
acyclicity. The supplied computation isomorphisms identify F(Q(P)) with E(P), and
likewise at each bounded stage. Scalar extension is left adjoint to restriction
of scalars, so termwise E commutes with this colimit. Each E(stage) has vanishing
cohomology below a by the hypothesis and the quasi-isomorphism to its truncation.
Exact filtered colimits therefore give the same vanishing for E(P). Transport
along Q(P) ≅ Q(G) gives the conclusion. The indexing integers are lifted to the
coefficient universe when necessary. Zero complexes, zero rings, and arbitrary
negative a are covered by the same argument; no upper bound on G is used. -/
theorem derivedScalar_lower_bound_of_truncations
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))]
    (E : SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R) ⥤
      SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S))
    (hobj : ∀ N, E.obj N = changeOfRings.{v, u, r} φ N)
    (hmap : ∀ {N N'} (f : N ⟶ N'), E.map f = eqToHom (hobj N) ≫
      changeOfRingsHom.{v, u, r} φ N f ≫ eqToHom (hobj N').symm)
    [E.Additive]
    (F : DerivedCategory
        (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ⥤
      DerivedCategory (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)))
    (hcompute : ∀ P : CochainComplex
        (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ,
      P.IsKFlatIndependentCoefficients →
        Nonempty (F.obj (DerivedCategory.Q.obj P) ≅
          DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)))
    (G : CochainComplex
      (SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (a : ℤ)
    (hfinite : ∀ b : ℤ, (F.obj (DerivedCategory.Q.obj (G.truncLE b))).IsGE a) :
    (F.obj (DerivedCategory.Q.obj G)).IsGE a := by
  let A := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R)
  let B := SheafOfModules.{r} (derivedChangeRingIndependentCoefficients J S)
  have (I : Type r) : HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r} (derivedChangeRingIndependentCoefficients J R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (I : Type r) : HasColimitsOfShape (Discrete I) A :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let := tensorPreadditive R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (MonoidalCategory.tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ : GradedObject ℤ A, GradedObject.HasTensor X₁ X₂ := by
    infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ A,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{r} :=
    AB5OfSize_of_univLE.{0, 0, r, r} AddCommGrpCat.{r}
  have : HasExactColimitsOfShape ℤ A :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  have : HasExactColimitsOfShape ℤ B :=
    HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf _)
  have : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  let := hasFunctorialFlatResolution_kfi R
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  let L := Λ.minusResolutionFunctor ⋙
    (ObjectProperty.flat.ι : _ ⥤ A).mapCochainComplexMinus ⋙ CochainComplex.Minus.ι A
  let D := G.filtrationLEMinus ⋙ L
  let P := Λ.resolutionFunctor.obj G
  have hp : QuasiIso (Λ.resolutionNatTrans.app G) := inferInstance
  have hk : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P :=
    Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le G
  have hP : P.IsKFlatIndependentCoefficients := by
    intro Z hZ
    let T := MonoidalCategory.tensorRight P
    have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
    have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
    have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)
  obtain ⟨eP⟩ := hcompute P hP
  have : PreservesColimitsOfSize.{0, 0} E :=
    preservesColimits_specifiedChangeOfRings φ E hobj hmap
  let T := E.mapHomologicalComplex (.up ℤ)
  have hstage (b : ℤ) : CochainComplex.IsGE (T.obj (D.obj b)) a := by
    let K := G.filtrationLEMinus.obj b
    let P₀ := D.obj b
    have : K.obj.IsStrictlyLE b := by
      change (G.truncLE b).IsStrictlyLE b
      infer_instance
    have hbound : CochainComplex.IsStrictlyLE P₀ b := by
      have : (Λ.bicomplexFunctor.obj K.obj).HasTotal (.up ℤ) :=
        HomologicalComplex₂.hasTotal_of_isStrictlyLE _ b 0
      have : CochainComplex.IsStrictlyLE
          ((Λ.bicomplexFunctor.obj K.obj).total (.up ℤ)) b := inferInstance
      change CochainComplex.IsStrictlyLE
        (((ObjectProperty.flat.ι : _ ⥤ A).mapHomologicalComplex (.up ℤ)).obj
          ((Λ.bicomplexFunctor.obj K.obj).total (.up ℤ))) b
      exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff _
        (ObjectProperty.flat.ι : _ ⥤ A) b).2 inferInstance
    have hf (i : ℤ) : IsFlatOnSite (J := J) (R := R) (P₀.X i) := by
      exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P₀.X i)).symm
        (((Λ.bicomplexFunctor.obj K.obj).total (.up ℤ)).X i).property.2
    have hk₀ := isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P₀ b hf
    obtain ⟨e₀⟩ := hcompute P₀ hk₀
    have : (F.obj (DerivedCategory.Q.obj K.obj)).IsGE a := hfinite b
    have : (F.obj (DerivedCategory.Q.obj P₀)).IsGE a :=
      DerivedCategory.TStructure.t.isGE_of_iso
        (F.mapIso (asIso (DerivedCategory.Q.map (Λ.totalπ K)))).symm a
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso e₀ a
  have hE : CochainComplex.IsGE (T.obj P) a := by
    apply lower_bound_colimit (D ⋙ T) (T.mapCocone (colimit.cocone D))
      (isColimitOfPreserves T (colimit.isColimit D)) a hstage
  have : (F.obj (DerivedCategory.Q.obj P)).IsGE a :=
    DerivedCategory.TStructure.t.isGE_of_iso eP.symm a
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (F.mapIso (asIso (DerivedCategory.Q.map (Λ.resolutionNatTrans.app G)))) a

end SheafOfModules
