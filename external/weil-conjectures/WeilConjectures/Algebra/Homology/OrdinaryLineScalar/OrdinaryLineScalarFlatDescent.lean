/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Descent of the ordinary scalar and line comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0G7E and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t a w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
namespace SheafOfModules.OrdinaryLineScalar
attribute [local instance] modulesCategory modulesAbelian monoidalCategory
attribute [local implicit_reducible] monoidalCategory
variable {X : Scheme.{t}} [EssentiallySmall.{max a (t + 1)} X.ProEt]
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
variable {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}

attribute [local irreducible] compute LineUnbounded.derived monoidalCategory

private def complexComputation
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α) :
    𝒬[R] ⋙ p.derived ⟶ p.ordinary.mapHomologicalComplex (.up ℤ) ⋙ 𝒬[S] :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules.{t, a} X R)).inv
      p.derived ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (Modules.{t, a} X R) (.up ℤ)) p.counit ≫
    Functor.whiskerLeft (p.ordinary.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso (Modules.{t, a} X S)).hom

private theorem complexComputation_app
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α) (P : CochainComplex (Modules.{t, a} X R) ℤ) :
    (complexComputation α p).app P = compute p P := by
  unfold complexComputation compute
  change _ = _ ≫ _ ≫ (DerivedCategory.Qh (C := Modules.{t, a} X S)).map (𝟙 _) ≫ _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem computation_iso
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (P : CochainComplex (Modules.{t, a} X R) ℤ) (hP : FlatModel P) :
    IsIso ((complexComputation α p).app P) := by
  obtain ⟨d⟩ := SuccessiveDerivedQuotient.adjData_exists p
  have := d.computed P hP.1 hP.2
  unfold complexComputation
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

private theorem flat_restriction_fullyFaithful :
    Nonempty (((Functor.whiskeringLeft
      (ObjectProperty.FullSubcategory (FlatModel (X := X) (R := R)))
      (DerivedCategory (Modules.{t, a} X R)) (DerivedCategory (Modules.{t, a} X S))).obj
      ((ObjectProperty.ι (FlatModel (X := X) (R := R))) ⋙ 𝒬[R])).FullyFaithful) := by
  let A := Modules.{t, a} X R
  let P : ObjectProperty (CochainComplex A ℤ) := FlatModel
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun Y ↦ P Y.as
  let q := HomotopyCategory.quotient A (.up ℤ)
  let f := H.lift (P.ι ⋙ q) (fun Y ↦ Y.property)
  have : f.Full := ⟨by
    intro Y Z g
    obtain ⟨g, hg⟩ := q.map_surjective g.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply ObjectProperty.hom_ext
    exact hg⟩
  have : f.EssSurj := ⟨by
    intro Y
    obtain ⟨Z, hz⟩ := HomotopyCategory.quotient_obj_surjective Y.obj
    refine ⟨⟨Z, ?_⟩, ⟨ObjectProperty.isoMk H (eqToIso hz)⟩⟩
    have hh : H (q.obj Z) := hz.symm ▸ Y.property
    exact hh⟩
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  have hres : ∀ Y : HomotopyCategory A (.up ℤ),
      ∃ (Z : H.FullSubcategory) (s : Z.obj ⟶ Y), W s := by
    intro Y
    obtain ⟨Z, s, hZ, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients Y.as
    have hflat : ∀ i, IsFlatOnSite.{t + 1, t, max a (t + 1), max a (t + 1)}
        (J := Scheme.ProEt.topology X) (R := R) (Z.X i) := fun i ↦
      (exactFunctor (Modules.{t, a} X R) (Modules.{t, a} X R)).prop_of_iso
        (siteSheafTensorRightIso.{t + 1, t, max a (t + 1)}
          (J := Scheme.ProEt.topology X) R (Z.X i)).symm (hf i)
    exact ⟨⟨q.obj Z, hZ, hflat⟩, q.map s,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs⟩
  have : (H.ι ⋙ DerivedCategory.Qh).IsLocalization (W.inverseImage H.ι) :=
    CategoryTheory.restriction_localization W DerivedCategory.Qh H hres
  let ff := (Localization.fullyFaithfulWhiskeringLeft (H.ι ⋙ DerivedCategory.Qh)
    (W.inverseImage H.ι) (DerivedCategory (Modules.{t, a} X S))).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f
        (DerivedCategory (Modules.{t, a} X S)))
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ _).mapIso
    (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)))⟩

set_option linter.flexible false in
/-- Descend a fixed ordinary comparison with exact signed-line tensors.
Source: Stacks 06YY and 07A4, via resolving-class localization 06YS and 06YU.
(blueprint: lem-pur-ordinary-line-scalar-flat-descent).
Proof: restrict both composite functors to flat-term K-flat complexes. The scalar
computation maps are invertible there by the universal derived scalar computation;
line tensors are computed termwise. Tensoring by a line preserves flat-term K-flat
complexes and scalar extension preserves them even for a nonflat ring map. Conjugate
the termwise ordinary comparison by these computation isomorphisms. Its naturality
for chain maps gives naturality for homotopies and for roofs, since the backward
quasi-isomorphism is inverted. The resolving-class localization equivalence therefore
descends it and its inverse to a natural isomorphism on derived categories. The
representative equation is precisely the conjugation defining this isomorphism.
No evaluation compatibility or signed-power scalar normalization is used here. -/
theorem ordinary_scalar_line_flat_descent
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S)
    (l : LineData L) (k : LineData K)
    (o : ∀ m : ℤ, tensor.{t, a} L m ⋙ p.ordinary ≅
      p.ordinary ⋙ tensor.{t, a} K m) :
    ∃ d : ∀ m : ℤ, twist.{t, a, w} L m ⋙ p.derived ≅
        p.derived ⋙ twist.{t, a, w} K m,
      ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ), FlatModel P →
        (d m).hom.app (𝒬[R].obj P) ≫
          (twist.{t, a, w} K m).map (compute.{t, a, w} p P) ≫
          (k.factors m).hom.app ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
        p.derived.map ((l.factors m).hom.app P) ≫
          compute.{t, a, w} p (((tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)).obj P) ≫
          𝒬[S].map
            ((Functor.mapHomologicalComplexCompIso (o m) (.up ℤ)).hom.app P) := by
  classical
  obtain ⟨ff⟩ := flat_restriction_fullyFaithful (X := X) (R := R) (S := S)
  let P : ObjectProperty (CochainComplex (Modules.{t, a} X R) ℤ) := FlatModel
  let E := p.ordinary.mapHomologicalComplex (.up ℤ)
  let v := complexComputation α p
  have hv (Y : P.FullSubcategory) : IsIso (v.app Y.obj) :=
    computation_iso α p Y.obj Y.property
  have : ∀ Y : P.FullSubcategory, IsIso ((Functor.whiskerLeft P.ι v).app Y) := hv
  have : IsIso (Functor.whiskerLeft P.ι v) := NatIso.isIso_of_isIso_app _
  let c : P.ι ⋙ 𝒬[R] ⋙ p.derived ≅ P.ι ⋙ E ⋙ 𝒬[S] :=
    asIso (Functor.whiskerLeft P.ι v)
  let T (m : ℤ) := (tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)
  have ht (m : ℤ) (Y : P.FullSubcategory) : IsIso (v.app ((T m).obj Y.obj)) :=
    computation_iso α p _ (l.flat m Y.obj Y.property)
  have (m : ℤ) : IsIso (Functor.whiskerLeft (P.ι ⋙ T m) v) := by
    have : ∀ Y : P.FullSubcategory,
        IsIso ((Functor.whiskerLeft (P.ι ⋙ T m) v).app Y) := ht m
    exact NatIso.isIso_of_isIso_app _
  let cT (m : ℤ) : P.ι ⋙ T m ⋙ 𝒬[R] ⋙ p.derived ≅ P.ι ⋙ T m ⋙ E ⋙ 𝒬[S] :=
    asIso (Functor.whiskerLeft (P.ι ⋙ T m) v)
  let z (m : ℤ) : P.ι ⋙ 𝒬[R] ⋙ twist.{t, a, w} L m ⋙ p.derived ≅
      P.ι ⋙ 𝒬[R] ⋙ p.derived ⋙ twist.{t, a, w} K m :=
    Functor.isoWhiskerLeft P.ι (Functor.isoWhiskerRight (l.factors m) p.derived) ≪≫
      cT m ≪≫
      Functor.isoWhiskerLeft P.ι
        (Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexCompIso (o m) (.up ℤ)) 𝒬[S]) ≪≫
      (Functor.isoWhiskerLeft (P.ι ⋙ E) (k.factors m)).symm ≪≫
      (Functor.isoWhiskerRight c (twist.{t, a, w} K m)).symm
  let d (m : ℤ) : twist.{t, a, w} L m ⋙ p.derived ≅
      p.derived ⋙ twist.{t, a, w} K m := ff.preimageIso (z m)
  refine ⟨d, ?_⟩
  intro m Y hY
  have hh := congrArg (fun n ↦ n.app (⟨Y, hY⟩ : P.FullSubcategory))
    (ff.map_preimage (X := twist.{t, a, w} L m ⋙ p.derived)
      (Y := p.derived ⋙ twist.{t, a, w} K m) (z m).hom)
  change (d m).hom.app (𝒬[R].obj Y) = (z m).hom.app ⟨Y, hY⟩ at hh
  rw [hh]
  dsimp only [z, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, c, cT, asIso_hom, asIso_inv]
  simp only [Category.assoc, complexComputation_app, v]
  have hi : IsIso (compute p Y) := by
    rw [← complexComputation_app α p Y]
    exact computation_iso α p Y hY
  -- Normalize the presentation maps before supplying the fixed categorical identity below.
  simp [complexComputation_app, E, T]
  have hfinal := Category.comp_id
    (p.derived.map ((l.factors m).hom.app Y) ≫
      compute p (((tensor L m).mapHomologicalComplex (.up ℤ)).obj Y) ≫
      𝒬[S].map ((Functor.mapHomologicalComplexCompIso (o m) (.up ℤ)).hom.app Y))
  simp only [Category.assoc] at hfinal
  -- The two composite-complex encodings are definitionally equal; the kernel checks this.
  run_tac Lean.Elab.Tactic.withMainContext do
    let some h := (← Lean.getLCtx).findFromUserName? `hfinal
      | Lean.throwError "missing identity calculation"
    (← Lean.Elab.Tactic.getMainGoal).assign h.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

end SheafOfModules.OrdinaryLineScalar
