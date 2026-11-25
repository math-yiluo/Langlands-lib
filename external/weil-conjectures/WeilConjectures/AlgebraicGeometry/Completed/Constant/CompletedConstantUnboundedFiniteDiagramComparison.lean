/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRealizationDataSupplement
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
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantDerivedScalarFactorization

/-! # Finite diagrams of arbitrary completed constant complexes

Source: Stacks Tags 06YY, 06YU and 093J--093M; the finite tensor comparison
in amplification (c).
(blueprint: lem-weil-pbc-completed-constant-unbounded-finite-diagram-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem restrictComp_apply
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec M U x

private theorem derivedRestrictComp_assoc
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc) :
    Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
        pbcDerivedRestrictComp ab c abc habc =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
        pbcDerivedRestrictComp a bc abc habc' := by
  apply SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
  apply Iso.ext
  ext M U x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  change ((pbcRestrictComp ab c abc habc).hom.app M).val.app U
      (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x) =
    ((pbcRestrictComp a bc abc habc').hom.app M).val.app U
      (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x)
  simp only [restrictComp_apply]

private theorem normalization_eq
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (E : DerivedCategory (pbcModules T R)) :
    pbcReductionNormalizationHom a b c h E =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
        (pbcDerivedRestrictComp a b c h)).hom.app E := by
  dsimp [pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

private theorem normalization_assoc
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc)
    (E : DerivedCategory (pbcModules T R)) :
    pbcReductionNormalizationHom b c bc hbc ((pbcDerivedExtend a).obj E) ≫
        pbcReductionNormalizationHom a bc abc habc' E =
      (pbcDerivedExtend c).map (pbcReductionNormalizationHom a b ab hab E) ≫
        pbcReductionNormalizationHom ab c abc habc E := by
  have h := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab hab) (pbcDerivedRestrictComp b c bc hbc)
    (pbcDerivedRestrictComp a bc abc habc') (pbcDerivedRestrictComp ab c abc habc)
    (derivedRestrictComp_assoc a b c ab bc abc hab hbc habc habc')
  have hE := congrArg (fun e ↦ e.hom.app E) h
  simpa only [normalization_eq, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp] using hE

private theorem normalization_transition
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc)
    (E : DerivedCategory (pbcModules T R)) :
    pbcReductionNormalizationHom a b ab hab E ≫
        pbcReductionTransition ab c abc habc E =
      pbcReductionTransition b c bc hbc ((pbcDerivedExtend a).obj E) ≫
        (pbcDerivedRestrict c).map (pbcReductionNormalizationHom a bc abc habc' E) := by
  have h := congrArg ((pbcDerivedScalarAdjunction c).homEquiv _ _)
    (normalization_assoc a b c ab bc abc hab hbc habc habc' E)
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left] at h
  simpa only [pbcReductionNormalizationHom, Equiv.apply_symm_apply] using h.symm

private theorem transition_naturality
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    {E F : DerivedCategory (pbcModules T R)} (f : E ⟶ F) :
    (pbcDerivedExtend a).map f ≫ pbcReductionTransition a b c h F =
      pbcReductionTransition a b c h E ≫
        (pbcDerivedRestrict b).map ((pbcDerivedExtend c).map f) := by
  unfold pbcReductionTransition
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  rw [← Category.assoc, ← (pbcDerivedScalarAdjunction c).unit_naturality f]
  simp only [Category.assoc]
  congr 1
  exact (pbcDerivedRestrictComp a b c h).inv.naturality ((pbcDerivedExtend c).map f)

/-- Finite scalar extension compares the completed realization with the realization
through the constant algebraic ring, naturally in every quotient map. There is no
local-system hypothesis, chosen algebraic tower, effectivity assumption or bound on E.

Source: Stacks Tags 06YY and 06YU, scalar extension on K-flat resolutions;
Tags 093J--093M, completed constant sheaf reduction; finite tensor comparison
in amplification (c).
(blueprint: lem-weil-pbc-completed-constant-unbounded-finite-diagram-comparison).

Proof: first factor the completed realization through the single derived scalar
extension from the inverse image of the constant completion ring. The coefficient
map is the inverse image of the limit lift of constantAdicFiniteCone. Its composite
with each quotient projection is constantAdicFiniteProjection, by limit.lift_π.
Apply derived scalar-extension normalization to these factorizations to obtain
the quotient-linear isomorphisms. Ordinary scalar-restriction comparisons are
identity on sections, so they satisfy associativity; exact derivation transports
that identity. Adjunction.leftAdjointCompIso_assoc gives the corresponding
associativity for derived normalization. Transposing it along the last extension
adjunction gives normalization's compatibility with pbcReductionTransition.
Finally transition naturality transports this equality along the single completed
realization comparison, proving the forward square for all n ≤ m, including n = m. -/
theorem completed_constant_unbounded_finite_diagram_comparison
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : adicLisseConstantRing Y (AdicCompletion d.ideal A) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ d.ideal (n + 1)).toRingHom))
    (β : (adicTowerInverseImage g).obj (adicLisseCompletedRing X d.ideal) ⟶
      adicLisseCompletedRing Y d.ideal)
    (hβ : ∀ n : ℕ, β ≫ limit.π (adicLisseRingSystem Y d.ideal) (op n) =
      (adicTowerInverseImage g).map (limit.π (adicLisseRingSystem X d.ideal) (op n)) ≫
        proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) :
    let c := completedConstantRealization Y d.ideal φ ⋙ pbcRestrict β ⋙
      pbcRestrict ((adicTowerInverseImage g).map (pbcCompletedComparison X d).inv)
    ∀ (hc : c.Additive) (hlim : PreservesFiniteLimits c)
      (hcolim : PreservesFiniteColimits c),
      letI := hc
      letI := hlim
      letI := hcolim
      ∀ E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A)),
      ∃ e : ∀ n : ℕ,
        (pbcDerivedExtend ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).obj
            (c.mapDerivedCategory.obj E) ≅
          (pbcDerivedExtend (constantAdicFiniteProjection g d n)).obj
            ((constantAdicFiniteRealization g d).obj E),
        ∀ (m n : ℕ) (hnm : n ≤ m),
          (e m).hom ≫ pbcReductionTransition
              (constantAdicFiniteProjection g d m)
              ((adicTowerInverseImage g).map (pbcAdicQuotient X d m n hnm))
              (constantAdicFiniteProjection g d n)
              (constantAdicFiniteProjection_comp g d m n hnm)
              ((constantAdicFiniteRealization g d).obj E) =
            pbcReductionTransition
                ((adicTowerInverseImage g).map (pbcAdicProjection X d m))
                ((adicTowerInverseImage g).map (pbcAdicQuotient X d m n hnm))
                ((adicTowerInverseImage g).map (pbcAdicProjection X d n))
                (((adicTowerInverseImage g).map_comp _ _).symm.trans
                  (congrArg (adicTowerInverseImage g).map
                    (pbcAdicProjection_comp X d m n hnm)))
                (c.mapDerivedCategory.obj E) ≫
              (pbcDerivedRestrict ((adicTowerInverseImage g).map
                (pbcAdicQuotient X d m n hnm))).map (e n).hom := by
  dsimp only
  intro hc hlim hcolim
  let := hc
  let := hlim
  let := hcolim
  intro E
  obtain ⟨f⟩ := completed_constant_derived_scalar_factorization X Y g d φ hφ β hβ
    hc hlim hcolim
  let a : (adicTowerInverseImage g).obj
      (adicLisseConstantRing X (AdicCompletion d.ideal A)) ⟶
      (adicTowerInverseImage g).obj (pbcAdicCompletion X d) :=
    (adicTowerInverseImage g).map
    (limit.lift (pbcAdicRings X d) (constantAdicFiniteCone X d))
  have ha (n : ℕ) :
      a ≫ (adicTowerInverseImage g).map (pbcAdicProjection X d n) =
        constantAdicFiniteProjection g d n := by
    dsimp only [a, constantAdicFiniteProjection, pbcAdicProjection]
    rw [← Functor.map_comp]
    exact congrArg (adicTowerInverseImage g).map
      (limit.lift_π (constantAdicFiniteCone X d) (op n))
  let e := f.app E
  refine ⟨fun n ↦
    (pbcDerivedExtend ((adicTowerInverseImage g).map (pbcAdicProjection X d n))).mapIso e ≪≫
      pbcReductionNormalization a
        ((adicTowerInverseImage g).map (pbcAdicProjection X d n))
        (constantAdicFiniteProjection g d n) (ha n)
        ((constantAdicFiniteRealization g d).obj E), ?_⟩
  intro m n hnm
  let b := (adicTowerInverseImage g).map (pbcAdicProjection X d m)
  let q := (adicTowerInverseImage g).map (pbcAdicQuotient X d m n hnm)
  let c := (adicTowerInverseImage g).map (pbcAdicProjection X d n)
  let r : (adicTowerInverseImage g).obj
      (adicLisseConstantRing X (AdicCompletion d.ideal A)) ⟶
      (adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op m)) :=
    constantAdicFiniteProjection g d m
  let s : (adicTowerInverseImage g).obj
      (adicLisseConstantRing X (AdicCompletion d.ideal A)) ⟶
      (adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)) :=
    constantAdicFiniteProjection g d n
  have hbc : b ≫ q = c :=
    ((adicTowerInverseImage g).map_comp _ _).symm.trans
      (congrArg (adicTowerInverseImage g).map (pbcAdicProjection_comp X d m n hnm))
  have hrs : r ≫ q = s := constantAdicFiniteProjection_comp g d m n hnm
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (pbcDerivedExtend b).map e.hom ≫
      pbcReductionNormalizationHom a b r (ha m) _ ≫
        pbcReductionTransition r q s hrs _ =
    pbcReductionTransition b q c hbc _ ≫
      (pbcDerivedRestrict q).map
        ((pbcDerivedExtend c).map e.hom ≫
          pbcReductionNormalizationHom a c s (ha n) _)
  rw [normalization_transition a b q r c s (ha m) hbc hrs (ha n)]
  rw [← Category.assoc]
  erw [transition_naturality b q c hbc e.hom]
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Scheme
