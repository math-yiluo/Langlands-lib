/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarData
import all WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineScalarFlatDescent
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
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower

/-! # Evaluation compatibility of the scalar and line comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0G7E and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
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
attribute [local implicit_reducible] monoidalCategory LineUnbounded.tensor
variable {X : Scheme.{t}} [EssentiallySmall.{max a (t + 1)} X.ProEt]
  [∀ R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)},
    HasDerivedCategory.{w} (Modules.{t, a} X R)]
local notation "𝒬[" R "]" => (DerivedCategory.Q (C := Modules X R))
variable {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)}}

private theorem evaluation_on_representative
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁)
    (T U : C₀ ⥤ C₀) (V W : C₁ ⥤ C₁)
    (F G : D₀ ⥤ D₀) (H I : D₁ ⥤ D₁) (E : C₀ ⥤ C₁) (A : D₀ ⥤ D₁)
    (f : Q₀ ⋙ F ≅ T ⋙ Q₀) (g : Q₀ ⋙ G ≅ U ⋙ Q₀)
    (h : Q₁ ⋙ H ≅ V ⋙ Q₁) (i : Q₁ ⋙ I ≅ W ⋙ Q₁)
    (e : T ⋙ U ⟶ 𝟭 C₀) (z : V ⋙ W ⟶ 𝟭 C₁)
    (ε : F ⋙ G ⟶ 𝟭 D₀) (η : H ⋙ I ⟶ 𝟭 D₁)
    (o : T ⋙ E ⟶ E ⋙ V) (q : U ⋙ E ⟶ E ⋙ W)
    (d : F ⋙ A ⟶ A ⋙ H) (c : G ⋙ A ⟶ A ⋙ I)
    (v : Q₀ ⋙ A ⟶ E ⋙ Q₁) (P : C₀) [IsIso (v.app P)]
    (hε : ε.app (Q₀.obj P) = G.map (f.hom.app P) ≫
      g.hom.app (T.obj P) ≫ Q₀.map (e.app P))
    (hη : η.app (Q₁.obj (E.obj P)) = I.map (h.hom.app (E.obj P)) ≫
      i.hom.app (V.obj (E.obj P)) ≫ Q₁.map (z.app (E.obj P)))
    (hd : d.app (Q₀.obj P) ≫ H.map (v.app P) ≫ h.hom.app (E.obj P) =
      A.map (f.hom.app P) ≫ v.app (T.obj P) ≫ Q₁.map (o.app P))
    (hc : c.app (Q₀.obj (T.obj P)) ≫ I.map (v.app (T.obj P)) ≫
      i.hom.app (E.obj (T.obj P)) = A.map (g.hom.app (T.obj P)) ≫
        v.app (U.obj (T.obj P)) ≫ Q₁.map (q.app (T.obj P)))
    (ho : q.app (T.obj P) ≫ W.map (o.app P) ≫ z.app (E.obj P) =
      E.map (e.app P)) :
    c.app (F.obj (Q₀.obj P)) ≫ I.map (d.app (Q₀.obj P)) ≫
      η.app (A.obj (Q₀.obj P)) = A.map (ε.app (Q₀.obj P)) := by
  apply (cancel_mono (v.app P)).1
  simp only [Category.assoc]
  have hn := η.naturality (v.app P)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
  rw [← hn, hη]
  rw [← I.map_comp_assoc, ← I.map_comp_assoc, Category.assoc, hd]
  simp only [Functor.map_comp, Category.assoc]
  have cn := c.naturality (f.hom.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at cn
  rw [← reassoc_of% cn]
  have hin := i.hom.naturality (o.app P)
  simp only [Functor.comp_map, Functor.comp_obj] at hin
  rw [reassoc_of% hin, reassoc_of% hc]
  rw [← Q₁.map_comp_assoc, ← Q₁.map_comp, Category.assoc, ho]
  have vn := v.naturality (e.app P)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at vn
  rw [← vn, hε]
  simp only [Functor.map_comp, Category.assoc]

private theorem pure_eq_evaluation
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
    (M N : Modules.{t, a} X A) (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    LineUnbounded.pureTensor.{t, a} X A M N U x y =
      LineEvaluation.pureTensor.{t + 1, t, a} A M N U x y := rfl

private theorem cancellation_eq_evaluation
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
    (P Q : Modules.{t, a} X A) (e : P ⊗ Q ≅ 𝟙_ (Modules.{t, a} X A)) :
    LineUnbounded.cancellation.{t, a} X A P Q e =
      LineEvaluation.cancellation.{t + 1, t, a} A P Q e := rfl

attribute [local irreducible] LineUnbounded.cancellation LineUnbounded.pureTensor
  LineEvaluation.cancellation LineEvaluation.pureTensor

private local instance
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
    (M : Modules.{t, a} X A) (U : X.ProEtᵒᵖ) :
    SMul ((𝟙_ (Modules.{t, a} X A)).val.obj U) (M.val.obj U) :=
  inferInstanceAs (SMul (A.obj.obj U) (M.val.obj U))

private theorem cancellation_pure
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
    (P Q M : Modules.{t, a} X A) (e : P ⊗ Q ≅ 𝟙_ (Modules.{t, a} X A))
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : P.val.obj U) (z : Q.val.obj U) :
    ((LineUnbounded.cancellation X A P Q e).hom.app M).val.app U
      (LineUnbounded.pureTensor X A (M ⊗ P) Q U
        (LineUnbounded.pureTensor X A M P U x y) z) =
      e.hom.val.app U (LineUnbounded.pureTensor X A P Q U y z) • x := by
  rw [cancellation_eq_evaluation, pure_eq_evaluation, pure_eq_evaluation,
    pure_eq_evaluation]
  unfold LineEvaluation.cancellation
  change (ρ_ M).hom.val.app U
    ((M ◁ e.hom).val.app U ((α_ M P Q).hom.val.app U _)) = _
  rw [LineEvaluation.pure_assoc.{t + 1, t, a}]
  have hm := LineEvaluation.pure_map.{t + 1, t, a} A (𝟙 M) e.hom U x
    (LineEvaluation.pureTensor.{t + 1, t, a} A P Q U y z)
  rw [id_tensorHom] at hm
  rw [hm]
  exact LineEvaluation.pure_right_unitor.{t + 1, t, a} A M U x _

private theorem cancellation_inv_pure
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{max a (t + 1)})
    (P Q M : Modules.{t, a} X A) (e : P ⊗ Q ≅ 𝟙_ (Modules.{t, a} X A))
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) (y : P.val.obj U) (z : Q.val.obj U)
    (h : e.hom.val.app U (LineUnbounded.pureTensor X A P Q U y z) = (1 : A.obj.obj U)) :
    ((LineUnbounded.cancellation X A P Q e).inv.app M).val.app U x =
      LineUnbounded.pureTensor X A (M ⊗ P) Q U
        (LineUnbounded.pureTensor X A M P U x y) z := by
  let c := LineUnbounded.cancellation X A P Q e
  let v := LineUnbounded.pureTensor X A (M ⊗ P) Q U
    (LineUnbounded.pureTensor X A M P U x y) z
  have hi := congrArg (fun k ↦ k.val.app U v) (c.hom_inv_id_app M)
  change (c.inv.app M).val.app U ((c.hom.app M).val.app U v) = v at hi
  dsimp only [c, v] at hi
  rw [cancellation_pure, h, one_smul] at hi
  exact hi

attribute [local irreducible] LineUnbounded.derived LineUnbounded.normalization
  compute signedLinePower scalarTensorPower

-- The chart-wise computation through the successive derived quotient is slow to elaborate.
private theorem ordinary_evaluation
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S)
    [L.IsFiniteLocallyFreeOfRank 1] [K.IsFiniteLocallyFreeOfRank 1]
    (B : ∀ m : ℤ, changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α (power.{t, a} L m) ≅ power.{t, a} K m)
    (l : LineData L) (k : LineData K)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α L ≅ K)
    (hB : SignedLineComparisonNormalized.{t + 1, t, a} α L K b B)
    (o : ∀ m : ℤ, tensor.{t, a} L m ⋙ p.ordinary ≅
      p.ordinary ⋙ tensor.{t, a} K m)
    (ho : ∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s : S.obj.obj U),
      ((o m).hom.app M).val.app U
        (scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U s
          (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) =
      LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
        (scalar.{t, a, w} p M U s x)
        ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U 1 y)))
    : ∀ (m : ℤ) (M : Modules.{t, a} X R),
      (o (-m)).hom.app ((tensor L m).obj M) ≫
        (tensor K (-m)).map ((o m).hom.app M) ≫
        (LineUnbounded.cancellation X S (power K m) (power K (-m))
          (k.evaluation m)).hom.app (p.ordinary.obj M) =
      p.ordinary.map ((LineUnbounded.cancellation X R (power L m) (power L (-m))
        (l.evaluation m)).hom.app M) := by
  classical
  intro m M
  let e := LineUnbounded.cancellation X R (power L m) (power L (-m)) (l.evaluation m)
  let f := LineUnbounded.cancellation X S (power K m) (power K (-m)) (k.evaluation m)
  apply (cancel_epi (p.ordinary.map (e.inv.app M))).1
  let g : p.ordinary.obj M ⟶ p.ordinary.obj M :=
    p.ordinary.map (e.inv.app M) ≫ (o (-m)).hom.app ((tensor L m).obj M) ≫
    (tensor K (-m)).map ((o m).hom.app M) ≫ f.hom.app (p.ordinary.obj M)
  have he : p.ordinary.map (e.inv.app M) ≫ p.ordinary.map (e.hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, e.inv_hom_id_app, CategoryTheory.Functor.map_id]
  change g = _
  rw [he]
  obtain ⟨A⟩ := SuccessiveDerivedQuotient.adjData_exists p
  apply (A.ordinary.homEquiv M (p.ordinary.obj M)).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change g.val.app U ((A.ordinary.unit.app M).val.app U x) =
    (A.ordinary.unit.app M).val.app U x
  obtain ⟨I, V, hV, h⟩ :=
    (isFiniteLocallyFreeOfRank_iff_exists_over_iso_free (M := L) (r := 1)).mp
      inferInstance
  apply (p.ordinary.obj M).isSheaf.isSeparated _ _ (hV U.unop)
  intro W j hj
  obtain ⟨i, ⟨q⟩⟩ := hj
  change (p.ordinary.obj M).val.map j.op
      (g.val.app U ((A.ordinary.unit.app M).val.app U x)) =
    (p.ordinary.obj M).val.map j.op ((A.ordinary.unit.app M).val.app U x)
  rw [← PresheafOfModules.naturality_apply g.val]
  have hnat := PresheafOfModules.naturality_apply (A.ordinary.unit.app M).val j.op x
  change (A.ordinary.unit.app M).val.app (op W) (M.val.map j.op x) =
    (p.ordinary.obj M).val.map j.op ((A.ordinary.unit.app M).val.app U x) at hnat
  rw [← hnat]
  let chart := (h i).some ≪≫ freeUniqueIso (ULift (Fin 1))
  obtain ⟨E, hE⟩ := signedBasis_on_chart.{t + 1, t, a} L (V i) chart
  let E' : ∀ n : ℤ, (power L n).val.obj (op W) :=
    fun n ↦ (power L n).val.map q.op (E n)
  have he' : SignedLineBasisPowers.{t + 1, t, a} L (op W) E' :=
    signedBasis_restrict L _ _ q.op E hE
  obtain ⟨F, hF, hb⟩ := comparison_basis.{t + 1, t, a} α L K b (op W) E' he'
  have hn := normalized_on_basis.{t + 1, t, a} α L K b B hB (op W) E' F he' hF hb
  have hu (N : Modules.{t, a} X R) (y : N.val.obj (op W)) :
      (A.ordinary.unit.app N).val.app (op W) y = scalar p N (op W) 1 y := by
    exact A.ordinary_unit N (op W) y
  rw [hu]
  dsimp only [g]
  simp only [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hmap (N N' : Modules.{t, a} X R) (u : N ⟶ N') (y : N.val.obj (op W)) :
      (p.ordinary.map u).val.app (op W) (scalar p N (op W) 1 y) =
        scalar p N' (op W) 1 (u.val.app (op W) y) := by
    have hh := congrArg (fun z ↦ z.val.app (op W) y)
      (A.ordinary.unit.naturality u).symm
    change (p.ordinary.map u).val.app (op W)
        ((A.ordinary.unit.app N).val.app (op W) y) =
      (A.ordinary.unit.app N').val.app (op W) (u.val.app (op W) y) at hh
    rw [hu, hu] at hh
    exact hh
  rw [hmap]
  let x' : M.val.obj (op W) := M.val.map j.op x
  have hinv := cancellation_inv_pure R (power L m) (power L (-m)) M
    (l.evaluation m) (op W) x' (E' m) (E' (-m))
    (l.evaluation_basis m (op W) E' he')
  change (e.inv.app M).val.app (op W) x' = _ at hinv
  change (f.hom.app (p.ordinary.obj M)).val.app (op W)
    (((tensor K (-m)).map ((o m).hom.app M)).val.app (op W)
      (((o (-m)).hom.app ((tensor L m).obj M)).val.app (op W)
        (scalar p _ (op W) 1 ((e.inv.app M).val.app (op W) x')))) =
    scalar p M (op W) 1 x'
  rw [hinv]
  dsimp only [tensor, LineUnbounded.tensor] at ho ⊢
  erw [ho, hn]
  have ht := LineEvaluation.pure_map.{t + 1, t, a} S
    ((o m).hom.app M) (𝟙 (power K (-m)))
    (op W) (scalar p ((tensor L m).obj M) (op W) 1
      (LineUnbounded.pureTensor X R M (power L m) (op W)
        x' (E' m))) (F (-m))
  simp only [← pure_eq_evaluation, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] at ht
  rw [tensorHom_id] at ht
  change ((tensor K (-m)).map ((o m).hom.app M)).val.app (op W) _ = _ at ht
  dsimp only [f]
  dsimp only [tensor, LineUnbounded.tensor] at ht
  erw [ht, ho, hn, cancellation_pure, k.evaluation_basis m (op W) F hF, one_smul]

/-- Evaluation is preserved by any representative-normalized scalar comparison.
Source: blueprint Tate-twist local freeness proof (3); Stacks 07A4 and 06YU.
(blueprint: lem-pur-ordinary-line-scalar-evaluation).
Proof: choose a flat-term K-flat representative P of the derived input. Both line
tensors and scalar extension preserve this class. Substitute the representative
squares for m and -m and the two epsilon_computed equations. The remaining equality
is the ordinary chain evaluation square. On generators its two paths send
((x tensor y) tensor z) tensor s to x tensor s alpha(ev(y,z)).
To check the ordinary square, work on a covering slice trivializing L. Transport
its basis through b to the scalar-extended basis of K, and take the recorded signed
basis powers e_n and f_n. The hypothesis hB sends 1 tensor e_n to f_n; the two
evaluation_basis equations send e_m tensor e_-m and f_m tensor f_-m to 1.
For multiples a e_m and c e_-m, bilinearity gives a*c and alpha(a)*alpha(c),
respectively, so the displayed generator formulas agree. This includes n=0 and
negative n with the actual dual basis. Restriction naturality, sheaf separatedness
and the balanced tensor universal property prove equality without asserting global
pure-tensor generation of sheaf sections. Localization transports the square to Q(P);
naturality along
the resolution isomorphism extends it to every derived object. -/
theorem ordinary_scalar_line_evaluation
    (α : R ⟶ S) (p : SuccessiveDerivedQuotient.Presentation.{t + 1, t, max a (t + 1), w}
      (J := Scheme.ProEt.topology X) α)
    (L : Modules.{t, a} X R) (K : Modules.{t, a} X S)
    [L.IsFiniteLocallyFreeOfRank 1] [K.IsFiniteLocallyFreeOfRank 1]
    (B : ∀ m : ℤ, changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α (power.{t, a} L m) ≅ power.{t, a} K m)
    (l : LineData L) (k : LineData K)
    (b : changeOfRingsOfUniverses.{t, t + 1, max a (t + 1), max a (t + 1)}
      (J := Scheme.ProEt.topology X) α L ≅ K)
    (hB : SignedLineComparisonNormalized.{t + 1, t, a} α L K b B)
    (o : ∀ m : ℤ, tensor.{t, a} L m ⋙ p.ordinary ≅
      p.ordinary ⋙ tensor.{t, a} K m)
    (ho : ∀ (m : ℤ) (M : Modules.{t, a} X R) (U : X.ProEtᵒᵖ)
      (x : M.val.obj U) (y : (power.{t, a} L m).val.obj U) (s : S.obj.obj U),
      ((o m).hom.app M).val.app U
        (scalar.{t, a, w} p ((tensor.{t, a} L m).obj M) U s
          (LineUnbounded.pureTensor.{t, a} X R M (power.{t, a} L m) U x y)) =
      LineUnbounded.pureTensor.{t, a} X S (p.ordinary.obj M) (power.{t, a} K m) U
        (scalar.{t, a, w} p M U s x)
        ((B m).hom.val.app U (scalarExtensionSection α (power.{t, a} L m) U 1 y)))
    (d : ∀ m : ℤ, twist.{t, a, w} L m ⋙ p.derived ≅
      p.derived ⋙ twist.{t, a, w} K m)
    (hd : ∀ (m : ℤ) (P : CochainComplex (Modules.{t, a} X R) ℤ), FlatModel P →
      (d m).hom.app (𝒬[R].obj P) ≫
        (twist.{t, a, w} K m).map (compute.{t, a, w} p P) ≫
        (k.factors m).hom.app ((p.ordinary.mapHomologicalComplex (.up ℤ)).obj P) =
      p.derived.map ((l.factors m).hom.app P) ≫
        compute.{t, a, w} p (((tensor.{t, a} L m).mapHomologicalComplex (.up ℤ)).obj P) ≫
        𝒬[S].map ((Functor.mapHomologicalComplexCompIso (o m) (.up ℤ)).hom.app P)) :
    ∀ (m : ℤ) (Y : DerivedCategory (Modules.{t, a} X R)),
      (d (-m)).hom.app ((twist.{t, a, w} L m).obj Y) ≫
        (twist.{t, a, w} K (-m)).map ((d m).hom.app Y) ≫
        (k.epsilon m).hom.app (p.derived.obj Y) =
      p.derived.map ((l.epsilon m).hom.app Y) := by
  classical
  intro m Y
  let T := (tensor L m).mapHomologicalComplex (.up ℤ)
  let U := (tensor L (-m)).mapHomologicalComplex (.up ℤ)
  let V := (tensor K m).mapHomologicalComplex (.up ℤ)
  let W := (tensor K (-m)).mapHomologicalComplex (.up ℤ)
  let E := p.ordinary.mapHomologicalComplex (.up ℤ)
  let e := Functor.mapHomologicalComplexCompIso
    (LineUnbounded.cancellation X R (power L m) (power L (-m)) (l.evaluation m))
    (.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso (Modules X R) (.up ℤ)
  let z := Functor.mapHomologicalComplexCompIso
    (LineUnbounded.cancellation X S (power K m) (power K (-m)) (k.evaluation m))
    (.up ℤ) ≪≫ Functor.mapHomologicalComplexIdIso (Modules X S) (.up ℤ)
  let oc := Functor.mapHomologicalComplexCompIso (o m) (.up ℤ)
  let qc := Functor.mapHomologicalComplexCompIso (o (-m)) (.up ℤ)
  have he (P : CochainComplex (Modules X R) ℤ) (i : ℤ) :
      (e.hom.app P).f i =
        (LineUnbounded.cancellation X R (power L m) (power L (-m))
          (l.evaluation m)).hom.app (P.X i) := by
    change (_ ≫ 𝟙 _) ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have hz (P : CochainComplex (Modules X S) ℤ) (i : ℤ) :
      (z.hom.app P).f i =
        (LineUnbounded.cancellation X S (power K m) (power K (-m))
          (k.evaluation m)).hom.app (P.X i) := by
    change (_ ≫ 𝟙 _) ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have hoc (P : CochainComplex (Modules X R) ℤ) :
      qc.hom.app (T.obj P) ≫ W.map (oc.hom.app P) ≫ z.hom.app (E.obj P) =
        E.map (e.hom.app P) := by
    apply HomologicalComplex.Hom.ext
    funext i
    change (o (-m)).hom.app ((tensor L m).obj (P.X i)) ≫
      (tensor K (-m)).map ((o m).hom.app (P.X i)) ≫ (z.hom.app (E.obj P)).f i =
        p.ordinary.map ((e.hom.app P).f i)
    rw [he, hz]
    exact ordinary_evaluation α p L K B l k b hB o ho m (P.X i)
  let lhs : (twist L m ⋙ twist L (-m)) ⋙ p.derived ⟶ p.derived :=
    Functor.whiskerLeft (twist L m) (d (-m)).hom ≫
      Functor.whiskerRight (d m).hom (twist K (-m)) ≫
      Functor.whiskerLeft p.derived (k.epsilon m).hom
  let rhs : (twist L m ⋙ twist L (-m)) ⋙ p.derived ⟶ p.derived :=
    Functor.whiskerRight (l.epsilon m).hom p.derived
  obtain ⟨ff⟩ := flat_restriction_fullyFaithful (X := X) (R := R) (S := S)
  have hh : lhs = rhs := ff.map_injective (by
    apply NatTrans.ext
    funext P
    have hi := computation_iso α p P.obj P.property
    have hcalc := evaluation_on_representative 𝒬[R] 𝒬[S] T U V W
      (twist L m) (twist L (-m)) (twist K m) (twist K (-m)) E p.derived
      (l.factors m) (l.factors (-m)) (k.factors m) (k.factors (-m))
      e.hom z.hom (l.epsilon m).hom (k.epsilon m).hom oc.hom qc.hom
      (d m).hom (d (-m)).hom (complexComputation α p) P.obj
      (l.epsilon_computed m P.obj) (k.epsilon_computed m (E.obj P.obj))
      (by simpa only [complexComputation_app] using hd m P.obj P.property)
      (by simpa only [complexComputation_app] using
        hd (-m) (T.obj P.obj) (l.flat m P.obj P.property)) (hoc P.obj)
    exact hcalc)
  exact congrArg (fun n ↦ n.app Y) hh

end SheafOfModules.OrdinaryLineScalar
