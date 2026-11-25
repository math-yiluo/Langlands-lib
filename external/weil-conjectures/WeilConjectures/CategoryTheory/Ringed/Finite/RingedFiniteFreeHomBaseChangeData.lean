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
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
/-! # Normalized tensor comparison for scalar extension

Source: Stacks Project, Tags 07A4 and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

/-- A pure scalar-extension section, transported along the specified object equality.
It is the sheafification unit applied to s tensor x; no basis is used.
Source: Stacks 03EK, 08J9
(blueprint: lem-sf-ringed-finite-free-hom-base-change). -/
def ringedFiniteFreeScalarSection
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (M : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (E.obj M).val.obj U :=
  (eqToHom (h M).symm).val.app U
    ((((PresheafOfModules.sheafificationAdjunction
      (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf φ M)).app U)
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))

open SheafOfModules WeilConjectures CategoryTheory.MonoidalCategory

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory coefficientTotalTensor

private theorem scalarComparison_natural
    [∀ A : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J A)]
    (M : ScalarHomModels.{c, v, r, w} J) (μ : ScalarHomTensorComparison M φ)
    {P P' Q Q' : CochainComplex (scalarModules J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    ((scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive).map
      ((coefficientTotalTensor.{r, c, v} J R).map (Prod.mkHom f g))) ≫
        (μ.complexIso P' Q').hom =
      (μ.complexIso P Q).hom ≫ (coefficientTotalTensor.{r, c, v} J S).map
        (Prod.mkHom
          ((scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive).map f)
          ((scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive).map g)) := by
  let s := M.scalar φ
  let := s.extension_additive
  apply HomologicalComplex.Hom.ext
  funext n
  apply (s.ordinaryAdjunction.homEquiv _ _).injective
  apply ScalarHomTensor.total_pure_hom_ext
  intro p q h V x y
  have hu {X Y : scalarModules J R} (a : X ⟶ Y) (z : X.val.obj V) :
      (s.extension.map a).val.app V (scalarHomUnitSection M φ X V z) =
        scalarHomUnitSection M φ Y V (a.val.app V z) :=
    (congrArg (fun k ↦ k.val.app V z) (s.ordinaryAdjunction.unit.naturality a)).symm
  change ((μ.complexIso P' Q').hom.f n).val.app V
      ((s.extension.map (((coefficientTotalTensor.{r, c, v} J R).map
        (Prod.mkHom f g)).f n)).val.app V (scalarHomUnitSection M φ _ V _)) =
    (((coefficientTotalTensor.{r, c, v} J S).map (Prod.mkHom
      ((scalarComplex s.extension s.extension_additive).map f)
      ((scalarComplex s.extension s.extension_additive).map g))).f n).val.app V
      (((μ.complexIso P Q).hom.f n).val.app V (scalarHomUnitSection M φ _ V _))
  rw [hu, ScalarHomTensor.tensor_generator_map, μ.generators, μ.generators,
    ScalarHomTensor.tensor_generator_map]
  change _ = coefficientTensorGenerator.{r, c, v} J S
    ((scalarComplex s.extension s.extension_additive).obj P')
    ((scalarComplex s.extension s.extension_additive).obj Q') p q n h V
    ((s.extension.map (f.f p)).val.app V (scalarHomUnitSection M φ _ V x))
    ((s.extension.map (g.f q)).val.app V (scalarHomUnitSection M φ _ V y))
  rw [hu, hu]

/-- The actual scalar tensor comparison on complexes and preservation of K-flatness.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 06YT and 08J9.
(blueprint: lem-sf-ringed-finite-free-tensor-complex).

Proof: on sheafified pure tensors send s tensor (x tensor y) to
(s tensor x) tensor (1 tensor y). The inverse multiplies the scalars.
Balanced relations make both maps well-defined, and sheafification extends them.
Naturality in both factors gives a map on total complexes: the two tensor
differentials are preserved separately, including the sign on the second one.
Extension is a left adjoint and preserves the coproducts in each total degree,
so these mutually inverse maps assemble to a natural chain isomorphism.
For an acyclic S-complex F, restriction is exact and U(F) is acyclic.
The cancellation isomorphism U(F tensor_S E(P)) = U(F) tensor_R P
identifies the signed total differentials. K-flatness of P makes the right side
acyclic. Faithful exact restriction detects acyclicity, proving E(P) K-flat.
The generator formula is the same pure-tensor formula at scalar 1.
The argument includes the zero algebra and all unbounded complexes. -/
theorem ringedFiniteFreeHomBaseChange_complex
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ) :
    ∃ (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          D.E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (D.E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (D.E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S),
      (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y)) ∧
      (∀ (P : CochainComplex (SheafOfModules.{max c v r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
          CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
  classical
  rcases D with ⟨E, hobj, hmap, hadd⟩
  let : ∀ A : Sheaf J CommRingCat.{max c v r},
      HasDerivedCategory (scalarModules J A) := fun A ↦ HasDerivedCategory.standard _
  obtain ⟨M, μ, _⟩ := scalarInternalHomAdjunction_exists.{c, v, r} (J := J)
  have he : (M.scalar φ).extension = E := by
    refine Functor.ext (fun X ↦ ((M.scalar φ).extension_obj X).trans (hobj X).symm) ?_
    intro X Y f
    rw [(M.scalar φ).extension_map, hmap]
    simp
  subst E
  have hu (N : scalarModules J R) (V : Cᵒᵖ) (x : N.val.obj V) :
      ringedFiniteFreeScalarSection.{c, v, r} J φ (M.scalar φ).extension hobj N V 1 x =
        scalarHomUnitSection M φ N V x := by
    have hh := (M.scalar φ).ordinaryUnit N V x
    have hn : (M.scalar φ).extension_obj N = hobj N := Subsingleton.elim _ _
    rw [hn] at hh
    apply_fun (eqToHom (hobj N).symm).val.app V at hh
    simp only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply] at hh
    rw [← PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)
      (changeOfRingsPresheaf φ N)] at hh
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] at hh
    erw [PresheafOfModules.toPresheaf_map_app_apply] at hh
    exact hh.symm
  let F := scalarComplex (M.scalar φ).extension (M.scalar φ).extension_additive
  let κ : coefficientTotalTensor.{r, c, v} J R ⋙ F ≅
      F.prod F ⋙ coefficientTotalTensor.{r, c, v} J S :=
    NatIso.ofComponents (fun X ↦ (μ φ).complexIso X.1 X.2)
    (fun f ↦ scalarComparison_natural.{c, v, r} J φ M (μ φ) f.1 f.2)
  refine ⟨κ, ?_, ?_⟩
  · intro P Q p q U x y
    simp only [hu]
    exact (μ φ).generators P Q p q (p + q) rfl U x y
  · exact (μ φ).preservesKFlat

end Site
end CategoryTheory
