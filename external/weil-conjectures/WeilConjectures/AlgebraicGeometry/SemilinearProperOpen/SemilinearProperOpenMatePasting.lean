/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.AdjunctConjugateOpenFactor
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCoherence
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenScalarSupport
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport

import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.IntrinsicScalarAlphaCompatibility
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.IntrinsicEvaluationAlphaCompatibility

import Mathlib.Util.AliasIn
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import all WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import all WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all WeilConjectures.SixFunctors.Etale.Derived.Hom
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.Algebra.Category.Grp.Abelian
import all WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import all Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.CategoryTheory.Sites.CoverPreserving
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenScalarSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenEvaluationSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCoherence
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization

/-! # Intrinsic proper/open mates for semilinear coefficient systems

## Main definitions and statements

- `Modules`, `Derived`, `P`, `R`, `J`: the actual ordinary and derived system operations.
- `alpha`, `gamma`, `lambda`: the intrinsic clopen mate and its open restriction.
- `semilinearProperOpenMatePasting`: vertical, horizontal and base-change equations.
- `gamma_adjunct`, `gamma_identities`, `compositor_associativity`: normalization and coherence.
- `gamma_scalarRestriction`, `gamma_evaluation`, `gamma_finite`: coefficient comparisons.

## References

* Stacks Project, Tags 0F7B, 0F7C, 0F7D and 0F7F, open cases
* Stacks Project, Tags 0F7B and 07A7
* Stacks 09AE and the proof of 0F7B
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

-- The original instances followed every proof import in this module. Restore that
-- registration order after moving their declarations into the data modules.
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
attribute [-instance] VaryingRing.ringSheafify proEtSmall VaryingRing.sequenceSiteSmall derived
  siteMap_continuous push_additive push_isRightAdjoint pull_additive pull_limits
  pull_colimits systems_kInjective openPull_isRightAdjoint extension_additive
  extension_limits extension_colimits rho_additive rho_limits rho_colimits
attribute [instance] VaryingRing.ringSheafify
attribute [instance] proEtSmall
attribute [instance] VaryingRing.sequenceSiteSmall
attribute [instance] derived
attribute [instance] siteMap_continuous
attribute [instance] push_additive
attribute [instance] push_isRightAdjoint
attribute [instance] pull_additive
attribute [instance] pull_limits
attribute [instance] pull_colimits
attribute [instance] systems_kInjective
attribute [instance] openPull_isRightAdjoint
attribute [instance] extension_additive
attribute [instance] extension_limits
attribute [instance] extension_colimits
attribute [instance] rho_additive
attribute [instance] rho_limits
attribute [instance] rho_colimits
end AlgebraicGeometry.ProEtale.SemilinearProperOpen

section ProofEnvironment

-- Compare the canonical constructions through their APIs, without unfolding their data.
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors

section CategoricalProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private alias map_iso_transport := SemilinearProperOpenCoreAliases.map_iso_transport

private alias tower_normalized_transport :=
  SemilinearProperOpenCoreAliases.tower_normalized_transport

private alias tower_iso_ext_sections := SemilinearProperOpenCoreAliases.tower_iso_ext_sections

private alias normalized_function := SemilinearProperOpenCoreAliases.normalized_function

private alias isIso_of_heq := SemilinearProperOpenCoreAliases.isIso_of_heq

private alias normalized_square := SemilinearProperOpenCoreAliases.normalized_square

private alias chosen_unit_isIso_congr := SemilinearProperOpenCoreAliases.chosen_unit_isIso_congr

private alias exact_derived_congr := SemilinearProperOpenCoreAliases.exact_derived_congr

private alias right_derived_congr := SemilinearProperOpenCoreAliases.right_derived_congr

private def constant_diagram_square
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ E) (I : E ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) :
    F ⋙ (G ⋙ Functor.const ℕᵒᵖ) ≅
      (H ⋙ Functor.const ℕᵒᵖ) ⋙ (Functor.whiskeringRight ℕᵒᵖ E D).obj I := by
  exact SemilinearProperOpenCoreAliases.constant_diagram_square (A := A) (B := B) (D := D)
    (E := E) (F := F) (G := G) (H := H) (I := I) (e := e)

private alias constant_diagram_square_hom_app :=
  SemilinearProperOpenCoreAliases.constant_diagram_square_hom_app

private alias constant_diagram_square_inv_app :=
  SemilinearProperOpenCoreAliases.constant_diagram_square_inv_app

private alias mate_of_unit_normalization :=
  SemilinearProperOpenCoreAliases.mate_of_unit_normalization

private alias constant_diagram_mate := SemilinearProperOpenCoreAliases.constant_diagram_mate

private alias composite_conjugate_inv := SemilinearProperOpenCoreAliases.composite_conjugate_inv

private def adjunct_comparison
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Rr : A ⥤ D} {Lp : E ⥤ B} {Rp : B ⥤ E}
    {Ji : D ⥤ E} {Pi : E ⥤ D} {Jb : F ⥤ B} {Pb : B ⥤ F}
    {Lq : D ⥤ F} {Rq : F ⥤ D} {Rs : A ⥤ F}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (ap : Lp ⊣ Rp) (ai : Ji ⊣ Pi) (ab : Jb ⊣ Pb) (aq : Lq ⊣ Rq)
    [IsIso ab.unit] (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk)
    (t : Js ≅ Rs) (δ : Rs ⋙ Rq ≅ Rr) : (Jk ⋙ Rp) ⋙ Pi ≅ Rr := by
  exact SemilinearProperOpenCoreAliases.adjunct_comparison (A := A) (B := B) (D := D) (E := E)
    (F := F) (Rr := Rr) (Lp := Lp) (Rp := Rp) (Ji := Ji) (Pi := Pi) (Jb := Jb) (Pb := Pb)
    (Lq := Lq) (Rq := Rq) (Rs := Rs) (Js := Js) (Jk := Jk) (ap := ap) (ai := ai) (ab := ab)
    (aq := aq) (β := β) (d := d) (t := t) (δ := δ)

private alias adjunct_comparison_identity :=
  SemilinearProperOpenCoreAliases.adjunct_comparison_identity

private alias homEquiv_iso_inverse := SemilinearProperOpenCoreAliases.homEquiv_iso_inverse

private def projection_square
    {A B D E F : Type*}
    [Category A] [Category B] [Category D] [Category E] [Category F]
    {Lr : D ⥤ A} {Lp : E ⥤ B} {Ji : D ⥤ E}
    {Jb : F ⥤ B} {Lq : D ⥤ F} {Ls : F ⥤ A}
    {Js : A ⥤ F} {Jk : A ⥤ B}
    (β : Ji ⋙ Lp ≅ Lq ⋙ Jb) (d : Js ⋙ Jb ≅ Jk) (e : Lr ≅ Lq ⋙ Ls)
    (π : 𝟭 F ⟶ Ls ⋙ Js) : Ji ⋙ Lp ⟶ Lr ⋙ Jk := by
  exact SemilinearProperOpenCoreAliases.projection_square (A := A) (B := B) (D := D) (E := E)
    (F := F) (Lr := Lr) (Lp := Lp) (Ji := Ji) (Jb := Jb) (Lq := Lq) (Ls := Ls) (Js := Js)
    (Jk := Jk) (β := β) (d := d) (e := e) (π := π)

private alias projection_square_formula := SemilinearProperOpenCoreAliases.projection_square_formula

private alias projection_square_formula_of_eq :=
  SemilinearProperOpenCoreAliases.projection_square_formula_of_eq

attribute [local implicit_reducible] SemilinearSections.ringPresheaf

private alias ordinary_restriction_existsUnique :=
  SemilinearProperOpenCoreAliases.ordinary_restriction_existsUnique

end CategoricalProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section DerivedSquareConjugation
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]
  {L : A ⥤ B} {l : D ⥤ E} {G G' : A ⥤ D} {H H' : B ⥤ E}
  [L.Additive] [l.Additive] [G.Additive] [G'.Additive] [H.Additive] [H'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
private alias derived_square_conjugate := SemilinearProperOpenCoreAliases.derived_square_conjugate

private alias derived_iso_symm_inv := SemilinearProperOpenCoreAliases.derived_iso_symm_inv

end DerivedSquareConjugation

section DerivedConstantSquare
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
  [Abelian A] [Abelian B] [Abelian D] [Abelian E]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory D] [HasDerivedCategory E]
  [HasDerivedCategory (ℕᵒᵖ ⥤ D)] [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
  (L : A ⥤ B) (G : B ⥤ D) (F : A ⥤ E) (l : E ⥤ D)
  [L.Additive] [G.Additive] [F.Additive] [l.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits l] [PreservesFiniteColimits l]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ E D).obj l)]

private alias derived_constant_square_comp :=
  SemilinearProperOpenCoreAliases.derived_constant_square_comp

private alias derived_constant_square_inverse :=
  SemilinearProperOpenCoreAliases.derived_constant_square_inverse

end DerivedConstantSquare

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
attribute [local irreducible] alpha gamma

set_option synthInstance.maxSize 64 in
private alias coefficientMap_forget_eq := SemilinearProperOpenCoreAliases.coefficientMap_forget_eq

attribute [local irreducible] SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap

private alias push_eq := SemilinearProperOpenCoreAliases.push_eq

private alias pull_eq := SemilinearProperOpenCoreAliases.pull_eq

private alias extension_eq := SemilinearProperOpenCoreAliases.extension_eq

private alias P_eq := SemilinearProperOpenCoreAliases.P_eq

private alias J_eq := SemilinearProperOpenCoreAliases.J_eq

private alias R_eq := SemilinearProperOpenCoreAliases.R_eq

private alias conjugate_transport := SemilinearProperOpenCoreAliases.conjugate_transport

private alias conjugate_transport_inverse :=
  SemilinearProperOpenCoreAliases.conjugate_transport_inverse

private alias sComp_congr := SemilinearProperOpenCoreAliases.sComp_congr

private alias alpha_eq_projection_square :=
  SemilinearProperOpenCoreAliases.alpha_eq_projection_square

-- Preserve the private helpers used by existing import-all consumers.

private alias normalized_apply := SemilinearProperOpenScalarAliases.normalized_apply

section
variable (n : ℕ)
private alias level_push_evaluation_normalized :=
  SemilinearProperOpenEvaluationAliases.level_push_evaluation_normalized

end

private alias inverse_mate_change_isIso :=
  SemilinearProperOpenEvaluationAliases.inverse_mate_change_isIso

private alias inverse_mate_pasted_isIso :=
  SemilinearProperOpenEvaluationAliases.inverse_mate_pasted_isIso

universe v h w

open SheafOfModules.OpenTensorNormalization in
private alias exact_hom_fac := SemilinearProperOpenEvaluationAliases.exact_hom_fac

open SheafOfModules.OpenTensorNormalization in
private alias exact_inverse_mate_isIso :=
  SemilinearProperOpenEvaluationAliases.exact_inverse_mate_isIso

-- Keep both proper-face pullback hypotheses of the cube statement.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedVariables false in
/-- Vertical, horizontal and base-change coherence for every commutative proper/open
square, as equalities in derived semilinear-system categories, without assuming evaluation
faithful. -/
theorem semilinearProperOpenMatePasting :
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C₀ ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived C τ A),
      (J C τ j).map ((sComp C τ r₁ r₂).hom.app M) ≫
          (gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (sComp C τ p₁ p₂).inv.app ((J C τ k).obj M) =
        (gamma C τ i r₂ p₂ j h₂).app ((R C τ r₁).obj M) ≫
          (R C τ p₂).map ((gamma C τ k r₁ p₁ i h₁).app M)) ∧
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C₀) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived C τ A),
      (jComp C τ i j).hom.app ((R C τ r).obj M) ≫
          (gamma C τ (k ≫ l) r q (i ≫ j) h).app M ≫
          (R C τ q).map ((jComp C τ k l).inv.app M) =
        (J C τ j).map ((gamma C τ k r p i h₁).app M) ≫
          (gamma C τ l p q j h₂).app ((J C τ k).obj M)) ∧
    (∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
      (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
      (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
      (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) (M : Derived C τ V),
      (P C τ b).map ((gamma C τ k r p i h).app M) ≫
          (exchange C τ a p₁ p b wp).app ((J C τ k).obj M) ≫
          (R C τ p₁).map ((beta C τ d k₁ k a wk sk).hom.app M) =
        (beta C τ c i₁ i b wi si).hom.app ((R C τ r).obj M) ≫
          (J C τ i₁).map ((exchange C τ d r₁ r c wr).app M) ≫
          (gamma C τ k₁ r₁ p₁ i₁ h₁).app ((P C τ d).obj M)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A C₀ E B₀ D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
    exact Normalization.vertical_transfer
      (J C τ k) (VaryingRing.J C τ k)
      (J C τ i) (VaryingRing.J C τ i)
      (J C τ j) (VaryingRing.J C τ j)
      (R C τ r₁) (VaryingRing.P C τ r₁)
      (R C τ r₂) (VaryingRing.P C τ r₂)
      (R C τ (r₁ ≫ r₂)) (VaryingRing.P C τ (r₁ ≫ r₂))
      (R C τ p₁) (VaryingRing.P C τ p₁)
      (R C τ p₂) (VaryingRing.P C τ p₂)
      (R C τ (p₁ ≫ p₂)) (VaryingRing.P C τ (p₁ ≫ p₂))
      (gamma C τ k r₁ p₁ i h₁) (VaryingRing.gamma C τ k r₁ p₁ i h₁)
      (gamma C τ i r₂ p₂ j h₂) (VaryingRing.gamma C τ i r₂ p₂ j h₂)
      (gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h) (VaryingRing.gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
      (sComp C τ r₁ r₂) (VaryingRing.pComp C τ r₁ r₂)
      (sComp C τ p₁ p₂) (VaryingRing.pComp C τ p₁ p₂)
      (J_eq C τ k)
      (J_eq C τ i)
      (J_eq C τ j)
      (R_eq C τ r₁)
      (R_eq C τ r₂)
      (R_eq C τ (r₁ ≫ r₂))
      (R_eq C τ p₁)
      (R_eq C τ p₂)
      (R_eq C τ (p₁ ≫ p₂))
      (Normalization.gamma_normalization C τ k r₁ p₁ i h₁)
      (Normalization.gamma_normalization C τ i r₂ p₂ j h₂)
      (Normalization.gamma_normalization C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
      (Normalization.scomp_heq C τ r₁ r₂)
      (Normalization.scomp_heq C τ p₁ p₂)
      ((VaryingRing.properOpenPasting C τ).1 k i j r₁ r₂ p₁ p₂ h₁ h₂ h)
  · intro A C₀ E B₀ D F k l i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h
    exact Normalization.horizontal_transfer
      (J C τ k) (VaryingRing.J C τ k)
      (J C τ l) (VaryingRing.J C τ l)
      (J C τ i) (VaryingRing.J C τ i)
      (J C τ j) (VaryingRing.J C τ j)
      (J C τ (k ≫ l)) (VaryingRing.J C τ (k ≫ l))
      (J C τ (i ≫ j)) (VaryingRing.J C τ (i ≫ j))
      (R C τ r) (VaryingRing.P C τ r)
      (R C τ p) (VaryingRing.P C τ p)
      (R C τ q) (VaryingRing.P C τ q)
      (gamma C τ k r p i h₁) (VaryingRing.gamma C τ k r p i h₁)
      (gamma C τ l p q j h₂) (VaryingRing.gamma C τ l p q j h₂)
      (gamma C τ (k ≫ l) r q (i ≫ j) h) (VaryingRing.gamma C τ (k ≫ l) r q (i ≫ j) h)
      (jComp C τ i j) (VaryingRing.jComp C τ i j)
      (jComp C τ k l) (VaryingRing.jComp C τ k l)
      (J_eq C τ k)
      (J_eq C τ l)
      (J_eq C τ i)
      (J_eq C τ j)
      (J_eq C τ (k ≫ l))
      (J_eq C τ (i ≫ j))
      (R_eq C τ r)
      (R_eq C τ p)
      (R_eq C τ q)
      (Normalization.gamma_normalization C τ k r p i h₁)
      (Normalization.gamma_normalization C τ l p q j h₂)
      (Normalization.gamma_normalization C τ (k ≫ l) r q (i ≫ j) h)
      (Normalization.jcomp_heq C τ i j)
      (Normalization.jcomp_heq C τ k l)
      ((VaryingRing.properOpenPasting C τ).2 k l i j r p q h₁ h₂ h)
  · intro V W S T V₁ W₁ S₁ T₁ k i r p k₁ i₁ r₁ p₁ a b c d
      _ _ _ _ _ _ _ _ _ _ _ _ h h₁ wk wi wp wr sk si sp sr
    exact Normalization.cube_transfer
      (R C τ r) (VaryingRing.P C τ r)
      (R C τ p) (VaryingRing.P C τ p)
      (J C τ k) (VaryingRing.J C τ k)
      (J C τ i) (VaryingRing.J C τ i)
      (R C τ r₁) (VaryingRing.P C τ r₁)
      (R C τ p₁) (VaryingRing.P C τ p₁)
      (J C τ k₁) (VaryingRing.J C τ k₁)
      (J C τ i₁) (VaryingRing.J C τ i₁)
      (P C τ a) (VaryingRing.G C τ a)
      (P C τ b) (VaryingRing.G C τ b)
      (P C τ c) (VaryingRing.G C τ c)
      (P C τ d) (VaryingRing.G C τ d)
      (gamma C τ k r p i h) (VaryingRing.gamma C τ k r p i h)
      (gamma C τ k₁ r₁ p₁ i₁ h₁) (VaryingRing.gamma C τ k₁ r₁ p₁ i₁ h₁)
      (exchange C τ a p₁ p b wp) (Normalization.varyingExchange C τ a p₁ p b wp)
      (exchange C τ d r₁ r c wr) (Normalization.varyingExchange C τ d r₁ r c wr)
      (beta C τ d k₁ k a wk sk) (VaryingRing.alphaPullbackBeta C τ d k₁ k a wk sk)
      (beta C τ c i₁ i b wi si) (VaryingRing.alphaPullbackBeta C τ c i₁ i b wi si)
      (R_eq C τ r)
      (R_eq C τ p)
      (J_eq C τ k)
      (J_eq C τ i)
      (R_eq C τ r₁)
      (R_eq C τ p₁)
      (J_eq C τ k₁)
      (J_eq C τ i₁)
      (P_eq C τ a)
      (P_eq C τ b)
      (P_eq C τ c)
      (P_eq C τ d)
      (Normalization.gamma_normalization C τ k r p i h)
      (Normalization.gamma_normalization C τ k₁ r₁ p₁ i₁ h₁)
      (Normalization.exchange_heq C τ a p₁ p b wp)
      (Normalization.exchange_heq C τ d r₁ r c wr)
      (Normalization.beta_heq C τ d k₁ k a wk sk)
      (Normalization.beta_heq C τ c i₁ i b wi si)
      (Normalization.varying_cube C τ k i r p k₁ i₁ r₁ p₁ a b c d
        h h₁ wk wi wp wr sk si sp sr)

section CoefficientMateAssembly
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe k₁

end CoefficientMateAssembly

section ScalarRestriction
attribute [local irreducible] P R J rhoP adj StrictTower.G StrictTower.R StrictTower.J
  StrictTower.adj StrictTower.alpha
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

end ScalarRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Evaluation
attribute [local irreducible] J evalP evalJ adj StrictTower.J StrictTower.adj
  StrictTower.alpha
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible]
  VaryingRing.coefficientTransition StrictTower.G StrictTower.R P R
variable (n : ℕ)

end Evaluation

section FiniteEvaluation
variable (n : ℕ)

end FiniteEvaluation

private alias push_transport := SemilinearProperOpenCoherenceAliases.push_transport
private alias push_map_apply := SemilinearProperOpenCoherenceAliases.push_map_apply
private alias push_obj_map_apply := SemilinearProperOpenCoherenceAliases.push_obj_map_apply
private alias pushComp_apply := SemilinearProperOpenCoherenceAliases.pushComp_apply
private alias push_coherence := SemilinearProperOpenCoherenceAliases.push_coherence
private alias pull_coherence := SemilinearProperOpenCoherenceAliases.pull_coherence
private alias pull_derived_transport := SemilinearProperOpenCoherenceAliases.pull_derived_transport
private alias p_coherence := SemilinearProperOpenCoherenceAliases.p_coherence
private alias jComp_transport := SemilinearProperOpenCoherenceAliases.jComp_transport

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Identity normalizations of gamma in both directions. -/
theorem gamma_identities :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived C τ U),
      (gamma C τ j (𝟙 U) (𝟙 X) j h).app M ≫
          (sId C τ X).hom.app ((J C τ j).obj M) =
        (J C τ j).map ((sId C τ U).hom.app M)) ∧
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived C τ U),
      (gamma C τ (𝟙 U) p p (𝟙 X) h).app M ≫
          (R C τ p).map ((jId C τ U).hom.app M) =
        (jId C τ X).hom.app ((R C τ p).obj M)) := by
  constructor
  · intro U X j _ _ h
    exact Normalization.identity_left_transfer
      (J C τ j) (VaryingRing.J C τ j)
      (R C τ (𝟙 U)) (VaryingRing.P C τ (𝟙 U))
      (R C τ (𝟙 X)) (VaryingRing.P C τ (𝟙 X))
      (gamma C τ j (𝟙 U) (𝟙 X) j h) (VaryingRing.gamma C τ j (𝟙 U) (𝟙 X) j h)
      (sId C τ U) (VaryingRing.pId C τ U) (sId C τ X) (VaryingRing.pId C τ X)
      (J_eq C τ j) (R_eq C τ (𝟙 U)) (R_eq C τ (𝟙 X))
      (Normalization.gamma_normalization C τ j (𝟙 U) (𝟙 X) j h)
      (Normalization.sid_heq C τ U) (Normalization.sid_heq C τ X)
      ((VaryingRing.gamma_identities C τ).1 j h)
  · intro U X p _ h
    exact Normalization.identity_right_transfer
      (R C τ p) (VaryingRing.P C τ p)
      (J C τ (𝟙 U)) (VaryingRing.J C τ (𝟙 U))
      (J C τ (𝟙 X)) (VaryingRing.J C τ (𝟙 X))
      (gamma C τ (𝟙 U) p p (𝟙 X) h) (VaryingRing.gamma C τ (𝟙 U) p p (𝟙 X) h)
      (jId C τ U) (VaryingRing.jId C τ U) (jId C τ X) (VaryingRing.jId C τ X)
      (R_eq C τ p) (J_eq C τ (𝟙 U)) (J_eq C τ (𝟙 X))
      (Normalization.gamma_normalization C τ (𝟙 U) p p (𝟙 X) h)
      (Normalization.jid_heq C τ U) (Normalization.jid_heq C τ X)
      ((VaryingRing.gamma_identities C τ).2 p h)

/-- The projector selects the clopen image: identity there, zero on its complement. -/
theorem pi_components {U X D : Scheme.{u}} (s : U ⟶ X) (c : D ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Derived C τ X) :
    (P C τ s).map ((pi C τ s).app M) = (jAdj C τ s).unit.app ((P C τ s).obj M) ∧
      (P C τ c).map ((pi C τ s).app M) = 0 := by
  constructor
  · have hu := jAdj_unit_isIso C τ s
    let t : Adjunction.Triple (J C τ s) (P C τ s) (R C τ s) :=
      ⟨jAdj C τ s, adj C τ s⟩
    let ff := (jAdj C τ s).fullyFaithfulLOfIsIsoUnit
    have := ff.full
    have := ff.faithful
    have he : openToS C τ s = t.leftToRight := by
      ext N
      simp [openToS, t, Adjunction.Triple.leftToRight]
    have ho := openToS_isIso C τ s
    simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app]
    rw [Functor.map_comp]
    apply (cancel_mono ((P C τ s).map ((openToS C τ s).app ((P C τ s).obj M)))).1
    simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
      Category.comp_id]
    rw [he, t.leftToRight_app_obj, Functor.map_comp]
    change _ = (jAdj C τ s).unit.app _ ≫
      (P C τ s).map ((jAdj C τ s).counit.app M) ≫ _
    rw [← Category.assoc, (jAdj C τ s).right_triangle_components]
    exact (Category.id_comp _).symm
  · have hz (N : VaryingRing.Modules C τ U) :
        IsZero ((VaryingRing.pull C τ c).obj ((VaryingRing.extension C τ s).obj N)) := by
      obtain ⟨e⟩ := VaryingRing.ordinary_clopen_iso C τ s
      have := VaryingRing.moduleJAdj_unit_isIso C τ s
      let ff := (VaryingRing.moduleJAdj C τ s).fullyFaithfulLOfIsIsoUnit
      let fp := ff.ofIso e
      have := fp.full
      have := fp.faithful
      have := (VaryingRing.moduleAdj C τ s).isIso_unit_app_of_iso (e.app N)
      have := VaryingRing.moduleOpenToP_isIso C τ s
      have hi : IsIso ((VaryingRing.modulePi C τ s).app
          ((VaryingRing.extension C τ s).obj N)) := by
        dsimp only [VaryingRing.modulePi, NatTrans.comp_app, Functor.whiskerLeft_app]
        infer_instance
      have hii := (VaryingRing.pull C τ c).map_isIso
        ((VaryingRing.modulePi C τ s).app ((VaryingRing.extension C τ s).obj N))
      rw [(VaryingRing.modulePi_components C τ s c hc _).2] at hii
      exact ((isIsoZero_iff_source_target_isZero _ _).mp hii).1
    let F := extension C τ s ⋙ pull C τ c
    have hz' (N : Modules C τ U) : IsZero (F.obj N) := by
      change IsZero ((pull C τ c).obj ((extension C τ s).obj N))
      rw [pull_eq, extension_eq]
      exact hz N
    have hzD := F.isZero_mapDerivedCategory_obj ((P C τ s).obj M) (fun q ↦ hz' _)
    have hzT := hzD.of_iso
      ((Functor.mapDerivedCategoryCompIso (extension C τ s) (pull C τ c)).app
        ((P C τ s).obj M))
    exact hzT.eq_of_tgt _ _

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

end ProofEnvironment
