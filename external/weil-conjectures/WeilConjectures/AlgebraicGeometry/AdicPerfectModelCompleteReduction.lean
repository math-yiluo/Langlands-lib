/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
import all WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
import all WeilConjectures.AlgebraicGeometry.TorsionLimitSheafCompleteness
import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Completeness and residue reduction of completed perfect models

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication;
Stacks Tags 093J, 093M, 099Q, 06YQ and 0E8K
(auxiliary; not a blueprint node).

We use the equivalent coefficient-sized small model of the pro-etale site. The ring
and the module universe are independent of the scheme universe. Positive exponents
are indexed by n : ℕ, meaning n+1. In particular the residue field is A/I^(0+1).
All helpers below only name the actual complexes and maps in the assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.Scheme.AdicPerfectModel

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
  {A : Type w} [CommRing A] (I : Ideal A)

/-- The actual termwise constant complex, using the recorded exact realization.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
abbrev constantComplex (R : Type w) [CommRing R] :=
  (commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)

/-- The complex B tensor_A P, before localization.
Source: Bhatt--Scholze 6.6.11 (auxiliary; not a blueprint node). -/
abbrev model (P : CochainComplex (ModuleCat.{w} A) ℤ) :=
  ((ConstantCompletion.change (ConstantCompletion.coefficientMap J A I)).mapHomologicalComplex
    (.up ℤ)).obj ((constantComplex J A).obj P)

/-- The ordinary algebraic residue complex k tensor_A P, with its k-action retained.
Source: Stacks 093M (auxiliary; not a blueprint node). -/
def algebraicResidue (P : CochainComplex (ModuleCat.{w} A) ℤ) :
    CochainComplex (ModuleCat.{w} (A ⧸ I ^ (0 + 1))) ℤ :=
  letI := (ModuleCat.extendRestrictScalarsAdj
    (Ideal.Quotient.mk (I ^ (0 + 1)))).left_adjoint_additive
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (0 + 1)))).mapHomologicalComplex
    (.up ℤ)).obj P

/-- The constant sheaf of the ordinary residue complex.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
abbrev constantResidue (P : CochainComplex (ModuleCat.{w} A) ℤ) :=
  (constantComplex J (A ⧸ I ^ (0 + 1))).obj (algebraicResidue I P)

variable {J}

/-- Restrict actual complexes and chain maps to the localized site.
Source: Stacks 03DJ (auxiliary; not a blueprint node). -/
def overComplex (R : Sheaf J CommRingCat.{w}) (U : C) :
    ConstantCompletion.Cx R ⥤ ConstantCompletion.Cx (R.over U) :=
  letI := ringedOverFunctor_additive R U
  (SheafOfModules.overFunctor (siteModuleRings R) U).mapHomologicalComplex
    (.up ℤ)

/-- Cohomology in the standard derived localization used throughout the coefficient API.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
abbrev cohomology (R : Sheaf J CommRingCat.{w}) (q : ℤ) :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard (ConstantCompletion.Mod R)) q

variable (J)

/-- Constant module sections, through the actual additive sheafification unit.
Source: Stacks 093J (auxiliary; not a blueprint node). -/
def constantSection (R : Type w) [CommRing R] (N : ModuleCat.{w} R) (U : Cᵒᵖ) (x : N) :
    ((commutativeSiteConstantModuleFunctor J R).obj N).val.obj U :=
  (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj N).presheaf).app U x

/-- The normalization fixing the canonical residue comparison on local tensor generators.
The image of (c tensor (b tensor p)) is c times bar(b) times the constant section 1 tensor p.
Source: Stacks 093M (auxiliary; not a blueprint node). -/
def IsResidueComparison (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (f : ((ConstantCompletion.change (ConstantCompletion.projection J A I 0)).mapHomologicalComplex
      (.up ℤ)).obj (model J I P) ⟶ constantResidue J I P) : Prop :=
  ∀ (q : ℤ) (U : Cᵒᵖ) (b : (ConstantCompletion.completed J A I).obj.obj U)
    (c : (ConstantCompletion.finite J A I 0).obj.obj U) (p : P.X q),
    (f.f q).val.app U
      (ConstantCompletion.tensorSection (ConstantCompletion.projection J A I 0) _ U c
        (ConstantCompletion.tensorSection (ConstantCompletion.coefficientMap J A I) _ U b
          (constantSection J A (P.X q) U p))) =
      (c * (ConstantCompletion.projection J A I 0).hom.app U b) •
        constantSection J (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).X q) U
          ((1 : A ⧸ I ^ (0 + 1)) ⊗ₜ[A, Ideal.Quotient.mk (I ^ (0 + 1))] p)

/-- The same canonical tensor formula on a slice, with the restricted coefficient sheaf.
Source: Stacks 03DJ, 093M and 0E8K
(auxiliary; not a blueprint node). -/
def IsSliceResidueComparison (P : CochainComplex (ModuleCat.{w} A) ℤ) (U : C)
    (f : ((ConstantCompletion.change
      ((J.overPullback CommRingCat U).map
        (ConstantCompletion.projection J A I 0))).mapHomologicalComplex
         (.up ℤ)).obj
          ((overComplex (ConstantCompletion.completed J A I) U).obj (model J I P)) ⟶
        (overComplex (ConstantCompletion.finite J A I 0) U).obj (constantResidue J I P)) :
    Prop :=
  ∀ (q : ℤ) (W : (Over U)ᵒᵖ)
    (b : (ConstantCompletion.completed J A I).obj.obj (op W.unop.left))
    (c : (ConstantCompletion.finite J A I 0).obj.obj (op W.unop.left)) (p : P.X q),
    (f.f q).val.app W
      (ConstantCompletion.tensorSection
        ((J.overPullback CommRingCat U).map (ConstantCompletion.projection J A I 0)) _ W c
        (ConstantCompletion.tensorSection (ConstantCompletion.coefficientMap J A I) _
          (op W.unop.left) b (constantSection J A (P.X q) (op W.unop.left) p))) =
      (c * (ConstantCompletion.projection J A I 0).hom.app (op W.unop.left) b) •
        constantSection J (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).X q) (op W.unop.left)
          ((1 : A ⧸ I ^ (0 + 1)) ⊗ₜ[A, Ideal.Quotient.mk (I ^ (0 + 1))] p)

variable {J}

/-- The complete assertion on a site or a slice, retaining the canonical chain comparison.
This uses the existing local internal-Hom completeness predicate and universal derived counit.
Source: Bhatt--Scholze 6.6.11; Stacks 093J, 093M, 099Q and 06YY
(auxiliary; not a blueprint node). -/
def HasCompleteResidueCalculation
    {B k : Sheaf J CommRingCat.{w}} (π : B ⟶ k)
    (M : ConstantCompletion.Cx B) (V : ConstantCompletion.Cx k)
    (H : ℤ → ConstantCompletion.Mod k) (a b : ℤ)
    (c : ((ConstantCompletion.change π).mapHomologicalComplex (.up ℤ)).obj M ≅ V) : Prop :=
  ConstantCompletion.IsComplete π ((ConstantCompletion.Q B).obj M) ∧
    IsIso ((ConstantCompletion.extendComparison π).app M ≫
      (ConstantCompletion.Q k).map c.hom) ∧
    (∀ q : ℤ, Nonempty
      ((cohomology k q).obj ((ConstantCompletion.extend π).obj ((ConstantCompletion.Q B).obj M)) ≅
        H q)) ∧
    ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((cohomology B q).obj ((ConstantCompletion.Q B).obj M)) ∧
      IsZero ((cohomology k q).obj
        ((ConstantCompletion.extend π).obj ((ConstantCompletion.Q B).obj M)))

private def scalarAdjunction {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S) :
    ConstantCompletion.change φ ⊣ ConstantCompletion.res φ :=
  SheafOfModules.RingedTensor.tensorAdjunction φ

private def scalarRestrictionComp {R S B : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ B) :
    ConstantCompletion.res ψ ⋙ ConstantCompletion.res φ ≅
      ConstantCompletion.res (φ ≫ ψ) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine { hom := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             inv := { val := { app := fun U ↦ ?_, naturality := ?_ } }
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · exact ModuleCat.ofHom
        (X := ((ConstantCompletion.res φ).obj
          ((ConstantCompletion.res ψ).obj M)).val.obj U)
        (Y := ((ConstantCompletion.res (φ ≫ ψ)).obj M).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · exact ModuleCat.ofHom
        (X := ((ConstantCompletion.res (φ ≫ ψ)).obj M).val.obj U)
        (Y := ((ConstantCompletion.res φ).obj
          ((ConstantCompletion.res ψ).obj M)).val.obj U)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
    · intros; ext; rfl
    · ext; rfl
    · ext; rfl
  · intros; ext; rfl

private def scalarChangeComp {R S B : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ B) :
    ConstantCompletion.change φ ⋙ ConstantCompletion.change ψ ≅
      ConstantCompletion.change (φ ≫ ψ) :=
  Adjunction.leftAdjointUniq
    (((scalarAdjunction φ).comp (scalarAdjunction ψ)).ofNatIsoRight
      (scalarRestrictionComp φ ψ))
    (scalarAdjunction (φ ≫ ψ))

private theorem tensorSection_smul {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (M : ConstantCompletion.Mod R) (U : Cᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    ConstantCompletion.tensorSection φ M U s m =
      s • ConstantCompletion.tensorSection φ M U 1 m := by
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M)
  have h := (η.app U).hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  change η.app U ((s * 1) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) = _ at h
  rw [mul_one] at h
  exact h

private theorem scalarChangeComp_one {R S B : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (M : ConstantCompletion.Mod R)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    ((scalarChangeComp φ ψ).hom.app M).val.app U
      (ConstantCompletion.tensorSection ψ _ U 1
        (ConstantCompletion.tensorSection φ M U 1 m)) =
      ConstantCompletion.tensorSection (φ ≫ ψ) M U 1 m := by
  have he := congrArg
    (fun f : M ⟶ (ConstantCompletion.res (φ ≫ ψ)).obj
      ((ConstantCompletion.change (φ ≫ ψ)).obj M) ↦ f.val.app U m)
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((scalarAdjunction φ).comp (scalarAdjunction ψ)).ofNatIsoRight
        (scalarRestrictionComp φ ψ)) (scalarAdjunction (φ ≫ ψ)) M)
  change _ = ConstantCompletion.tensorSection (φ ≫ ψ) M U 1 m at he
  exact he

private theorem scalarChangeComp_tmul {R S B : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (M : ConstantCompletion.Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (b : B.obj.obj U) (m : M.val.obj U) :
    ((scalarChangeComp φ ψ).hom.app M).val.app U
      (ConstantCompletion.tensorSection ψ _ U b
        (ConstantCompletion.tensorSection φ M U s m)) =
      ConstantCompletion.tensorSection (φ ≫ ψ) M U (b * ψ.hom.app U s) m := by
  have hs := (((scalarAdjunction ψ).unit.app
    ((ConstantCompletion.change φ).obj M)).val.app U).hom.map_smul s
      (ConstantCompletion.tensorSection φ M U 1 m)
  change ConstantCompletion.tensorSection ψ _ U 1
      (s • ConstantCompletion.tensorSection φ M U 1 m) =
    ψ.hom.app U s • ConstantCompletion.tensorSection ψ _ U 1
      (ConstantCompletion.tensorSection φ M U 1 m) at hs
  rw [tensorSection_smul φ, tensorSection_smul ψ, hs, map_smul, map_smul,
    scalarChangeComp_one]
  rw [tensorSection_smul (φ ≫ ψ) M U (b * ψ.hom.app U s)]
  simp only [mul_smul]

private def scalarChangeCompTo {R S B : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (q : R ⟶ B) (h : φ ≫ ψ = q) :
    ConstantCompletion.change φ ⋙ ConstantCompletion.change ψ ≅ ConstantCompletion.change q := by
  subst q
  exact scalarChangeComp φ ψ

private theorem scalarChangeCompTo_tmul {R S B : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (q : R ⟶ B) (h : φ ≫ ψ = q)
    (M : ConstantCompletion.Mod R) (U : Cᵒᵖ) (s : S.obj.obj U)
    (b : B.obj.obj U) (m : M.val.obj U) :
    ((scalarChangeCompTo φ ψ q h).hom.app M).val.app U
      (ConstantCompletion.tensorSection ψ _ U b
        (ConstantCompletion.tensorSection φ M U s m)) =
      ConstantCompletion.tensorSection q M U (b * ψ.hom.app U s) m := by
  subst q
  exact scalarChangeComp_tmul φ ψ M U s b m

private def constantChangeAdjunction {R S : Type w} [CommRing R] [CommRing S]
    (q : R →+* S) :
    ConstantCompletion.change
      ((constantSheaf J CommRingCat.{w}).map (CommRingCat.ofHom q)) ⊣
      ConstantScalarRealization.restriction J q :=
  scalarAdjunction _

private def constantChangeIso {R S : Type w} [CommRing R] [CommRing S]
    (q : R →+* S) :
    ConstantCompletion.change
      ((constantSheaf J CommRingCat.{w}).map (CommRingCat.ofHom q)) ≅
      ConstantScalarRealization.extension J q :=
  Adjunction.leftAdjointUniq (constantChangeAdjunction q)
    (ConstantScalarRealization.adjunction J q)

private def constantResidueIso (P : CochainComplex (ModuleCat.{w} A) ℤ) :
    ((ConstantCompletion.change (ConstantCompletion.quotient J A I 0)).mapHomologicalComplex
      (.up ℤ)).obj ((constantComplex J A).obj P) ≅ constantResidue J I P := by
  let q := Ideal.Quotient.mk (I ^ (0 + 1))
  let f := ConstantScalarRealization.complexComparison J q P
  have : ∀ n, IsIso (f.f n) := fun n ↦
    (ConstantScalarRealization.moduleComparison_tensor J q (P.X n)).1
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact (NatIso.mapHomologicalComplex (constantChangeIso (J := J) q) (.up ℤ)).app
    ((constantComplex J A).obj P) ≪≫ asIso f

private theorem constantResidueIso_tmul (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (n : ℤ) (U : Cᵒᵖ) (s : (ConstantCompletion.finite J A I 0).obj.obj U)
    (p : P.X n) :
    ((constantResidueIso I P).hom.f n).val.app U
      (ConstantCompletion.tensorSection (ConstantCompletion.quotient J A I 0) _ U s
        (constantSection J A (P.X n) U p)) =
    s • constantSection J (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).X n) U
      ((1 : A ⧸ I ^ (0 + 1)) ⊗ₜ[A, Ideal.Quotient.mk (I ^ (0 + 1))] p) := by
  let q := Ideal.Quotient.mk (I ^ (0 + 1))
  let M := (commutativeSiteConstantModuleFunctor J A).obj (P.X n)
  have he := congrArg
    (fun f : M ⟶ (ConstantScalarRealization.restriction J q).obj
      ((ConstantScalarRealization.extension J q).obj M) ↦ f.val.app U
        (constantSection J A (P.X n) U p))
    (Adjunction.homEquiv_leftAdjointUniq_hom_app
      (constantChangeAdjunction (J := J) q) (ConstantScalarRealization.adjunction J q) M)
  change ((constantChangeIso (J := J) q).hom.app M).val.app U
      (ConstantCompletion.tensorSection (ConstantCompletion.quotient J A I 0) M U 1
        (constantSection J A (P.X n) U p)) =
    ((ConstantScalarRealization.adjunction J q).unit.app M).val.app U
      (constantSection J A (P.X n) U p) at he
  change (ConstantScalarRealization.moduleComparison J q (P.X n)).val.app U
    (((constantChangeIso (J := J) q).hom.app M).val.app U
      (ConstantCompletion.tensorSection (ConstantCompletion.quotient J A I 0) M U s
        (constantSection J A (P.X n) U p))) = _
  rw [tensorSection_smul, map_smul, he, map_smul]
  congr 1
  have hf := (ConstantScalarRealization.moduleComparison_tensor J q (P.X n)).2 U p 1
  simpa only [map_one, one_smul, ConstantScalarRealization.constantSection_eq,
    constantSection, algebraicResidue, Functor.mapHomologicalComplex, M, id_eq] using hf

private theorem coefficientMap_projection :
    ConstantCompletion.coefficientMap J A I ≫ ConstantCompletion.projection J A I 0 =
      ConstantCompletion.quotient J A I 0 := by
  exact limit.lift_π (ConstantCompletion.quotientCone J A I) (op 0)

private def residueIso (P : CochainComplex (ModuleCat.{w} A) ℤ) :
    ((ConstantCompletion.change (ConstantCompletion.projection J A I 0)).mapHomologicalComplex
      (.up ℤ)).obj (model J I P) ≅ constantResidue J I P := by
  let φ := ConstantCompletion.coefficientMap J A I
  let ψ := ConstantCompletion.projection J A I 0
  let e := scalarChangeCompTo φ ψ (ConstantCompletion.quotient J A I 0)
    (coefficientMap_projection (J := J) I)
  exact (Functor.mapHomologicalComplexCompIso e (.up ℤ)).app
      ((constantComplex J A).obj P) ≪≫
    constantResidueIso I P

private theorem residueIso_formula (P : CochainComplex (ModuleCat.{w} A) ℤ) :
    IsResidueComparison J I P (residueIso I P).hom := by
  intro n U b c p
  change ((constantResidueIso I P).hom.f n).val.app U
    (((scalarChangeCompTo (ConstantCompletion.coefficientMap J A I)
        (ConstantCompletion.projection J A I 0) (ConstantCompletion.quotient J A I 0)
        (coefficientMap_projection (J := J) I)).hom.app
          ((commutativeSiteConstantModuleFunctor J A).obj (P.X n))).val.app U
      (ConstantCompletion.tensorSection (ConstantCompletion.projection J A I 0) _ U c
        (ConstantCompletion.tensorSection (ConstantCompletion.coefficientMap J A I) _ U b
          (constantSection J A (P.X n) U p)))) = _
  rw [scalarChangeCompTo_tmul]
  exact constantResidueIso_tmul I P n U _ p

private def extensionUniverseIso {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (M : ConstantCompletion.Mod R) :
    (ConstantCompletion.change φ).obj M ≅
      SheafOfModules.changeOfRingsOfUniverses.{w, w, w, w} φ M := by
  apply (PresheafOfModules.sheafification (𝟙 _)).mapIso
  exact PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x =>
      change SheafOfModules.changeOfRingsMap.{w, w, w} φ M i
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) =
        SheafOfModules.changeOfRingsMapOfUniverses φ M i
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)
      exact (Classical.choose_spec
        (SheafOfModules.exists_changeOfRingsMap.{w, w, w} φ M i) s x).trans
        (SheafOfModules.changeOfRingsMap_tmulOfUniverses φ M i s x).symm)

private def constantPresentationIso :
    constantModuleHomFunctor J A ≅ commutativeSiteConstantModuleFunctor J A := by
  have hcoeff : realizationRingIso J A = (constantModuleHomRingIso J A).symm := by
    have hc : (Functor.compConstIso Cᵒᵖ (forget₂ CommRingCat.{w}
        RingCat.{w})).inv.app (CommRingCat.of A) = 𝟙 _ := by
      ext
      rfl
    ext U x
    simp [realizationRingIso, constantCommuteCompose, constantModuleHomRingIso, hc]
  let e := constantModuleHomRingIso J A
  let t := Classical.choice (commutativeSiteConstantModuleFunctor_transport J A)
  rw [hcoeff] at t
  change commutativeSiteConstantModuleFunctor J A ⋙
    SheafOfModules.pushforward (F := 𝟭 C) e.hom ≅ siteConstantModuleFunctorGeneral J A at t
  have he : e.inv ≫ ((𝟭 C).sheafPushforwardContinuous RingCat.{w} J J).map e.hom = 𝟙 _ :=
    e.inv_hom_id
  let R₁ := (constantSheaf J RingCat.{w}).obj (RingCat.of A)
  let R₂ := siteModuleRings (ConstantCompletion.constant J A)
  let c := SheafOfModules.pushforwardComp (S := R₂) (R := R₁) (R' := R₂)
    (J := J) (K := J) (K' := J) (F := 𝟭 C) (G := 𝟭 C) e.inv e.hom
  let d := SheafOfModules.pushforwardCongr (S := R₂) (R := R₂) (J := J) (K := J) (F := 𝟭 C) he
  let k : SheafOfModules.pushforward (F := 𝟭 C) e.hom ⋙
      SheafOfModules.pushforward (F := 𝟭 C) e.inv ≅ 𝟭 _ :=
    c ≪≫ d ≪≫ SheafOfModules.pushforwardId _
  exact Functor.isoWhiskerRight t.symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ k ≪≫ Functor.rightUnitor _

private theorem model_retract (N : ModuleCat.{w} A)
    [Module.Finite A N] [Module.Projective A N] :
    ∃ r : ℕ, ∃ i : (ConstantCompletion.change
        (ConstantCompletion.coefficientMap J A I)).obj
          ((commutativeSiteConstantModuleFunctor J A).obj N) ⟶
        ∏ᶜ (fun _ : Fin r ↦
          SheafOfModules.unit (siteModuleRings (ConstantCompletion.completed J A I))),
      ∃ p, i ≫ p = 𝟙 _ := by
  let φ := ConstantCompletion.coefficientMap J A I
  let G := commutativeSiteConstantModuleFunctor J A ⋙ ConstantCompletion.change φ
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A N
  let t := constantPresentationIso (J := J) (A := A)
  obtain ⟨_, β, _⟩ :=
    (ConstantFiniteFreePresentationExtension.constantFiniteFreePresentationExtension
      J A (ConstantCompletion.completed J A I) φ).2
  let e : G.obj (ModuleCat.of A (Fin r → A)) ≅
      ∏ᶜ (fun _ : Fin r ↦
        SheafOfModules.unit (siteModuleRings (ConstantCompletion.completed J A I))) :=
    (ConstantCompletion.change φ).mapIso (t.symm.app _) ≪≫
      extensionUniverseIso φ _ ≪≫ β r
  refine ⟨r, G.map (ModuleCat.ofHom g) ≫ e.hom, e.inv ≫ G.map (ModuleCat.ofHom f), ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp]
  have h : ModuleCat.ofHom g ≫ ModuleCat.ofHom f = 𝟙 N := ModuleCat.hom_ext hfg
  rw [h, G.map_id]
  rfl

private theorem isoLocus_retract {B : Type*} [Category* B] (P : B ⥤ B) (δ : P ⟶ P)
    {M N : B} (i : M ⟶ N) (p : N ⟶ M) (hip : i ≫ p = 𝟙 M)
    (hN : IsIso (δ.app N)) : IsIso (δ.app M) := by
  have := hN
  refine ⟨P.map i ≫ inv (δ.app N) ≫ P.map p, ?_, ?_⟩
  · rw [← Category.assoc, ← δ.naturality, Category.assoc, IsIso.hom_inv_id_assoc,
      ← P.map_comp, hip, P.map_id]
  · rw [Category.assoc, Category.assoc, δ.naturality, ← Category.assoc (inv _) _,
      IsIso.inv_hom_id, Category.id_comp, ← P.map_comp, hip, P.map_id]

private theorem model_flat (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (hP : ∀ q : ℤ, Module.Projective A (P.X q)) (q : ℤ) :
    SheafOfModules.IsFlat ((model J I P).X q) := by
  let R := ConstantCompletion.completed J A I
  let φ := ConstantCompletion.coefficientMap J A I
  have := hP q
  have h := SheafOfModules.flatScalarRealization_flat J φ (P.X q)
    (inferInstanceAs (Module.Flat A (P.X q)))
  let e := extensionUniverseIso φ ((commutativeSiteConstantModuleFunctor J A).obj (P.X q))
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  have hc := (SheafOfModules.flat_to_cat R _ h).2
  exact (exactFunctor _ _).prop_of_iso
    (MonoidalCategory.tensoringRight _ |>.mapIso e).symm hc

private def constantHomologyIso (P : CochainComplex (ModuleCat.{w} A) ℤ) (q : ℤ) :
    (cohomology (ConstantCompletion.finite J A I 0) q).obj
      ((ConstantCompletion.Q _).obj (constantResidue J I P)) ≅
      (commutativeSiteConstantModuleFunctor J (A ⧸ I ^ (0 + 1))).obj
        ((algebraicResidue I P).homology q) :=
  ((@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard _) q).app
    (constantResidue J I P)) ≪≫
      ((algebraicResidue I P).sc q).mapHomologyIso
        (commutativeSiteConstantModuleFunctor J (A ⧸ I ^ (0 + 1)))

private def changeOverPresheafIso {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (U : C) (M : ConstantCompletion.Mod R) :
    SheafOfModules.changeOfRingsPresheaf.{w, w, w}
        ((J.overPullback CommRingCat U).map φ) (M.over U) ≅
      (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj
        (SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M) := by
  exact PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x =>
      exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{w, w, w}
        ((J.overPullback CommRingCat U).map φ) (M.over U) i) s x).trans
          (Classical.choose_spec
            (SheafOfModules.exists_changeOfRingsMap.{w, w, w} φ M i.unop.left.op) s x).symm)

private def changeOverIso {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (U : C) (M : ConstantCompletion.Mod R) :
    (ConstantCompletion.change ((J.overPullback CommRingCat U).map φ)).obj (M.over U) ≅
      ((ConstantCompletion.change φ).obj M).over U := by
  have := SheafOfModules.overSheafificationMap_isIso (siteModuleRings S) U
    (SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M)
  exact (PresheafOfModules.sheafification (𝟙 _)).mapIso
      (changeOverPresheafIso φ U M) ≪≫
    asIso (SheafOfModules.overSheafificationMap (siteModuleRings S) U
      (SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M))

private theorem changeOverIso_tensor {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (U : C) (M : ConstantCompletion.Mod R) (V : (Over U)ᵒᵖ)
    (s : S.obj.obj (op V.unop.left)) (m : M.val.obj (op V.unop.left)) :
    (changeOverIso φ U M).hom.val.app V
      (ConstantCompletion.tensorSection ((J.overPullback CommRingCat U).map φ)
        (M.over U) V s m) =
      ConstantCompletion.tensorSection φ M (op V.unop.left) s m := by
  have ha := congrArg (fun f ↦ f.app V
      (s ⊗ₜ[R.obj.obj (op V.unop.left), (φ.hom.app _).hom] m))
    (toSheafify_naturality (J.over U)
      ((PresheafOfModules.toPresheaf _).map (changeOverPresheafIso φ U M).hom))
  have hb := congrArg (fun f ↦ f.app V
      (s ⊗ₜ[R.obj.obj (op V.unop.left), (φ.hom.app _).hom] m))
    (SheafOfModules.overSheafificationMap_unit (siteModuleRings S) U
      (SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M))
  exact (congrArg (fun x ↦
    (SheafOfModules.overSheafificationMap (siteModuleRings S) U
      (SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M)).val.app V x) ha.symm).trans hb

private theorem changeOverIso_naturality {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (U : C) {M N : ConstantCompletion.Mod R} (f : M ⟶ N) :
    (ConstantCompletion.change ((J.overPullback CommRingCat U).map φ)).map (f.over U) ≫
        (changeOverIso φ U N).hom =
      (changeOverIso φ U M).hom ≫ ((ConstantCompletion.change φ).map f).over U := by
  let L := PresheafOfModules.sheafification (𝟙 (siteModuleRings (S.over U)).obj)
  let t : SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} φ N :=
    { app V := (ModuleCat.extendScalars (φ.hom.app V).hom).map (f.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{w, w, w} φ M f }
  let tU : SheafOfModules.changeOfRingsPresheaf.{w, w, w}
      ((J.overPullback CommRingCat U).map φ) (M.over U) ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w}
        ((J.overPullback CommRingCat U).map φ) (N.over U) :=
    { app V := (ModuleCat.extendScalars (φ.hom.app (op V.unop.left)).hom).map
        ((f.over U).val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{w, w, w}
        ((J.overPullback CommRingCat U).map φ) (M.over U) (f.over U) }
  have ht : tU ≫ (changeOverPresheafIso φ U N).hom =
      (changeOverPresheafIso φ U M).hom ≫
        (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map t := by
    ext V x
    rfl
  change L.map tU ≫ (L.map (changeOverPresheafIso φ U N).hom ≫ _) =
    (L.map (changeOverPresheafIso φ U M).hom ≫ _) ≫ _
  rw [← Category.assoc, ← L.map_comp, ht, L.map_comp, Category.assoc]
  have hn := SheafOfModules.overSheafificationMap_naturality (siteModuleRings S) U t
  have hn' := congrArg (fun k ↦ L.map (changeOverPresheafIso φ U M).hom ≫ k) hn
  convert! hn' using 1

private def changeOverComplexIso {R S : Sheaf J CommRingCat.{w}} (φ : R ⟶ S)
    (U : C) (K : ConstantCompletion.Cx R) :
    ((ConstantCompletion.change ((J.overPullback CommRingCat U).map φ)).mapHomologicalComplex
        (.up ℤ)).obj ((overComplex R U).obj K) ≅
      (overComplex S U).obj
        (((ConstantCompletion.change φ).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ changeOverIso φ U (K.X n))
    (by intro n m h; exact (changeOverIso_naturality φ U (K.d n m)).symm)

private def sliceResidueIso (P : CochainComplex (ModuleCat.{w} A) ℤ) (U : C) :
    ((ConstantCompletion.change
      ((J.overPullback CommRingCat U).map
        (ConstantCompletion.projection J A I 0))).mapHomologicalComplex
      (.up ℤ)).obj
        ((overComplex (ConstantCompletion.completed J A I) U).obj (model J I P)) ≅
      (overComplex (ConstantCompletion.finite J A I 0) U).obj (constantResidue J I P) :=
  changeOverComplexIso (ConstantCompletion.projection J A I 0) U (model J I P) ≪≫
    (overComplex (ConstantCompletion.finite J A I 0) U).mapIso (residueIso I P)

private theorem sliceResidueIso_formula (P : CochainComplex (ModuleCat.{w} A) ℤ) (U : C) :
    IsSliceResidueComparison J I P U (sliceResidueIso I P U).hom := by
  intro n V b c p
  change ((residueIso I P).hom.f n).val.app (op V.unop.left)
    ((changeOverIso (ConstantCompletion.projection J A I 0) U ((model J I P).X n)).hom.val.app V
      (ConstantCompletion.tensorSection
        ((J.overPullback CommRingCat U).map (ConstantCompletion.projection J A I 0)) _ V c
        (ConstantCompletion.tensorSection (ConstantCompletion.coefficientMap J A I) _
          (op V.unop.left) b (constantSection J A (P.X n) (op V.unop.left) p)))) = _
  rw [changeOverIso_tensor]
  exact residueIso_formula I P n (op V.unop.left) b c p

private theorem over_preservesLimit {R : Sheaf J RingCat.{w}} (U : C)
    {D : Type} [Category D] (F : D ⥤ SheafOfModules.{w} R) :
    PreservesLimit F (SheafOfModules.overFunctor R U) := by
  constructor
  intro c hc
  refine ⟨?_⟩
  apply isLimitOfReflects (SheafOfModules.forget (R.over U))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  exact isLimitOfPreserves (SheafOfModules.evaluation R (op V.unop.left)) hc

private def ringConeModules (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone F) :
    ℕᵒᵖ ⥤ ConstantCompletion.Mod c.pt where
  obj n := (ConstantCompletion.res (c.π.app n)).obj (SheafOfModules.unit (siteModuleRings _))
  map {n m} f :=
    { val :=
      { app := fun U ↦ ModuleCat.ofHom
          (X := ((ConstantCompletion.res (c.π.app n)).obj
            (SheafOfModules.unit (siteModuleRings _))).val.obj U)
          (Y := ((ConstantCompletion.res (c.π.app m)).obj
            (SheafOfModules.unit (siteModuleRings _))).val.obj U)
          { toFun := (F.map f).hom.app U
            map_add' := map_add _
            map_smul' := by
              intro r x
              change (F.obj n).obj.obj U at x
              change (F.map f).hom.app U ((c.π.app n).hom.app U r * x) =
                (c.π.app m).hom.app U r * (F.map f).hom.app U x
              rw [map_mul]
              congr 1
              exact congrArg (fun t : c.pt ⟶ F.obj m ↦ t.hom.app U r) (c.w f) }
        naturality := by
          intros
          ext x
          exact ConcreteCategory.congr_hom ((F.map f).hom.naturality _) x } }
  map_id n := by
    ext U x
    change (F.obj n).obj.obj U at x
    exact congrArg (fun t : F.obj n ⟶ F.obj n ↦ t.hom.app U x) (F.map_id n)
  map_comp {n m l} f g := by
    ext U x
    exact congrArg (fun t : F.obj n ⟶ F.obj l ↦ t.hom.app U x) (F.map_comp f g)

private def ringConeModuleCone (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone F) :
    Cone (ringConeModules F c) where
  pt := SheafOfModules.unit (siteModuleRings c.pt)
  π :=
    { app := fun n ↦
      { val :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := (SheafOfModules.unit (siteModuleRings c.pt)).val.obj U)
            (Y := ((ringConeModules F c).obj n).val.obj U)
            { toFun := (c.π.app n).hom.app U
              map_add' := map_add _
              map_smul' := by
                intro r x
                change c.pt.obj.obj U at r x
                change (c.π.app n).hom.app U (r * x) =
                  (c.π.app n).hom.app U r * (c.π.app n).hom.app U x
                exact map_mul _ _ _ }
          naturality := by
            intros
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact ConcreteCategory.congr_hom ((c.π.app n).hom.naturality _) x } }
      naturality := by
        intro n m f
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (congrArg (fun t : c.pt ⟶ F.obj m ↦ t.hom.app U x) (c.w f)).symm }

private def ringConeModule_isLimit (F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (c : Cone F)
    (hc : IsLimit c) : IsLimit (ringConeModuleCone F c) := by
  apply isLimitOfReflects (SheafOfModules.forget (siteModuleRings c.pt))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects
    (forget₂ (ModuleCat.{w} (c.pt.obj.obj U)) AddCommGrpCat)
  let E := sheafToPresheaf J CommRingCat.{w} ⋙
    (CategoryTheory.evaluation Cᵒᵖ CommRingCat.{w}).obj U ⋙
      forget₂ CommRingCat.{w} RingCat.{w} ⋙ forget₂ RingCat.{w} AddCommGrpCat.{w}
  let G := ringConeModules F c ⋙ SheafOfModules.evaluation (siteModuleRings c.pt) U ⋙
    forget₂ _ AddCommGrpCat
  let α : G ≅ F ⋙ E := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros; ext x; rfl)
  let d := (forget₂ (ModuleCat.{w} (c.pt.obj.obj U)) AddCommGrpCat).mapCone
    ((PresheafOfModules.evaluation (siteModuleRings c.pt).obj U).mapCone
      ((SheafOfModules.forget (siteModuleRings c.pt)).mapCone (ringConeModuleCone F c)))
  apply (IsLimit.postcomposeHomEquiv α d).toFun
  exact (isLimitOfPreserves E hc).ofIsoLimit (Cone.ext (Iso.refl _) (by
    intros; ext x; rfl))

private theorem ringCone_difference {F : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (c : Cone F)
    (hc : IsLimit c) (U : C) (f : c.pt.obj.obj (op U))
    (hf : ∀ n : ℕᵒᵖ, IsNilpotent ((c.π.app n).hom.app (op U) f)) :
    IsIso ((multiplicationDifference c.pt U f).app
      ((SheafOfModules.unit (siteModuleRings c.pt)).over U)) := by
  let R := siteModuleRings c.pt
  let L := SheafOfModules.overFunctor R U
  let G := ringConeModules F c ⋙ L
  have : PreservesLimit (ringConeModules F c) L := over_preservesLimit U _
  have hG (n : ℕᵒᵖ) : IsIso ((multiplicationDifference c.pt U f).app (G.obj n)) := by
    apply difference_iso_of_nilpotent
    obtain ⟨e, he⟩ := hf n
    refine ⟨e, ?_⟩
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((endPower (.of (localSectionMultiplication c.pt U f (G.obj n))) e).asHom.val.app V)
      x = 0
    rw [sectionMultiplication_pow]
    change (F.obj n).obj.obj (op V.unop.left) at x
    change (c.π.app n).hom.app (op V.unop.left)
      ((c.pt.obj.map V.unop.hom.op f) ^ e) * x = 0
    rw [map_pow]
    have hn := (ConcreteCategory.congr_hom
      ((c.π.app n).hom.naturality V.unop.hom.op) f).symm
    change (F.obj n).obj.map V.unop.hom.op ((c.π.app n).hom.app (op U) f) =
      (c.π.app n).hom.app (op V.unop.left) (c.pt.obj.map V.unop.hom.op f) at hn
    rw [← hn, ← map_pow, he, map_zero, zero_mul]
  let d := L.mapCone (ringConeModuleCone F c)
  have hd : IsLimit d := isLimitOfPreserves L (ringConeModule_isLimit F c hc)
  let e := hd.conePointUniqueUpToIso (limit.isLimit G)
  have hi := isIso_on_limit G (countablePower _) (multiplicationDifference c.pt U f) hG
  exact isoLocus_of_iso _ _ e hi

private theorem projection_nilpotent [IsNoetherianRing A] (U : C)
    (f : (ConstantCompletion.completed J A I).obj.obj (op U))
    (hf : (ConstantCompletion.projection J A I 0).hom.app (op U) f = 0) (n : ℕ) :
    IsNilpotent ((ConstantCompletion.projection J A I n).hom.app (op U) f) := by
  let π := (ConstantCompletion.projection J A I n).hom.app (op U)
  have hle : Ideal.span (Set.range (fun a : ↥(I ^ (0 + 1)) ↦
      (ConstantCompletion.algebraSection (ConstantCompletion.coefficientMap J A I) a).val
        (op U))) ≤ Ideal.comap π.hom (_root_.nilradical _) := by
    apply Ideal.span_le.mpr
    rintro x ⟨a, rfl⟩
    apply mem_nilradical.mpr
    refine ⟨n + 1, ?_⟩
    rw [← map_pow]
    apply RingHom.mem_ker.mp
    rw [((ConstantCompletion.flat_and_quotients J A I).2.1 n U).2]
    apply Ideal.subset_span
    have ha : a.val ∈ I := by simpa using a.property
    refine ⟨⟨a.val ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
    simp only [ConstantCompletion.algebraSection, ConstantCompletion.constantSection,
      map_pow]
  apply mem_nilradical.mp
  apply hle
  have hker := ((ConstantCompletion.flat_and_quotients J A I).2.1 0 U).2
  have hmem : f ∈ RingHom.ker
      ((ConstantCompletion.projection J A I 0).hom.app (op U)).hom := hf
  rw [hker] at hmem
  exact hmem

private theorem complete_of_finite_retracts {R k : Sheaf J CommRingCat.{w}}
    (π : R ⟶ k)
    (hprod : ∀ U : C, CountableAB4Star (ConstantCompletion.Mod (R.over U)))
    (hunit : ∀ (U : C) (f : R.obj.obj (op U)), π.hom.app (op U) f = 0 →
      IsIso ((multiplicationDifference R U f).app
        ((SheafOfModules.unit (siteModuleRings R)).over U)))
    (K : ConstantCompletion.Cx R)
    (hK : ∀ q : ℤ, ∃ r : ℕ,
      ∃ i : K.X q ⟶ ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (siteModuleRings R)),
        ∃ p, i ≫ p = 𝟙 _) :
    ConstantCompletion.IsComplete π ((ConstantCompletion.Q R).obj K) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let hD (U : C) : HasDerivedCategory
      (SheafOfModules.{w} ((localCoefficientRings R).over U)) :=
    HasDerivedCategory.standard _
  intro U f ⟨y, hy⟩
  have hf : π.hom.app (op U) f = 0 := by
    change (ConstantCompletion.kernelIdeal π).sections U at y
    have hm := y.property
    change y.val = f at hy
    rw [hy] at hm
    change f ∈ (ConstantCompletion.kernelIdeal π).sections U at hm
    dsimp only [ConstantCompletion.kernelIdeal] at hm
    rw [(ConstantCompletion.kernelIdeal_existsUnique π).exists.choose_spec U] at hm
    exact hm
  let L := SheafOfModules.overFunctor (siteModuleRings R) U
  let δ := multiplicationDifference R U f
  have hterm (q : ℤ) : IsIso (δ.app ((K.X q).over U)) := by
    obtain ⟨r, i, p, hip⟩ := hK q
    let V := fun _ : Fin r ↦ SheafOfModules.unit (siteModuleRings R)
    let D := Discrete.functor V ⋙ L
    have : PreservesLimit (Discrete.functor V) L := over_preservesLimit U _
    have hd := isLimitOfPreserves L (limit.isLimit (Discrete.functor V))
    let e := hd.conePointUniqueUpToIso (limit.isLimit D)
    have hD : ∀ d, IsIso (δ.app (D.obj d)) := fun _ ↦ hunit U f hf
    have hlim := isIso_on_limit D (countablePower _) δ hD
    have hN := isoLocus_of_iso _ δ e hlim
    apply isoLocus_retract _ δ (L.map i) (L.map p) _ hN
    rw [← L.map_comp, hip, L.map_id]
  let : CountableAB4Star (SheafOfModules.{w} ((localCoefficientRings R).over U)) := hprod U
  have hz := localHom_zero_of_termwise_difference J R U f K hterm
  let eL := (DerivedCategory.singleFunctor (ConstantCompletion.Mod (R.over U)) 0).mapIso
    (coefficientLocalizationIso R U f).some
  exact hz.of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    (eL.symm.op.prod (Iso.refl _))).symm

private theorem complete_model (T : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) :
    ConstantCompletion.IsComplete
      (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} T) A I 0)
      ((ConstantCompletion.Q _).obj
        (model (coefficientProEtaleModelTopology.{u, v} T) I P)) := by
  let J := coefficientProEtaleModelTopology.{u, v} T
  let R := ConstantCompletion.completed J A I
  refine complete_of_finite_retracts _ (fun U ↦ slice_exact_products T R U) ?_ _ ?_
  · intro U f hf
    exact ringCone_difference (limit.cone (ConstantCompletion.finiteSystem J A I))
      (limit.isLimit _) U f (fun n ↦ projection_nilpotent I U f hf n.unop)
  · intro q
    have := (hP q).1
    have := (hP q).2
    exact model_retract (J := J) I (P.X q)

private theorem double_slice_products (T : Scheme.{u})
    (R : Sheaf (coefficientProEtaleModelTopology.{u, v} T) CommRingCat.{max v (u + 1)})
    (U : coefficientProEtaleSiteModel.{u, v} T) (V : Over U) :
    CountableAB4Star (ConstantCompletion.Mod ((R.over U).over V)) := by
  let J := coefficientProEtaleModelTopology.{u, v} T
  let e := V.iteratedSliceEquiv
  obtain ⟨q⟩ := module_equivalence ((J.over U).over V) (J.over V.left) e
    (siteModuleRings ((R.over U).over V)) (siteModuleRings (R.over V.left)) (Iso.refl _)
  let : CountableAB4Star (ConstantCompletion.Mod (R.over V.left)) :=
    slice_exact_products T R V.left
  constructor
  intro D _
  have : HasExactLimitsOfShape (Discrete D) (ConstantCompletion.Mod (R.over V.left)) :=
    CountableAB4Star.ofShape D
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete D) q.symm

private theorem complete_slice_model (T : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q))
    (U : coefficientProEtaleSiteModel.{u, v} T) :
    ConstantCompletion.IsComplete
      (((coefficientProEtaleModelTopology.{u, v} T).overPullback CommRingCat U).map
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} T) A I 0))
      ((ConstantCompletion.Q _).obj
        ((overComplex (ConstantCompletion.completed
          (coefficientProEtaleModelTopology.{u, v} T) A I) U).obj
            (model (coefficientProEtaleModelTopology.{u, v} T) I P))) := by
  let J := coefficientProEtaleModelTopology.{u, v} T
  let R := ConstantCompletion.completed J A I
  let L := SheafOfModules.overFunctor (siteModuleRings R) U
  refine complete_of_finite_retracts _ (double_slice_products T R U) ?_ _ ?_
  · intro V f hf
    let F := ConstantCompletion.finiteSystem J A I
    let D := J.overPullback CommRingCat U
    let c := D.mapCone (limit.cone F)
    exact ringCone_difference c (isLimitOfPreserves D (limit.isLimit F)) V f
      (fun n ↦ projection_nilpotent I V.left f hf n.unop)
  · intro q
    have := (hP q).1
    have := (hP q).2
    obtain ⟨r, i, p, hip⟩ := model_retract (J := J) I (P.X q)
    have : PreservesLimit (Discrete.functor
        (fun _ : Fin r ↦ SheafOfModules.unit (siteModuleRings R))) L :=
      over_preservesLimit U _
    let e : L.obj (∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (siteModuleRings R))) ≅
        ∏ᶜ (fun _ : Fin r ↦ SheafOfModules.unit (siteModuleRings (R.over U))) :=
      PreservesProduct.iso L _ ≪≫ Pi.mapIso (fun _ ↦ ringedOverRingIso R U)
    refine ⟨r, L.map i ≫ e.hom, e.inv ≫ L.map p, ?_⟩
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp, hip]
    exact L.map_id _

private theorem algebraicResidue_finite_homology [IsNoetherianRing A]
    (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (hP : ∀ q : ℤ, Module.Finite A (P.X q)) (q : ℤ) :
    Module.Finite (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).homology q) := by
  let k := A ⧸ I ^ (0 + 1)
  let Q := algebraicResidue I P
  have := hP q
  have : Module.Finite k (Q.X q) := by
    change Module.Finite k (k ⊗[A] P.X q)
    infer_instance
  have : Module.Finite k (Q.cycles q) :=
    Module.Finite.of_injective (Q.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  exact Module.Finite.of_surjective (Q.homologyπ q).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

private theorem cohomology_zero_of_term_zero {R : Sheaf J CommRingCat.{w}}
    (K : ConstantCompletion.Cx R) (q : ℤ) (hq : IsZero (K.X q)) :
    IsZero ((cohomology R q).obj ((ConstantCompletion.Q R).obj K)) := by
  have hH : IsZero (K.homology q) :=
    (K.sc q).isZero_homology_of_isZero_X₂ hq
  exact hH.of_iso ((@DerivedCategory.homologyFunctorFactors _ _ _
    (HasDerivedCategory.standard _) q).app K)

private theorem calculation_of_complete {B k : Sheaf J CommRingCat.{w}} (π : B ⟶ k)
    (M : ConstantCompletion.Cx B) (V : ConstantCompletion.Cx k)
    (H : ℤ → ConstantCompletion.Mod k) (a b : ℤ)
    (c : ((ConstantCompletion.change π).mapHomologicalComplex (.up ℤ)).obj M ≅ V)
    (hc : ConstantCompletion.IsComplete π ((ConstantCompletion.Q B).obj M))
    (hk : M.IsKFlatTensor)
    (hH : ∀ q, Nonempty ((cohomology k q).obj ((ConstantCompletion.Q k).obj V) ≅ H q))
    (hM : ∀ q, q < a ∨ b < q → IsZero (M.X q))
    (hV : ∀ q, q < a ∨ b < q → IsZero (V.X q)) :
    HasCompleteResidueCalculation π M V H a b c := by
  have hi : IsIso ((ConstantCompletion.extendComparison π).app M) :=
    (ConstantCompletion.derivedExtension π).computation M hk
  let e : (ConstantCompletion.extend π).obj ((ConstantCompletion.Q B).obj M) ≅
      (ConstantCompletion.Q k).obj V :=
    asIso ((ConstantCompletion.extendComparison π).app M ≫
      (ConstantCompletion.Q k).map c.hom)
  refine ⟨hc, inferInstance, fun q ↦ ⟨(cohomology k q).mapIso e ≪≫ (hH q).some⟩, ?_⟩
  intro q hq
  exact ⟨cohomology_zero_of_term_zero M q (hM q hq),
    (cohomology_zero_of_term_zero V q (hV q hq)).of_iso
      ((cohomology k q).mapIso e)⟩

private theorem model_zero_term (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (q : ℤ) (hq : IsZero (P.X q)) : IsZero ((model J I P).X q) :=
  (ConstantCompletion.change (ConstantCompletion.coefficientMap J A I)).map_isZero
    ((commutativeSiteConstantModuleFunctor J A).map_isZero hq)

private theorem constantResidue_zero_term (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (q : ℤ) (hq : IsZero (P.X q)) : IsZero ((constantResidue J I P).X q) :=
  (commutativeSiteConstantModuleFunctor J (A ⧸ I ^ (0 + 1))).map_isZero
    ((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (0 + 1)))).map_isZero hq)

private theorem model_kflat (P : CochainComplex (ModuleCat.{w} A) ℤ) (b : ℤ)
    (hbounded : ∀ q : ℤ, b < q → IsZero (P.X q))
    (hP : ∀ q : ℤ, Module.Projective A (P.X q)) :
    CochainComplex.IsKFlatTensor (R := ConstantCompletion.completed J A I)
      (model J I P) :=
  CochainComplex.isKFlat_of_boundedAbove_flat _
    ⟨b, fun q hq ↦ model_zero_term I P q (hbounded q hq)⟩ (model_flat I P hP)

private def sliceConstantHomologyIso (P : CochainComplex (ModuleCat.{w} A) ℤ)
    (U : C) (q : ℤ) :
    (cohomology ((ConstantCompletion.finite J A I 0).over U) q).obj
      ((ConstantCompletion.Q _).obj
        ((overComplex (ConstantCompletion.finite J A I 0) U).obj (constantResidue J I P))) ≅
      (SheafOfModules.overFunctor (siteModuleRings (ConstantCompletion.finite J A I 0)) U).obj
        ((commutativeSiteConstantModuleFunctor J (A ⧸ I ^ (0 + 1))).obj
          ((algebraicResidue I P).homology q)) := by
  let R := ConstantCompletion.finite J A I 0
  let F := SheafOfModules.overFunctor (siteModuleRings R) U
  let K := constantResidue J I P
  have : PreservesFiniteLimits F := ringedSite_overFunctor_limits J R U
  have : PreservesFiniteColimits F := ringedSite_overFunctor_colimits J R U
  exact ((@DerivedCategory.homologyFunctorFactors _ _ _ (HasDerivedCategory.standard _) q).app
      ((overComplex R U).obj K)) ≪≫
    (K.sc q).mapHomologyIso F ≪≫
      F.mapIso (((algebraicResidue I P).sc q).mapHomologyIso
        (commutativeSiteConstantModuleFunctor J (A ⧸ I ^ (0 + 1))))

end AlgebraicGeometry.Scheme.AdicPerfectModel

namespace AlgebraicGeometry.Scheme

open AdicPerfectModel

attribute [local irreducible] ConstantCompletion.completed

/-- Completed bounded finite-projective models are locally derived complete and their
canonical derived residue comparison is an isomorphism, on the site and every slice.
Source: Bhatt--Scholze 6.6.11, reverse implication; Stacks 093J, 093M, 099Q, 06YQ, 0E8K
(auxiliary; not a blueprint node).

Proof, following the seven DAG steps:
1. Split each finite-projective P^i off a finite free module. Constant sheaves preserve
   the splitting, so B tensor P^i is the image of the same idempotent on B^r. Sectionwise
   limits identify this with lim_n of the constant sheaves P^i/I^n P^i, including rank zero.
2. Noetherianity makes I finitely generated. Torsion-limit completeness applies to these
   inverse limits and their bounded complex. Restriction of scalars preserves and reflects
   local derived completeness for the extended ideal, giving completeness over B.
3. The constant-completion quotient theorem identifies B/IB with the constant residue field,
   through the first projection. It assumes no finite underlying residue set or regularity.
4. Each term is a retract of a finite free B-module, hence flat. Bounded-above flat complexes
   are K-flat, so the universal derived-change-of-rings counit computes reduction ordinarily.
5. The displayed tensor-generator formula is balanced, natural in the differential, and
   invertible on finite free modules and their retracts. It gives the canonical chain
   isomorphism; its composite with the universal counit is the asserted derived isomorphism.
6. Exactness of constant realization identifies cycles, boundaries and cohomology. The
   algebraic residue terms are finite-dimensional vector spaces, hence so is their
   cohomology. Both complexes have zero terms, hence zero cohomology, outside [a,b].
7. Localization identifies the slice with the pro-etale site of the covering object.
   Restriction is exact, commutes with tensor and preserves K-flat complexes and limits.
   Restrict the same chain comparison and apply the preceding argument on the slice.
   This works for every object, so in particular every covering slice, and for a>b.

The kernel of the first projection is IB by the Noetherian constant-completion quotient
identification. Thus HasCompleteResidueCalculation uses exactly local derived IB-completeness.
No completeness or localness assumption on A, or perfectness of its quotients, is used. -/
theorem adicPerfectModel_complete_reduction
    (T : Scheme.{u}) (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (_hI : I.IsMaximal)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (a b : ℤ)
    (_hbounded : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q))
    (_hP : ∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) :
    ∃ c : ((ConstantCompletion.change
        (ConstantCompletion.projection
          (coefficientProEtaleModelTopology.{u, v} T) A I 0)).mapHomologicalComplex
          (.up ℤ)).obj
            (model (coefficientProEtaleModelTopology.{u, v} T) I P) ≅
              constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P,
      IsResidueComparison (coefficientProEtaleModelTopology.{u, v} T) I P c.hom ∧
      (∀ q : ℤ, Module.Finite (A ⧸ I ^ (0 + 1)) ((algebraicResidue I P).homology q)) ∧
      HasCompleteResidueCalculation
        (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} T) A I 0)
        (model (coefficientProEtaleModelTopology.{u, v} T) I P)
        (constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P)
        (fun q ↦ (commutativeSiteConstantModuleFunctor
          (coefficientProEtaleModelTopology.{u, v} T) (A ⧸ I ^ (0 + 1))).obj
            ((algebraicResidue I P).homology q)) a b c ∧
      ∀ U : coefficientProEtaleSiteModel.{u, v} T,
        ∃ d : ((ConstantCompletion.change
            (((coefficientProEtaleModelTopology.{u, v} T).overPullback CommRingCat U).map
              (ConstantCompletion.projection
                (coefficientProEtaleModelTopology.{u, v} T) A I 0))).mapHomologicalComplex
                  (.up ℤ)).obj
          ((overComplex (ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} T) A I) U).obj
              (model (coefficientProEtaleModelTopology.{u, v} T) I P)) ≅
          (overComplex (ConstantCompletion.finite
            (coefficientProEtaleModelTopology.{u, v} T) A I 0) U).obj
              (constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P),
        IsSliceResidueComparison (coefficientProEtaleModelTopology.{u, v} T) I P U d.hom ∧
        HasCompleteResidueCalculation
          (((coefficientProEtaleModelTopology.{u, v} T).overPullback CommRingCat U).map
            (ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} T) A I 0))
          ((overComplex (ConstantCompletion.completed
            (coefficientProEtaleModelTopology.{u, v} T) A I) U).obj
              (model (coefficientProEtaleModelTopology.{u, v} T) I P))
          ((overComplex (ConstantCompletion.finite
            (coefficientProEtaleModelTopology.{u, v} T) A I 0) U).obj
              (constantResidue (coefficientProEtaleModelTopology.{u, v} T) I P))
          (fun q ↦ (SheafOfModules.overFunctor
            (siteModuleRings (ConstantCompletion.finite
              (coefficientProEtaleModelTopology.{u, v} T) A I 0)) U).obj
                ((commutativeSiteConstantModuleFunctor
                  (coefficientProEtaleModelTopology.{u, v} T) (A ⧸ I ^ (0 + 1))).obj
                    ((algebraicResidue I P).homology q))) a b d := by
  let J := coefficientProEtaleModelTopology.{u, v} T
  let R := ConstantCompletion.completed J A I
  let k := ConstantCompletion.finite J A I 0
  let π := ConstantCompletion.projection J A I 0
  let M := model J I P
  have hbounded : ∀ q : ℤ, b < q → IsZero (P.X q) :=
    fun q hq ↦ _hbounded q (Or.inr hq)
  have hk : CochainComplex.IsKFlatTensor (R := R) M :=
    model_kflat I P b hbounded (fun q ↦ (_hP q).2)
  refine ⟨residueIso I P, residueIso_formula I P,
    algebraicResidue_finite_homology I P (fun q ↦ (_hP q).1), ?_, ?_⟩
  · exact calculation_of_complete π M (constantResidue J I P) _ a b (residueIso I P)
      (complete_model T I P _hP) hk (fun q ↦ ⟨constantHomologyIso I P q⟩)
      (fun q hq ↦ model_zero_term I P q (_hbounded q hq))
      (fun q hq ↦ constantResidue_zero_term I P q (_hbounded q hq))
  · intro U
    have hki : CochainComplex.IsKFlatIndependentCoefficients (R := R) M :=
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat M).mpr hk
    have hku : CochainComplex.IsKFlatTensor (R := R.over U)
        ((overComplex R U).obj M) :=
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp
        ((SheafOfModules.ringedSite_restriction_exact_kflat J R U).2.2 M hki)
    refine ⟨sliceResidueIso I P U, sliceResidueIso_formula I P U, ?_⟩
    have hc := complete_slice_model T I P _hP U
    exact calculation_of_complete ((J.overPullback CommRingCat U).map π)
      ((overComplex R U).obj M) ((overComplex k U).obj (constantResidue J I P)) _ a b
      (sliceResidueIso I P U) hc hku
      (fun q ↦ ⟨sliceConstantHomologyIso I P U q⟩)
      (fun q hq ↦ (SheafOfModules.overFunctor (siteModuleRings R) U).map_isZero
        (model_zero_term I P q (_hbounded q hq)))
      (fun q hq ↦ (SheafOfModules.overFunctor (siteModuleRings k) U).map_isZero
        (constantResidue_zero_term I P q (_hbounded q hq)))

end AlgebraicGeometry.Scheme
