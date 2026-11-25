/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CompletionTriangle.CompletionTriangleComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.SchemeRefinementTree
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionComparison
import WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # Finite-stratum detection for strict integral completion

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-def-localizing-closure-ctf-equals-bc.proof.md, Strata and Locality;
Stacks Tags 09Y4, 09AA, 09AH, 09BM
(blueprint: lem-sfb-finite-strata-completion-detection).

The helpers only specialize published constructions: exact inverse image, the actual
base-changed cover, its leaf tests, and the cone of the specified strict augmentation.
The scalar-presentation clause retains each supplied scalar matrix, including zero ranks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.Mod.extendScalars

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteStrataCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact inverse image on the ordinary unbounded derived module categories.
It is the levelwise form of the recorded total left derived pullback, identified by
`CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`.
Source: blueprint Strata/Locality (blueprint: lem-sfb-finite-strata-completion-detection). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapDerivedCategory

/-- The cone of the specified strict Roos augmentation on a complex. On a K-flat
representative this is the cone of the completion unit, with its zero second coordinate.
Source: blueprint strict completion (blueprint: lem-sfb-finite-strata-completion-detection). -/
def completionCone (X : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) :
    DerivedCategory (AdicCompletion.Modules l E X) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCone (AdicCompletion.augmentation l E X P))

variable {W : Scheme.{u}} (S : Scheme.FiniteLocallyClosedStratification W)
  (𝒰 : ∀ a : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a))

/-- The given cover pulled back to an actual stratum factor of a leaf. Its cover structure
retains the fpqc finite-refinement condition, not just joint surjectivity.
Source: Stacks Tag 022D (blueprint: lem-sfb-finite-strata-completion-detection). -/
abbrev leafCover {L : Scheme.{u}} (a : Fin S.n) (t : L ⟶ S.domain a) :
    Scheme.Cover.{u} Scheme.proetalePrecoverage L :=
  (𝒰 a).pullback₂ t

/-- Test a property on every base-changed covering member of a leaf, using its actual
branch morphism. The accompanying tree assertion supplies stratum factors for nonempty
leaves; every restriction on an empty leaf lies in the zero module category.
Source: blueprint Strata/Locality (blueprint: lem-sfb-finite-strata-completion-detection). -/
def leafCoverTest (P : ∀ (T : Scheme.{u}), (T ⟶ W) → Prop)
    (L : Scheme.{u}) (branch : L ⟶ W) : Prop :=
  ∀ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch →
    ∀ i : (𝒰 a).I₀,
      P ((leafCover S 𝒰 a t).X i) ((leafCover S 𝒰 a t).f i ≫ branch)

/-- The same scalar module and every one of its finite scalar presentations survive
restriction from a stratum-cover member to the corresponding leaf-cover member.
Scalar modules are ordinary modules encoded as module objects in abelian groups;
matrix entries are maps from the integer tensor unit, equivalently scalar elements.
Source: blueprint finite scalar models (blueprint: lem-sfb-finite-strata-completion-detection).
-/
def leafScalarModels (L : Scheme.{u}) (branch : L ⟶ W) : Prop :=
  ∀ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch →
    ∀ (i : (𝒰 a).I₀) (M : AdicCompletion.Modules l E W)
      (P : Mod Ab.{u + 1} (scalarRingObj (DerivedNakayama.integerRing l E))),
      Mod.IsFinitelyPresented (scalarRingObj (DerivedNakayama.integerRing l E)) P →
      Nonempty
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) ((𝒰 a).f i)).obj
          ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
            (S.immersion a)).obj M) ≅
          (finiteConstantScalarExtension (DerivedNakayama.integerRing l E) ((𝒰 a).X i)).obj
            P) →
      Nonempty
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
          ((leafCover S 𝒰 a t).f i ≫ branch)).obj M ≅
          (finiteConstantScalarExtension (DerivedNakayama.integerRing l E)
            ((leafCover S 𝒰 a t).X i)).obj P) ∧
      ∀ (m n : ℕ)
        (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶
          scalarRingObj (DerivedNakayama.integerRing l E))),
        Nonempty (P ≅ cokernel (biproduct.matrix fun j k ↦
          Mod.regularLift (Mod.regular (scalarRingObj (DerivedNakayama.integerRing l E)))
            (A j k))) →
        Nonempty
          ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) ((𝒰 a).f i)).obj
            ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
              (S.immersion a)).obj M) ≅
            cokernel (scalarMatrix (DerivedNakayama.integerRing l E) ((𝒰 a).X i) A)) ∧
        Nonempty
          ((CondensedRing.upperStar (DerivedNakayama.integerRing l E)
            ((leafCover S 𝒰 a t).f i ≫ branch)).obj M ≅
            cokernel (scalarMatrix (DerivedNakayama.integerRing l E)
              ((leafCover S 𝒰 a t).X i) A))

attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension

private theorem scalar_cokernel_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (P : Mod Ab.{u + 1} (scalarRingObj Λ)) (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ))
    (e : P ≅ cokernel (biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k))) :
    Nonempty ((finiteConstantScalarExtension Λ X).obj P ≅
      cokernel (scalarMatrix Λ X A)) := by
  let f := biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)
  let F := finiteConstantScalarExtension Λ X
  refine ⟨F.mapIso e ≪≫ PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) (scalarMatrix Λ X A)
      (scalarFreeIso Λ X m) (scalarFreeIso Λ X n) ?_⟩
  rw [← scalarMatrix_map]
  simp only [F, f, Iso.hom_inv_id_assoc]

private noncomputable def scalar_point_cokernel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (m n : ℕ)
    (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)) :
    cokernel (scalarMatrix Λ X A) ≅
      ((upperStarFromPoint X).mapMod Λ).obj
        (cokernel (biproduct.matrix fun j k ↦
          Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k)))) := by
  let B := biproduct.matrix fun j k ↦
    Mod.regularLift (Mod.regular Λ) (pointScalarSection Λ (A j k))
  let F := (upperStarFromPoint X).mapMod Λ
  refine (cokernel.mapIso (F.map B) (scalarMatrix Λ X A)
    (pointFreeIso Λ X m) (pointFreeIso Λ X n) ?_).symm ≪≫
    (PreservesCokernel.iso F B).symm
  rw [← pointMatrix_map]
  simp only [B, F, Iso.hom_inv_id_assoc]

private theorem scalar_pull_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      ((finiteConstantScalarExtension Λ Y).obj P) ≅
        (finiteConstantScalarExtension Λ X).obj P) := by
  obtain ⟨n, m, d, ⟨ed⟩⟩ := hP
  let A (j : Fin m) (k : Fin n) : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ :=
    (MonObj.one : 𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ) ≫
      (biproduct.ι _ j ≫ d ≫ biproduct.π _ k).hom
  have hd : (biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)) = d :=
    scalarMatrix_reconstruct Λ d
  have eP : P ≅ cokernel (biproduct.matrix fun j k ↦
      Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k)) := by
    rw [hd]
    exact ed
  obtain ⟨eY⟩ := scalar_cokernel_model Λ Y P m n A eP
  obtain ⟨eX⟩ := scalar_cokernel_model Λ X P m n A eP
  exact ⟨(CondensedRing.upperStar Λ f).mapIso (eY ≪≫ scalar_point_cokernel Λ Y m n A) ≪≫
    (pullback_point_iso Λ f).app _ ≪≫
      (scalar_point_cokernel Λ X m n A).symm ≪≫ eX.symm⟩

private theorem scalar_restrict_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ T) (h : X ⟶ T)
    (hc : p ≫ f ≫ g = h)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P)
    (e : (CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ g).obj M) ≅
      (finiteConstantScalarExtension Λ Y).obj P) :
    Nonempty ((CondensedRing.upperStar Λ h).obj M ≅
      (finiteConstantScalarExtension Λ X).obj P) := by
  exact ⟨eqToIso (congrArg (fun r ↦ (CondensedRing.upperStar Λ r).obj M) hc.symm) ≪≫
    (CondensedRing.upperStarComp Λ p (f ≫ g)).app M ≪≫
    (CondensedRing.upperStar Λ p).mapIso ((CondensedRing.upperStarComp Λ f g).app M) ≪≫
    (CondensedRing.upperStar Λ p).mapIso e ≪≫ (scalar_pull_model Λ p P hP).some⟩

private theorem scalar_restrict_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ T) (h : X ⟶ T)
    (hc : p ≫ f ≫ g = h)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (P : Mod Ab.{u + 1} (scalarRingObj Λ))
    (hP : Mod.IsFinitelyPresented (scalarRingObj Λ) P)
    (e : (CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ g).obj M) ≅
      (finiteConstantScalarExtension Λ Y).obj P) :
    Nonempty ((CondensedRing.upperStar Λ h).obj M ≅
      (finiteConstantScalarExtension Λ X).obj P) ∧
    ∀ (m n : ℕ) (A : Fin m → Fin n → (𝟙_ Ab.{u + 1} ⟶ scalarRingObj Λ)),
      Nonempty (P ≅ cokernel (biproduct.matrix fun j k ↦
        Mod.regularLift (Mod.regular (scalarRingObj Λ)) (A j k))) →
      Nonempty ((CondensedRing.upperStar Λ f).obj
        ((CondensedRing.upperStar Λ g).obj M) ≅ cokernel (scalarMatrix Λ Y A)) ∧
      Nonempty ((CondensedRing.upperStar Λ h).obj M ≅ cokernel (scalarMatrix Λ X A)) := by
  obtain ⟨ep⟩ := scalar_restrict_model Λ p f g h hc M P hP e
  refine ⟨⟨ep⟩, ?_⟩
  intro m n A ⟨eP⟩
  obtain ⟨es⟩ := scalar_cokernel_model Λ Y P m n A eP
  obtain ⟨el⟩ := scalar_cokernel_model Λ X P m n A eP
  exact ⟨⟨e ≪≫ es⟩, ⟨ep ≪≫ el⟩⟩

private noncomputable def leafProjection {L : Scheme.{u}} (a : Fin S.n)
    (t : L ⟶ S.domain a) (i : (𝒰 a).I₀) :
    (leafCover S 𝒰 a t).X i ⟶ (𝒰 a).X i := pullback.fst ((𝒰 a).f i) t

private theorem leafProjection_comp {L : Scheme.{u}} (a : Fin S.n)
    (t : L ⟶ S.domain a) (i : (𝒰 a).I₀) :
    leafProjection S 𝒰 a t i ≫ (𝒰 a).f i = (leafCover S 𝒰 a t).f i ≫ t :=
  pullback.condition

private theorem scalar_leaf_model {L : Scheme.{u}} (branch : L ⟶ W) :
    leafScalarModels l E S 𝒰 L branch := by
  intro a t ht i M P hP ⟨e⟩
  have hp : leafProjection S 𝒰 a t i ≫ (𝒰 a).f i ≫ S.immersion a =
      (leafCover S 𝒰 a t).f i ≫ branch := by
    rw [← Category.assoc, leafProjection_comp, Category.assoc, ht]
  exact scalar_restrict_models (DerivedNakayama.integerRing l E)
    (leafProjection S 𝒰 a t i) ((𝒰 a).f i) (S.immersion a)
    ((leafCover S 𝒰 a t).f i ≫ branch) hp M P hP e

private theorem complete_iso {T : Scheme.{u}}
    {K L : DerivedCategory (AdicCompletion.Modules l E T)} (e : K ≅ L) :
    IsDerivedComplete l E T K ↔ IsDerivedComplete l E T L := by
  constructor
  · rintro ⟨P, hP, ⟨eP⟩, h⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩, h⟩
  · rintro ⟨P, hP, ⟨eP⟩, h⟩
    exact ⟨P, hP, ⟨eP ≪≫ e.symm⟩, h⟩

private theorem complete_cone (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).kFlat P) :
    IsDerivedComplete l E T (DerivedCategory.Q.obj P) ↔
      IsZero (completionCone l E T P) := by
  rw [AdicCompletion.isDerivedComplete_iff l E T _ P hP (Iso.refl _)]
  change IsIso (𝟙 _ ≫ DerivedCategory.Q.map (AdicCompletion.augmentation l E T P)) ↔ _
  rw [Category.id_comp]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished
      (AdicCompletion.augmentation l E T P))).symm

private theorem presentation_complete (T : Scheme.{u})
    (S : StrictCompletionRestriction.Presentation (AdicCompletion.Modules l E T))
    (hS : StrictCompletionRestriction.IsIntegral l E T S)
    (K : DerivedCategory (AdicCompletion.Modules l E T)) :
    IsDerivedComplete l E T K ↔ IsIso (S.unit.app K) := by
  obtain ⟨data, hdata, ht, hs, hr, hu, hcomp⟩ := hS
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat
      (C := AdicCompletion.Modules l E T) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso f := hf
  let e := asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨ψ, hψ⟩ := hcomp K P hP e
  rw [AdicCompletion.isDerivedComplete_iff l E T K P hP e, ← hψ]
  exact isIso_comp_right_iff _ ψ.hom

private theorem restriction_complete_cone {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsImmersion f ∨ WeaklyEtale f ∨
      ∃ (Z : Scheme.{u}) (i : Z ⟶ Y) (j : X ⟶ Z),
        IsImmersion i ∧ WeaklyEtale j ∧ j ≫ i = f)
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ)).kFlat P) :
    IsDerivedComplete l E X ((pull l E f).obj (DerivedCategory.Q.obj P)) ↔
      IsZero ((pull l E f).obj (completionCone l E Y P)) := by
  obtain ⟨S, hS, _, _, hres⟩ :=
    StrictCompletionRestriction.strict_completion_restriction_comparison l E
  have hf' : (MorphismProperty.multiplicativeClosure
      (fun {V W : Scheme.{u}} (g : V ⟶ W) ↦ IsImmersion g ∨ WeaklyEtale g)) f := by
    rcases hf with hi | hw | ⟨Z, i, j, hi, hj, rfl⟩
    · exact MorphismProperty.le_multiplicativeClosure _ _ (.inl hi)
    · exact MorphismProperty.le_multiplicativeClosure _ _ (.inr hw)
    · exact MorphismProperty.multiplicativeClosure.comp_of j i
        (MorphismProperty.le_multiplicativeClosure _ _ (.inr hj)) (.inl hi)
  obtain ⟨_, ⟨cmp⟩⟩ := hres f hf'
  obtain ⟨data, hd, ht, hs, hr, hu, hcomp⟩ := hS Y
  obtain ⟨ψ, hψ⟩ := hcomp (DerivedCategory.Q.obj P) P hP (Iso.refl _)
  have hunit : (S Y).unit.app (DerivedCategory.Q.obj P) ≫ ψ.hom =
      DerivedCategory.Q.map (AdicCompletion.augmentation l E Y P) := by
    simpa only [AdicCompletion.completionMap, Iso.refl_inv, Category.id_comp] using hψ
  rw [presentation_complete l E X (S X) (hS X)]
  have hc : IsIso ((S X).unit.app ((pull l E f).obj (DerivedCategory.Q.obj P))) ↔
      IsIso ((pull l E f).map ((S Y).unit.app (DerivedCategory.Q.obj P))) := by
    rw [← cmp.unit]
    exact isIso_comp_right_iff _ (cmp.derived.hom.app (DerivedCategory.Q.obj P))
  rw [hc]
  have he : IsIso ((pull l E f).map ((S Y).unit.app (DerivedCategory.Q.obj P)) ≫
      (pull l E f).map ψ.hom) ↔
      IsIso ((pull l E f).map ((S Y).unit.app (DerivedCategory.Q.obj P))) := by
    exact isIso_comp_right_iff _ ((pull l E f).map ψ.hom)
  rw [← he, ← Functor.map_comp, hunit]
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
    ((pull l E f).map_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished
        (AdicCompletion.augmentation l E Y P)))).symm

private theorem module_empty (T : Scheme.{u}) [IsEmpty T]
    (M : AdicCompletion.Modules l E T) : IsZero M := by
  apply CondensedRing.isZero_of_isZero_X (DerivedNakayama.integerRing l E)
  apply Sheaf.isZero_of_isZero_obj
  intro V
  have : IsEmpty V.unop.left := ⟨fun x ↦ (inferInstance : IsEmpty T).false (V.unop.hom x)⟩
  exact (Scheme.ProEt.isTerminalSectionsOfIsEmpty M.X V.unop).isZero

private theorem module_cover_zero {T : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T)
    (M : AdicCompletion.Modules l E T)
    (h : ∀ i : C.I₀, IsZero
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) (C.f i)).obj M)) :
    IsZero M := by
  apply CondensedRing.isZero_of_isZero_X (DerivedNakayama.integerRing l E)
  rw [IsZero.iff_id_eq_zero]
  have (i : C.I₀) : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
  have hiso : IsIso (0 : M.X ⟶ M.X) := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} (0 : M.X ⟶ M.X)
      C.f C.mem₀ fun i ↦ ?_
    apply (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (C.f i) inferInstance) _).1
    have hz := ((Mod.forget _).map_isZero (h i)).of_iso
      ((CondensedRing.upperStarObjXIso (DerivedNakayama.integerRing l E) (C.f i) M).symm)
    exact isIso_of_source_target_iso_zero _ hz.isoZero hz.isoZero
  exact (cancel_mono (0 : M.X ⟶ M.X)).mp (by simp)

private theorem module_strata_zero
    [CompactSpace W] [QuasiSeparatedSpace W]
    (hc : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (M : AdicCompletion.Modules l E W)
    (h : ∀ a : Fin S.n, IsZero
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) (S.immersion a)).obj M)) :
    IsZero M := by
  have (a : Fin S.n) : IsImmersion (S.immersion a) := S.isImmersion a
  have (a : Fin S.n) : CompactSpace (S.domain a) := by
    rw [← isCompact_univ_iff]
    apply (S.immersion a).isEmbedding.isCompact_iff.mpr
    simpa only [Set.image_univ, S.range_immersion, Set.inter_univ] using
      (hc a).isRetrocompact isCompact_univ isOpen_univ
  have (a : Fin S.n) : QuasiCompact (S.immersion a) := inferInstance
  apply CondensedRing.isZero_of_isZero_X (DerivedNakayama.integerRing l E)
  rw [IsZero.iff_id_eq_zero]
  apply eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp S.immersion
  · intro x
    have hx : x ∈ ⋃ a, S.stratum a := by rw [S.iUnion_stratum_eq_univ]; trivial
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    exact ⟨a, (S.range_immersion a).symm ▸ ha⟩
  · intro a
    have hz := ((Mod.forget _).map_isZero (h a)).of_iso
      ((CondensedRing.upperStarObjXIso (DerivedNakayama.integerRing l E)
        (S.immersion a) M).symm)
    exact hz.eq_of_src _ _

private theorem pull_homology_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (AdicCompletion.Modules l E Y)) (q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj ((pull l E f).obj K)) ↔
      IsZero ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).obj
        ((DerivedCategory.homologyFunctor _ q).obj K)) := by
  let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f
  let e := F.mapDerivedCategoryHomologyFunctorIso q
  exact ⟨fun h ↦ h.of_iso (e.app K), fun h ↦ h.of_iso (e.app K).symm⟩

private theorem strata_homology_zero [CompactSpace W] [QuasiSeparatedSpace W]
    (hc : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (K : DerivedCategory (AdicCompletion.Modules l E W)) (q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) ↔
      ∀ (a : Fin S.n) (i : (𝒰 a).I₀), IsZero
        ((DerivedCategory.homologyFunctor _ q).obj
          ((pull l E ((𝒰 a).f i)).obj ((pull l E (S.immersion a)).obj K))) := by
  constructor
  · intro h a i
    exact (pull_homology_zero l E _ _ _).2
      ((CondensedRing.upperStar _ _).map_isZero
        ((pull_homology_zero l E _ _ _).2
          ((CondensedRing.upperStar _ _).map_isZero h)))
  · intro h
    apply module_strata_zero l E S hc
    intro a
    apply module_cover_zero l E (𝒰 a)
    intro i
    have hz := (pull_homology_zero l E ((𝒰 a).f i) _ q).1 (h a i)
    let F := CondensedRing.upperStar (DerivedNakayama.integerRing l E) (S.immersion a)
    exact hz.of_iso ((CondensedRing.upperStar _ ((𝒰 a).f i)).mapIso
      ((F.mapDerivedCategoryHomologyFunctorIso q).app K))

private theorem module_tree_zero {T : Scheme.{u}} {t : T ⟶ W}
    (tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) T t)
    (M : AdicCompletion.Modules l E W)
    (h : tree.AllLeaves (fun _L branch ↦ IsZero
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) branch).obj M))) :
    IsZero ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) t).obj M) := by
  induction tree with
  | tip t _ _ _ => exact h
  | node t f g hcompact hqs himm hf hg hfqc hgqc hcov hd ha left right ihl ihr =>
    have := hf
    have := hg
    have := hfqc
    apply CondensedRing.isZero_of_isZero_upperStar_of_isCompl
      (DerivedNakayama.integerRing l E) g f
    · exact ⟨hd.symm, codisjoint_iff.mpr (by simpa only [Set.sup_eq_union,
        Set.top_eq_univ] using (Set.union_comm _ _).trans hcov)⟩
    · exact (ihr h.2).of_iso ((CondensedRing.upperStarComp _ g t).app M).symm
    · exact (ihl h.1).of_iso ((CondensedRing.upperStarComp _ f t).app M).symm

private theorem leaf_module_zero {L : Scheme.{u}} (branch : L ⟶ W)
    (hfac : Nonempty L → ∃ (a : Fin S.n) (t : L ⟶ S.domain a),
      t ≫ S.immersion a = branch)
    (M : AdicCompletion.Modules l E W)
    (h : leafCoverTest S 𝒰 (fun _ r ↦ IsZero
      ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) r).obj M)) L branch) :
    IsZero ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) branch).obj M) := by
  cases isEmpty_or_nonempty L with
  | inl hempty => exact module_empty l E L _
  | inr hn =>
    obtain ⟨a, t, ht⟩ := hfac hn
    apply module_cover_zero l E (leafCover S 𝒰 a t)
    intro i
    exact (h a t ht i).of_iso
      ((CondensedRing.upperStarComp _ ((leafCover S 𝒰 a t).f i) branch).app M).symm

private theorem allLeaves_true {T : Scheme.{u}} {t : T ⟶ W}
    (tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) T t) :
    tree.AllLeaves (fun _ _ ↦ True) := by
  induction tree with
  | tip => trivial
  | node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihl ihr => exact ⟨ihl, ihr⟩

private theorem allLeaves_and {T : Scheme.{u}} {t : T ⟶ W}
    (tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) T t)
    (P Q : ∀ L : Scheme.{u}, (L ⟶ W) → Prop)
    (hP : tree.AllLeaves P) (hQ : tree.AllLeaves Q) :
    tree.AllLeaves (fun L branch ↦ P L branch ∧ Q L branch) := by
  induction tree with
  | tip => exact ⟨hP, hQ⟩
  | node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihl ihr =>
    exact ⟨ihl hP.1 hQ.1, ihr hP.2 hQ.2⟩

private theorem tree_homology_zero
    (tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) W (𝟙 W))
    (hfac : tree.AllLeaves (fun L branch ↦ Nonempty L →
      ∃ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch))
    (K : DerivedCategory (AdicCompletion.Modules l E W)) (q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) ↔
      tree.AllLeaves (leafCoverTest S 𝒰 (fun _ r ↦ IsZero
        ((DerivedCategory.homologyFunctor _ q).obj ((pull l E r).obj K)))) := by
  constructor
  · intro h
    have hall := allLeaves_true tree
    exact tree.allLeaves_mono (fun L branch _ a t ht i ↦
      (pull_homology_zero l E _ _ _).2 ((CondensedRing.upperStar _ _).map_isZero h)) hall
  · intro h
    have hleaf : tree.AllLeaves (fun L branch ↦ IsZero
        ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) branch).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) := by
      have hp : tree.AllLeaves (fun L branch ↦
          (Nonempty L → ∃ (a : Fin S.n) (t : L ⟶ S.domain a),
            t ≫ S.immersion a = branch) ∧
          leafCoverTest S 𝒰 (fun _ r ↦ IsZero
            ((DerivedCategory.homologyFunctor _ q).obj ((pull l E r).obj K))) L branch) := by
        exact allLeaves_and tree _ _ hfac h
      apply tree.allLeaves_mono (fun L branch hh ↦ ?_) hp
      apply leaf_module_zero l E S 𝒰 branch hh.1
      intro a t ht i
      exact (pull_homology_zero l E _ _ _).1 (hh.2 a t ht i)
    have hz := module_tree_zero l E tree _ hleaf
    exact hz.of_iso ((profinitePointModuleIdentity _ W).app _).symm

private theorem strata_derived_zero [CompactSpace W] [QuasiSeparatedSpace W]
    (hc : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (K : DerivedCategory (AdicCompletion.Modules l E W)) :
    IsZero K ↔ ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      IsZero ((pull l E ((𝒰 a).f i)).obj ((pull l E (S.immersion a)).obj K)) := by
  constructor
  · intro h a i
    exact (pull l E _).map_isZero ((pull l E _).map_isZero h)
  · intro h
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro q
    exact (strata_homology_zero l E S 𝒰 hc K q).2
      (fun a i ↦ (DerivedCategory.homologyFunctor _ q).map_isZero (h a i))

private theorem tree_immersions {T : Scheme.{u}} {t : T ⟶ W}
    (tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) T t) :
    tree.AllLeaves (fun _ r ↦ IsImmersion r) := by
  induction tree with
  | tip _ _ _ hi => exact hi
  | node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihl ihr => exact ⟨ihl, ihr⟩

private theorem strata_complete [CompactSpace W] [QuasiSeparatedSpace W]
    (hc : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a))
    (K : DerivedCategory (AdicCompletion.Modules l E W)) :
    IsDerivedComplete l E W K ↔ ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
      IsDerivedComplete l E ((𝒰 a).X i)
        ((pull l E ((𝒰 a).f i)).obj ((pull l E (S.immersion a)).obj K)) := by
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat
      (C := AdicCompletion.Modules l E W) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso f := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have h0 := (complete_iso l E e.symm).trans (complete_cone l E W P hP)
  rw [h0, strata_derived_zero l E S 𝒰 hc]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro i
  let ec := profinitePointModuleDerivedComp (DerivedNakayama.integerRing l E)
    ((𝒰 a).f i) (S.immersion a)
  let ep := ec.app (DerivedCategory.Q.obj P) ≪≫
    (pull l E ((𝒰 a).f i)).mapIso ((pull l E (S.immersion a)).mapIso e)
  have hwe : WeaklyEtale ((𝒰 a).f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ (𝒰 a).mem₀ (.mk i)
  exact (ec.app (completionCone l E W P)).isZero_iff.symm |>.trans
    ((restriction_complete_cone l E _
      (.inr (.inr ⟨S.domain a, S.immersion a, (𝒰 a).f i,
        S.isImmersion a, hwe, rfl⟩)) P hP).symm.trans (complete_iso l E ep))

private theorem tree_complete
    (tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) W (𝟙 W))
    (hfac : tree.AllLeaves (fun L branch ↦ Nonempty L →
      ∃ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch))
    (K : DerivedCategory (AdicCompletion.Modules l E W)) :
    IsDerivedComplete l E W K ↔
      tree.AllLeaves (leafCoverTest S 𝒰 (fun T r ↦
        IsDerivedComplete l E T ((pull l E r).obj K))) := by
  obtain ⟨P, f, hf, _, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat
      (C := AdicCompletion.Modules l E W) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso f := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have h0 := (complete_iso l E e.symm).trans (complete_cone l E W P hP)
  have hlocal {L : Scheme.{u}} (branch : L ⟶ W) (hi : IsImmersion branch)
      (a : Fin S.n) (t : L ⟶ S.domain a) (ht : t ≫ S.immersion a = branch)
      (i : (𝒰 a).I₀) :
      IsDerivedComplete l E ((leafCover S 𝒰 a t).X i)
        ((pull l E ((leafCover S 𝒰 a t).f i ≫ branch)).obj K) ↔
      IsZero ((pull l E ((leafCover S 𝒰 a t).f i ≫ branch)).obj
        (completionCone l E W P)) := by
    have hwe : WeaklyEtale ((leafCover S 𝒰 a t).f i) :=
      Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _
        (leafCover S 𝒰 a t).mem₀ (.mk i)
    exact (complete_iso l E ((pull l E _).mapIso e).symm).trans
      (restriction_complete_cone l E _
        (.inr (.inr ⟨L, branch, (leafCover S 𝒰 a t).f i, hi, hwe, rfl⟩)) P hP)
  have himm := tree_immersions tree
  constructor
  · intro h
    have hz := h0.1 h
    exact tree.allLeaves_mono (fun L branch hi a t ht i ↦
      (hlocal branch hi a t ht i).2 ((pull l E _).map_isZero hz)) himm
  · intro h
    apply h0.2
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro q
    apply (tree_homology_zero l E S 𝒰 tree hfac _ q).2
    have hh := allLeaves_and tree _ _ himm h
    exact tree.allLeaves_mono (fun L branch hh a t ht i ↦
      (DerivedCategory.homologyFunctor _ q).map_isZero
        ((hlocal branch hh.1 a t ht i).1 (hh.2 a t ht i))) hh

private theorem refinement_tree [CompactSpace W] [QuasiSeparatedSpace W]
    (hc : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) :
    ∃ tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) W (𝟙 W),
      tree.AllLeaves (fun L branch ↦ Nonempty L →
        ∃ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch) := by
  classical
  have hc' (a : Fin 1) (j : Fin S.n) :
      Topology.IsConstructible (Set.range (S.immersion j).base) := by
    simpa only [← S.range_immersion j] using hc j
  have hcover (a : Fin 1) :
      (⋃ j : Fin S.n, Set.range (S.immersion j).base) = Set.univ := by
    simpa only [S.range_immersion] using S.iUnion_stratum_eq_univ
  have hdisj (a : Fin 1) : Pairwise (fun j k : Fin S.n ↦
      Disjoint (Set.range (S.immersion j).base) (Set.range (S.immersion k).base)) := by
    simpa only [S.range_immersion] using S.pairwise_disjoint_stratum
  obtain ⟨O, Q, Z, o, c, q, z, ho, hc, hq, hz, hco, hoqc, hqqc, hqr, hzr,
    N, V, toW, root, parent, left, right, le, re, leaf,
    ⟨eroot, heroot⟩, hparent, horder, hle, hre, hcompact, hqs, himm,
    hchildren, hleaf, hsplit, hallowed, hcovered, hdisjoint, hfactor⟩ :=
    Scheme.exists_finite_open_closed_refinement 1 (fun _ ↦ S.n)
      (fun _ ↦ S.domain) (fun _ ↦ S.immersion) (fun _ ↦ S.isImmersion)
      hc' hcover hdisj
  have build (k : ℕ) : ∀ v : Fin N, N - v.val = k →
      ∃ tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) (V v) (toW v),
        tree.AllLeaves (fun L branch ↦ Nonempty L →
          ∃ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      by_cases hl : leaf v
      · exact ⟨.tip _ (hcompact v) (hqs v) (himm v), fun hn ↦ hfactor v hl hn 0⟩
      · obtain ⟨hne, hleft, hright, hpl, hpr, hol, hcr, hql, hqr, hcov, hd⟩ := hsplit v hl
        have htl := ih (N - (left v).val) (by omega) (left v) rfl
        have htr := ih (N - (right v).val) (by omega) (right v) rfl
        rw [← hle v hl] at htl
        rw [← hre v hl] at htr
        obtain ⟨tl, htl⟩ := htl
        obtain ⟨tr, htr⟩ := htr
        exact ⟨.node (toW v) (le v) (re v) (hcompact v) (hqs v) (himm v)
          hol hcr hql hqr hcov hd trivial tl tr, htl, htr⟩
  have ht := build _ root rfl
  rw [← heroot] at ht
  obtain ⟨tree, ht⟩ := ht
  cases tree with
  | tip t hcompact hqs himm =>
    refine ⟨.tip (𝟙 W) inferInstance inferInstance inferInstance, ?_⟩
    intro hn
    have hn' : Nonempty (V root) := ⟨eroot.inv hn.some⟩
    obtain ⟨a, t, hfac⟩ := ht hn'
    exact ⟨a, eroot.inv ≫ t, by rw [Category.assoc, hfac, eroot.inv_hom_id]⟩
  | @node T L R t le re hcompact hqs himm hl hr hlqc hrqc hcover hd ha tl tr =>
    have := hl
    have := hr
    have := hlqc
    have := hrqc
    have hcover' : Set.range (le ≫ eroot.hom).base ∪
        Set.range (re ≫ eroot.hom).base = Set.univ := by
      rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp,
        Set.range_comp, Set.range_comp, ← Set.image_union, hcover, Set.image_univ]
      exact Set.range_eq_univ.mpr eroot.hom.surjective
    have hd' : Disjoint (Set.range (le ≫ eroot.hom).base)
        (Set.range (re ≫ eroot.hom).base) := by
      rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp,
        Set.range_comp, Set.range_comp]
      exact hd.image eroot.hom.injective.injOn (Set.subset_univ _) (Set.subset_univ _)
    have hl' : ∃ tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True)
        L ((le ≫ eroot.hom) ≫ 𝟙 W), tree.AllLeaves (fun L branch ↦ Nonempty L →
          ∃ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch) := by
      simpa only [Category.comp_id] using ⟨tl, ht.1⟩
    have hr' : ∃ tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True)
        R ((re ≫ eroot.hom) ≫ 𝟙 W), tree.AllLeaves (fun L branch ↦ Nonempty L →
          ∃ (a : Fin S.n) (t : L ⟶ S.domain a), t ≫ S.immersion a = branch) := by
      simpa only [Category.comp_id] using ⟨tr, ht.2⟩
    obtain ⟨tl', htl'⟩ := hl'
    obtain ⟨tr', htr'⟩ := hr'
    exact ⟨.node (𝟙 W) (le ≫ eroot.hom) (re ≫ eroot.hom)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance hcover' hd' trivial tl' tr', htl', htr'⟩

/-- Finite-stratum and leaf-cover detection of strict completion, each cohomology degree,
and the cone of the specified completion unit, retaining the scalar models and matrices.
Source: blueprint main-20261015, finite-model proof, Strata and Locality;
Stacks Tags 09Y4, 09AA, 09AH, 09BM, 03DJ, 04TQ
(blueprint: lem-sfb-finite-strata-completion-detection).

Proof: (1) Apply lem-fix-constructible-open-closed-refinement to the given constructible
partition. Obtain the finite qcqs open/closed tree and actual stratum factorizations.
Base change the covers using weakly-etale stability and the fpqc covering axioms.
(2) Cartesian coefficients make inverse image exact. Immersion inverse image preserves
products by lem-weil-pbc-proetale-immersion-limit-preservation. Cover restriction is slice
restriction by weakly-etale localization; its extension-by-zero adjunction preserves products.
Exact inverse image commutes with each cohomology functor.
(3) In lem-pe-principal-reduction-cone-calculus the reductions are Cone(pi^n), their
transitions are (x,y) ↦ (x,pi*y), and their augmentations are m ↦ (m,0). Products and finite
cones identify their Roos 1-shift maps under restriction. The shifted-product coordinate
of the unit stays zero. Lem-pe-completion-triangle-comparison identifies precisely these
units with strict completion, not merely the completion objects.
(4) At each internal vertex use the arbitrary-ring proetale open/closed short exact
sequence. Lem-sfb-exact-open-closed-unbounded-calculus gives joint reflection of derived
isomorphisms; the sheaf cover criterion detects module isomorphisms on each leaf cover.
(5) Apply exact-cohomology comparison and cover detection on leaves, and induct through
the finite tree to detect each degree separately. Apply the same reflection to the unit;
the quasi-isomorphism/cone-acyclicity criterion gives the asserted cone zero-detection.
(6) Since stratum and branch immersions are monomorphisms, each leaf factor is a base
change of its branch immersion. Hence its further cover restriction is an immersion.
Pullback composition identifies the branch-cover and original-cover routes, proving both
directions of the original-cover equivalences.
(7) Apply definition-constructible-sheaves--1 to a finite scalar presentation. Exact
inverse image preserves finite colimits, the regular module and each constant scalar.
Lem-sfb-finite-colimit-matrix-cokernels therefore preserves the same entries, sizes and
cokernel, and hence the same scalar module.
(8) The empty covering forces all modules on an empty scheme to be zero. Empty leaves
and the empty root therefore impose no extra tests. No boundedness, Noetherianity or
invertibility of l is used, and no original stratum is required to be globally open. -/
theorem finite_strata_completion_detection
    [CompactSpace W] [QuasiSeparatedSpace W]
    (_hc : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) :
    (∀ K : DerivedCategory (AdicCompletion.Modules l E W),
      (IsDerivedComplete l E W K ↔ ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
        IsDerivedComplete l E ((𝒰 a).X i)
          ((pull l E ((𝒰 a).f i)).obj ((pull l E (S.immersion a)).obj K))) ∧
      (∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor _ q).obj K) ↔
        ∀ (a : Fin S.n) (i : (𝒰 a).I₀),
          IsZero ((DerivedCategory.homologyFunctor _ q).obj
            ((pull l E ((𝒰 a).f i)).obj ((pull l E (S.immersion a)).obj K))))) ∧
    ∃ tree : Scheme.SchemeRefinementTree W (fun _ _ _ _ _ _ ↦ True) W (𝟙 W),
      tree.AllLeaves (fun L branch ↦
        (Nonempty L → ∃ (a : Fin S.n) (t : L ⟶ S.domain a),
          t ≫ S.immersion a = branch) ∧
        (IsEmpty L → ∀ M : AdicCompletion.Modules l E L, IsZero M) ∧
        leafScalarModels l E S 𝒰 L branch) ∧
      (∀ K : DerivedCategory (AdicCompletion.Modules l E W),
        (IsDerivedComplete l E W K ↔
          tree.AllLeaves (leafCoverTest S 𝒰 (fun T r ↦
            IsDerivedComplete l E T ((pull l E r).obj K)))) ∧
        (∀ q : ℤ, IsZero ((DerivedCategory.homologyFunctor _ q).obj K) ↔
          tree.AllLeaves (leafCoverTest S 𝒰 (fun _ r ↦
            IsZero ((DerivedCategory.homologyFunctor _ q).obj ((pull l E r).obj K)))))) ∧
      (∀ (P : CochainComplex (AdicCompletion.Modules l E W) ℤ)
        (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E W) (.up ℤ)).kFlat P),
        IsZero (completionCone l E W P) ↔
          tree.AllLeaves (leafCoverTest S 𝒰 (fun _ r ↦
            IsZero ((pull l E r).obj (completionCone l E W P))))) := by
  classical
  obtain ⟨tree, hfac⟩ := refinement_tree S _hc
  refine ⟨fun K ↦ ⟨?_, strata_homology_zero l E S 𝒰 _hc K⟩,
    tree, ?_, (fun K ↦ ⟨?_, tree_homology_zero l E S 𝒰 tree hfac K⟩), ?_⟩
  · exact strata_complete l E S 𝒰 _hc K
  · apply tree.allLeaves_mono (fun L branch h ↦ ?_) hfac
    exact ⟨h, fun he M ↦ @module_empty l _ E _ _ _ L he M,
      scalar_leaf_model l E S 𝒰 branch⟩
  · exact tree_complete l E S 𝒰 tree hfac K
  · intro P hP
    constructor
    · intro h
      exact tree.allLeaves_mono (fun L branch _ a t ht i ↦
        (pull l E _).map_isZero h) (allLeaves_true tree)
    · intro h
      apply DerivedCategory.isZero_of_forall_isZero_homology
      intro q
      apply (tree_homology_zero l E S 𝒰 tree hfac _ q).2
      exact tree.allLeaves_mono (fun L branch hh a t ht i ↦
        (DerivedCategory.homologyFunctor _ q).map_isZero (hh a t ht i)) h

end AlgebraicGeometry.ProEtale.FiniteStrataCompletion
