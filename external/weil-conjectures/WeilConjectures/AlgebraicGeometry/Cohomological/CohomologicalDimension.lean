/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.QcqsHigherImagesPrimeTorsion
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Data.Nat.Factors
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Prime-power cohomological dimension

Source: blueprint `definition-cohomological-dimension`, order 1506; Stacks Project, Tag 0F10
(blueprint: definition-cohomological-dimension).

The common annihilator diagram gives the canonical filtered-colimit torsion condition
on both sites. Its local sectionwise form is also stated for the pro-étale site.
The comparison and finiteness statements are the corresponding blueprint clauses.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- A sheaf is locally `ℓ`-power torsion: every section is locally killed by a power of `ℓ`.
This is equivalent to the canonical map from the filtered colimit of the kernels of
`ℓ ^ r` to the sheaf being an isomorphism, with the inclusions as transition maps.
Source: blueprint `definition-cohomological-dimension`, opening local torsion convention
(blueprint: definition-cohomological-dimension). -/
def IsEllPowerTorsionLocal {X : Scheme.{u}} (ℓ : ℕ) (_hℓ : Nat.Prime ℓ)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ ⦃U : X.ProEtᵒᵖ⦄ (s : F.obj.obj U),
    ∃ S ∈ Scheme.ProEt.topology X U.unop,
      ∀ ⦃V : X.ProEt⦄ (f : V ⟶ U.unop), S f →
        ∃ r : ℕ, (ℓ ^ r) • (F.obj.map f.op).hom s = 0

/-- The `r`th annihilator subsheaf `F[ℓ ^ r]`, defined as the kernel of scalar
multiplication by `ℓ ^ r`.
Source: blueprint `definition-cohomological-dimension`, opening local torsion convention (blueprint:
definition-cohomological-dimension). -/
noncomputable def ellPowerKernel {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} (r : ℕ) : A :=
  kernel ((ℓ ^ r : ℕ) • 𝟙 F)

/-- The scalar-power annihilation identity needed by the kernel lift.
Source: blueprint `definition-cohomological-dimension`, opening kernel transition convention
(blueprint: definition-cohomological-dimension). Proof: write s = r + (s - r). Multiplication by
`ℓ ^ s` factors as multiplication by `ℓ ^ r` followed by multiplication by `ℓ ^ (s - r)`; the kernel
inclusion annihilates the first factor, so their composite is zero. -/
theorem ellPowerKernelMap_condition {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s : ℕ} (h : r ≤ s) :
    kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F) ≫ ((ℓ ^ s : ℕ) • 𝟙 F) = 0 := by
  have hr : (ℓ ^ r : ℕ) • kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F) = 0 := by
    simpa only [Preadditive.comp_nsmul, Category.comp_id] using
      kernel.condition ((ℓ ^ r : ℕ) • 𝟙 F)
  rw [Preadditive.comp_nsmul, Category.comp_id,
    ← Nat.add_sub_of_le h, pow_add, mul_comm, mul_smul, hr, smul_zero]

/-- The inclusion `F[ℓ ^ r] ⟶ F[ℓ ^ s]` for `r ≤ s`. Its underlying map is the
canonical kernel lift; the annihilation identity is the scalar-power identity.
Source: blueprint `definition-cohomological-dimension`, opening local torsion convention
(blueprint: definition-cohomological-dimension). -/
noncomputable def ellPowerKernelMap {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s : ℕ} (h : r ≤ s) :
    ellPowerKernel ℓ (F := F) r ⟶ ellPowerKernel ℓ (F := F) s :=
  kernel.lift ((ℓ ^ s : ℕ) • 𝟙 F) (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F))
    (ellPowerKernelMap_condition ℓ h)

/-- Identity law for the annihilator transition maps.
Source: blueprint `definition-cohomological-dimension`, opening filtered kernel diagram (blueprint:
definition-cohomological-dimension). Proof: uniqueness of kernel lifts for the identity
transition. -/
theorem ellPowerKernelFunctor_map_id {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} (r : ℕ) :
    ellPowerKernelMap ℓ (F := F) (le_refl r) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F))).1
  simp only [ellPowerKernelMap, kernel.lift_ι, Category.id_comp]

/-- Composition law for the annihilator transition maps.
Source: blueprint `definition-cohomological-dimension`, opening filtered kernel diagram (blueprint:
definition-cohomological-dimension). Proof: uniqueness of kernel lifts and transitivity of `≤`. -/
theorem ellPowerKernelFunctor_map_comp {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s t : ℕ}
    (f : r ⟶ s) (g : s ⟶ t) :
    ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom (f ≫ g)) =
      ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom f) ≫
        ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom g) := by
  apply (cancel_mono (kernel.ι ((ℓ ^ t : ℕ) • 𝟙 F))).1
  simp [ellPowerKernelMap, Category.assoc]

/-- The filtered diagram of annihilator subsheaves with its canonical inclusion maps.
Source: blueprint `definition-cohomological-dimension`, opening local torsion convention
(blueprint: definition-cohomological-dimension). -/
noncomputable def ellPowerKernelFunctor {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} : ℕ ⥤ A where
  obj r := ellPowerKernel ℓ (F := F) r
  map f := ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom f)
  map_id := fun r ↦ ellPowerKernelFunctor_map_id ℓ r
  map_comp := fun f g ↦ ellPowerKernelFunctor_map_comp ℓ f g

/-- Naturality of the annihilator inclusions into `F`.
Source: blueprint `definition-cohomological-dimension`, opening filtered kernel cocone (blueprint:
definition-cohomological-dimension). Proof: the defining equation of the kernel lift. -/
theorem ellPowerKernelCocone_naturality {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} {r s : ℕ} (f : r ⟶ s) :
    ellPowerKernelMap ℓ (F := F) (CategoryTheory.leOfHom f) ≫
        kernel.ι ((ℓ ^ s : ℕ) • 𝟙 F) = kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F) := by
  exact kernel.lift_ι _ _ _

/-- The cocone of the annihilator inclusions into `F`.
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
noncomputable def ellPowerKernelCocone {A : Type v} [Category.{w} A] [Abelian A]
    (ℓ : ℕ) {F : A} :
    Cocone (ellPowerKernelFunctor ℓ (F := F)) where
  pt := F
  ι := { app := fun r ↦ by
           simpa [ellPowerKernelFunctor, ellPowerKernel] using
             (kernel.ι ((ℓ ^ r : ℕ) • 𝟙 F))
         naturality := by
           intro r s f
           simpa [ellPowerKernelFunctor] using ellPowerKernelCocone_naturality ℓ (F := F) f }

/-- The canonical map from the filtered colimit of the annihilator subsheaves to `F`.
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
noncomputable def ellPowerKernelColimitMap {A : Type v} [Category.{w} A] [Abelian A]
    [HasColimitsOfShape ℕ A] (ℓ : ℕ) {F : A} :
    colimit (ellPowerKernelFunctor ℓ (F := F)) ⟶ F :=
  colimit.desc _ (ellPowerKernelCocone ℓ (F := F))

/-- Prime-power torsion in the canonical local-colimit convention.
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
def IsEllPowerTorsion {A : Type v} [Category.{w} A] [Abelian A]
    [HasColimitsOfShape ℕ A] (ℓ : ℕ) (_hℓ : Nat.Prime ℓ)
    (F : A) : Prop :=
  IsIso (ellPowerKernelColimitMap ℓ (F := F))

private theorem ellPowerTorsion_isColimit_iff
    {A : Type v} [Category.{w} A] [Abelian A] [HasColimitsOfShape ℕ A]
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (F : A) :
    IsEllPowerTorsion ℓ hℓ F ↔ Nonempty (IsColimit (ellPowerKernelCocone ℓ (F := F))) := by
  constructor
  · intro h
    have : IsIso ((colimit.isColimit (ellPowerKernelFunctor ℓ (F := F))).desc
        (ellPowerKernelCocone ℓ (F := F))) := h
    exact ⟨IsColimit.ofPointIso (colimit.isColimit _)⟩
  · rintro ⟨h⟩
    exact inferInstanceAs (IsIso ((colimit.isColimit _).coconePointUniqueUpToIso h).hom)

private theorem ellPowerTorsion_exact_iff
    {A : Type v} [Category.{w} A] [Abelian A] [HasColimitsOfShape ℕ A]
    {B : Type*} [Category B] [Abelian B] [HasColimitsOfShape ℕ B]
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesColimitsOfShape ℕ H]
    [H.Full] [H.Faithful] (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (F : A) :
    IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsion ℓ hℓ (H.obj F) := by
  let D := ellPowerKernelFunctor ℓ (F := F)
  let D' := ellPowerKernelFunctor ℓ (F := H.obj F)
  let c := ellPowerKernelCocone ℓ (F := F)
  let c' := ellPowerKernelCocone ℓ (F := H.obj F)
  let e (n : ℕ) : H.obj (D.obj n) ≅ D'.obj n :=
    PreservesKernel.iso H ((ℓ ^ n) • 𝟙 F) ≪≫
      kernel.mapIso _ _ (Iso.refl _) (Iso.refl _) (by simp)
  have he (n : ℕ) : (e n).hom ≫ c'.ι.app n = H.map (c.ι.app n) := by
    simp [e, c, c', ellPowerKernelCocone, PreservesKernel.iso_hom]
  let E : D ⋙ H ≅ D' := NatIso.ofComponents e (by
    intro n m f
    apply (cancel_mono (kernel.ι ((ℓ ^ m) • 𝟙 (H.obj F)))).mp
    change (H.map (D.map f) ≫ (e m).hom) ≫ c'.ι.app m =
      ((e n).hom ≫ D'.map f) ≫ c'.ι.app m
    rw [Category.assoc, he, ← H.map_comp]
    have hc' : D'.map f ≫ c'.ι.app m = c'.ι.app n := by simp
    rw [Category.assoc, hc', he]
    congr 1
    simp)
  have ec : H.mapCocone c ≅ (Cocone.precompose E.hom).obj c' :=
    Cocone.ext (Iso.refl _) (by
      intro n
      change H.map (c.ι.app n) ≫ 𝟙 _ = (e n).hom ≫ c'.ι.app n
      simpa using (he n).symm)
  rw [ellPowerTorsion_isColimit_iff, ellPowerTorsion_isColimit_iff]
  constructor
  · rintro ⟨hc⟩
    exact ⟨(IsColimit.precomposeHomEquiv E c')
      ((isColimitOfPreserves H hc).ofIsoColimit ec)⟩
  · rintro ⟨hc⟩
    have ht := ((IsColimit.precomposeHomEquiv E c').symm hc).ofIsoColimit ec.symm
    exact ⟨isColimitOfReflects H ht⟩

private theorem ellPowerTorsion_iff_local_general
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (F : Sheaf J AddCommGrpCat.{u + 1}) :
    IsEllPowerTorsion ℓ hℓ F ↔
      ∀ ⦃V : Cᵒᵖ⦄ (s : F.obj.obj V), ∃ R ∈ J V.unop,
        ∀ ⦃W : C⦄ (g : W ⟶ V.unop), R g →
          ∃ n : ℕ, (ℓ ^ n) • (F.obj.map g.op).hom s = 0 := by
  classical
  let D := ellPowerKernelFunctor ℓ (F := F)
  let c := ellPowerKernelCocone ℓ (F := F)
  let U := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let φ := ellPowerKernelColimitMap ℓ (F := F)
  have hk (n : ℕ) (V : Cᵒᵖ) (t : (D.obj n).obj.obj V) :
      (ℓ ^ n) • (c.ι.app n).hom.app V t = 0 := by
    have heq : c.ι.app n ≫ ((ℓ ^ n) • 𝟙 F) = 0 := kernel.condition _
    have h := congrArg (fun f ↦ (U.map f).app V) heq
    simp only [Functor.map_comp, Functor.map_nsmul,
      NatTrans.comp_app, NatTrans.app_nsmul,
      Functor.map_zero, NatTrans.app_zero] at h
    have ht := ConcreteCategory.congr_hom h t
    change (ℓ ^ n) • (c.ι.app n).hom.app V t = 0 at ht
    exact ht
  constructor
  · intro hF
    have : IsIso φ := hF
    have : IsIso ((colimit.isColimit D).desc c) := hF
    have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit D)
    let P := colimit (D ⋙ U)
    let k : P ⟶ F.obj := colimit.desc (D ⋙ U) (U.mapCocone c)
    let e := (Sheaf.isColimitSheafifyCocone (colimit.cocone (D ⋙ U))
      (colimit.isColimit (D ⋙ U))).coconePointUniqueUpToIso hc
    have hfac : k = toSheafify J P ≫ e.hom.hom := by
      apply colimit.hom_ext
      intro n
      rw [colimit.ι_desc]
      change (c.ι.app n).hom = _
      have he := congrArg (fun f ↦ f.hom)
        ((Sheaf.isColimitSheafifyCocone _ (colimit.isColimit (D ⋙ U))).fac c n)
      rw [ObjectProperty.FullSubcategory.comp_hom,
        Sheaf.sheafifyCocone_ι_app_val] at he
      exact he.symm
    have : Presheaf.IsLocallySurjective J k := by
      rw [hfac]
      infer_instance
    intro V s
    refine ⟨Presheaf.imageSieve k s, Presheaf.imageSieve_mem J k s, ?_⟩
    intro W f hf
    obtain ⟨t, ht⟩ := hf
    let E := (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Opposite.op W)
    have := preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1}
      (forget AddCommGrpCat.{u + 1})
    obtain ⟨n, y, hy⟩ := Concrete.isColimit_exists_rep ((D ⋙ U) ⋙ E)
      (isColimitOfPreserves E (colimit.isColimit (D ⋙ U))) t
    refine ⟨n, ?_⟩
    rw [← ht, ← hy]
    change (ℓ ^ n) • ((colimit.ι (D ⋙ U) n).app (Opposite.op W) ≫
      k.app (Opposite.op W)) y = 0
    rw [← NatTrans.comp_app, colimit.ι_desc]
    exact hk n (Opposite.op W) y
  · intro hF
    have : AB5OfSize.{0, 0} (Sheaf J AddCommGrpCat.{u + 1}) :=
      AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
    have hmono : Mono φ := by
      let α : D ⟶ (Functor.const ℕ).obj F := c.ι
      have : ∀ n, Mono (α.app n) := fun n ↦ inferInstanceAs (Mono (kernel.ι _))
      have : Mono α := NatTrans.mono_of_mono_app _
      have : Mono (colim.map α) := inferInstance
      let e := IsColimit.coconePointUniqueUpToIso
        (colimit.isColimit ((Functor.const ℕ).obj F)) (isColimitConstCocone ℕ F)
      have hφ : φ = colim.map α ≫ e.hom := by
        refine colimit.hom_ext fun n ↦ ?_
        simp [φ, ellPowerKernelColimitMap, e, α, c]
      rw [hφ]
      infer_instance
    have hepi : Epi φ := by
      have : Sheaf.IsLocallySurjective φ := by
        refine ⟨fun {V} s ↦ ?_⟩
        obtain ⟨R, hR, hRs⟩ := hF (V := Opposite.op V) s
        refine J.superset_covering ?_ hR
        intro W g hg
        obtain ⟨n, hns⟩ := hRs g hg
        have hx : ((ℓ ^ n) • 𝟙 F).hom.app (Opposite.op W)
            (F.obj.map g.op s) = 0 := by
          change ((U.map ((ℓ ^ n) • 𝟙 F)).app (Opposite.op W)) _ = 0
          rw [Functor.map_nsmul, NatTrans.app_nsmul]
          exact hns
        let E := U ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op W)
        let e := PreservesKernel.iso E ((ℓ ^ n) • 𝟙 F) ≪≫
          AddCommGrpCat.kernelIsoKer (E.map ((ℓ ^ n) • 𝟙 F))
        let t := e.inv ⟨F.obj.map g.op s, hx⟩
        have ht : (kernel.ι ((ℓ ^ n) • 𝟙 F)).hom.app (Opposite.op W) t =
            F.obj.map g.op s := by
          change (e.inv ≫ E.map (kernel.ι ((ℓ ^ n) • 𝟙 F)))
            ⟨F.obj.map g.op s, hx⟩ = _
          rw [Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι,
            AddCommGrpCat.kernelIsoKer_inv_comp_ι]
          rfl
        refine ⟨(colimit.ι D n).hom.app (Opposite.op W) t, ?_⟩
        rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
          ← ObjectProperty.FullSubcategory.comp_hom]
        change ((colimit.ι D n ≫ colimit.desc D c).hom.app (Opposite.op W)) t = _
        rw [colimit.ι_desc]
        exact ht
      exact Sheaf.epi_of_isLocallySurjective _
    exact isIso_of_mono_of_epi φ

private theorem ellPowerTorsion_iso_iff
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G) :
    IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsion ℓ hℓ G := by
  suffices h : ∀ {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G),
      IsEllPowerTorsion ℓ hℓ F → IsEllPowerTorsion ℓ hℓ G from ⟨h e, h e.symm⟩
  intro F G e hF
  rw [ellPowerTorsion_iff_local_general] at hF ⊢
  intro V s
  obtain ⟨R, hR, hs⟩ := hF (e.inv.hom.app V s)
  refine ⟨R, hR, ?_⟩
  intro W g hg
  obtain ⟨n, hn⟩ := hs g hg
  refine ⟨n, ?_⟩
  have he := congrArg (e.hom.hom.app (Opposite.op W)) hn
  rw [map_nsmul, map_zero] at he
  have he' : e.hom.hom.app (Opposite.op W)
      (F.obj.map g.op (e.inv.hom.app V s)) = G.obj.map g.op s := by
    rw [← ConcreteCategory.comp_apply, e.hom.hom.naturality]
    simp only [ConcreteCategory.comp_apply]
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app V) e.inv_hom_id) s
    exact congrArg (G.obj.map g.op) hi
  rwa [he'] at he

/-- The canonical colimit condition is equivalent to the local annihilator formulation.
Proof: kernels are computed sectionwise, so sections represented in the filtered
colimit are precisely sections locally annihilated by a power of `ℓ`. Sheafification
makes local representability surjectivity; the transition maps are monomorphisms,
so the canonical map is also a monomorphism. This proves both implications.
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
theorem isEllPowerTorsion_iff_local {X : Scheme.{u}} (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    IsEllPowerTorsion ℓ hℓ F ↔ IsEllPowerTorsionLocal ℓ hℓ F := by
  exact ellPowerTorsion_iff_local_general (Scheme.ProEt.topology X) ℓ hℓ F

private theorem ellPowerTorsion_etale_isTorsion {X : Scheme.{u}}
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsEllPowerTorsion ℓ hℓ F) : F.IsTorsion := by
  have h := (ellPowerTorsion_iff_local_general X.smallEtaleTopology ℓ hℓ F).mp hF
  intro V s
  obtain ⟨R, hR, hRs⟩ := h s
  refine ⟨R, hR, ?_⟩
  intro W g hg
  obtain ⟨n, hn⟩ := hRs g hg
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨ℓ ^ n, pow_pos hℓ.pos n, hn⟩

private theorem ellPowerTorsion_etale_iff_stalks {X : Scheme.{u}}
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsEllPowerTorsion ℓ hℓ F ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
        (x : ((Scheme.pointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj F),
        ∃ n : ℕ, (ℓ ^ n) • x = 0 := by
  classical
  let D := ellPowerKernelFunctor ℓ (F := F)
  let c := ellPowerKernelCocone ℓ (F := F)
  let φ := ellPowerKernelColimitMap ℓ (F := F)
  constructor
  · intro hF Ω _ _ s x
    have : IsIso ((colimit.isColimit D).desc c) := hF
    have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit D)
    let L := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
    have : L.Additive := (Scheme.pointSmallEtale s).sheafFiber_additive
    have := preservesFilteredColimitsOfSize_shrink.{0, u + 1, 0, u + 1}
      (forget AddCommGrpCat.{u + 1})
    obtain ⟨n, y, rfl⟩ := Concrete.isColimit_exists_rep (D ⋙ L)
      (isColimitOfPreserves L hc) x
    refine ⟨n, ?_⟩
    have hk : L.map (kernel.ι ((ℓ ^ n) • 𝟙 F)) ≫
        L.map ((ℓ ^ n) • 𝟙 F) = 0 := by
      rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
    rw [Functor.map_nsmul, L.map_id] at hk
    have he := ConcreteCategory.congr_hom hk y
    change (ℓ ^ n) • L.map (kernel.ι ((ℓ ^ n) • 𝟙 F)) y = 0 at he ⊢
    exact he
  · intro hF
    have : AB5OfSize.{0, 0} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      AB5OfSize_shrink.{0, 0, u + 1, u + 1} _
    have hmono : Mono φ := by
      let α : D ⟶ (Functor.const ℕ).obj F := c.ι
      have : ∀ n, Mono (α.app n) := fun n ↦ inferInstanceAs (Mono (kernel.ι _))
      have : Mono α := NatTrans.mono_of_mono_app _
      have : Mono (colim.map α) := inferInstance
      let e := IsColimit.coconePointUniqueUpToIso
        (colimit.isColimit ((Functor.const ℕ).obj F)) (isColimitConstCocone ℕ F)
      have hφ : φ = colim.map α ≫ e.hom := by
        refine colimit.hom_ext fun n ↦ ?_
        simp [φ, ellPowerKernelColimitMap, e, α, c]
      rw [hφ]
      infer_instance
    have hepi : Epi φ := by
      refine ⟨fun {G} g h hgh ↦ ?_⟩
      have hk (n : ℕ) : kernel.ι ((ℓ ^ n) • 𝟙 F) ≫ g =
          kernel.ι ((ℓ ^ n) • 𝟙 F) ≫ h := by
        have he := colimit.ι D n ≫= hgh
        change colimit.ι D n ≫ (colimit.desc D c ≫ g) =
          colimit.ι D n ≫ (colimit.desc D c ≫ h) at he
        rw [← Category.assoc, colimit.ι_desc, ← Category.assoc, colimit.ι_desc] at he
        exact he
      have : HasLimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
        hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
      have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
        AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
      apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
      intro p
      let T := (Scheme.pointSmallEtale (X.algClosurePoint p)).sheafFiber
        (A := AddCommGrpCat.{u + 1})
      have : T.Additive :=
        (Scheme.pointSmallEtale (X.algClosurePoint p)).sheafFiber_additive
      ext x
      obtain ⟨n, hx⟩ := hF _ (X.algClosurePoint p) x
      have : LocallySmall.{u} X.Etale := ⟨fun _ _ ↦ small_self _⟩
      have : PreservesFiniteLimits T := inferInstance
      have hS := (ShortComplex.kernelSequence_exact ((ℓ ^ n) • 𝟙 F)).map_of_mono_of_preservesKernel
        T inferInstance inferInstance
      have hx' : T.map ((ℓ ^ n) • 𝟙 F) x = 0 := by
        simpa only [Functor.map_nsmul, T.map_id, AddCommGrpCat.hom_nsmul,
          AddMonoidHom.nsmul_apply, AddCommGrpCat.id_apply] using hx
      obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).1 hS x hx'
      have he := congr(T.map $(hk n) z)
      simp only [Functor.map_comp] at he
      rw [← hz]
      exact he
    exact isIso_of_mono_of_epi φ

private theorem ellPowerTorsion_higherDirectImage {X Y : Scheme.{u}}
    (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsEllPowerTorsion ℓ hℓ F) (q : ℕ) :
    IsEllPowerTorsion ℓ hℓ (((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived q).obj F) := by
  let G := (DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} g).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
      (y : ((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G),
      ∃ n : ℕ, (ℓ ^ n) • y = 0 := by
    intro Ω _ _ s y
    obtain ⟨m, hm, hy, hmp⟩ :=
      Etale.qcqs_higherDirectImages_prime_torsion g {ℓ} F (by
        intro Ω _ _ s x
        obtain ⟨n, hn⟩ := (ellPowerTorsion_etale_iff_stalks ℓ hℓ F).mp hF Ω s x
        refine ⟨ℓ ^ n, pow_pos hℓ.pos n, hn, ?_⟩
        intro p hp hpn
        exact Set.mem_singleton_iff.mpr
          ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow hpn))) q Ω s y
    have hn := Nat.eq_prime_pow_of_unique_prime_dvd hm.ne' (by
      intro p hp hpm
      exact Set.mem_singleton_iff.mp (hmp p hp hpm))
    exact ⟨m.primeFactorsList.length, hn ▸ hy⟩
  let e := (Etale.lowerStar AddCommGrpCat.{u + 1} g)
    |>.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q
  apply (ellPowerTorsion_etale_iff_stalks ℓ hℓ _).mpr
  intro Ω _ _ s y
  let T := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  let e' := T.mapIso e
  obtain ⟨n, hn⟩ := hG Ω s (e'.inv y)
  refine ⟨n, ?_⟩
  have he := congrArg e'.hom hn
  simpa only [map_nsmul, map_zero, Iso.inv_hom_id_apply] using he

private theorem abComparisonForgetPreservesKan (X : Scheme.{u}) :
    (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (Scheme.toProEt X).op := by
  intro P
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
      (forget AddCommGrpCat.{u + 1}) P (Scheme.toProEt X).op V := by
    intro V
    infer_instance
  infer_instance

private noncomputable def abComparisonForgetIso (X : Scheme.{u}) :
    comparisonUpperStar AddCommGrpCat.{u + 1} X ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1}) ⋙
        Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X) := by
  let := abComparisonForgetPreservesKan X
  exact sheafPullbackForgetIso X.smallEtaleTopology (Scheme.ProEt.topology X)
    (Scheme.toProEt X) (forget AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem abComparisonForgetIso_counit (X : Scheme.{u})
    (G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    (abComparisonForgetIso X).inv.app
        ((comparisonLowerStar AddCommGrpCat.{u + 1} X).obj G) ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).map
        ((comparisonAdjunction AddCommGrpCat.{u + 1} X).counit.app G) =
      (Scheme.proEtaleSiteComparison X).counit.app
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget AddCommGrpCat.{u + 1})).obj G) := by
  let := abComparisonForgetPreservesKan X
  let M := AddCommGrpCat.{u + 1}
  let V := sheafCompose X.smallEtaleTopology (forget M)
  let W := sheafCompose (Scheme.ProEt.topology X) (forget M)
  let R := comparisonLowerStar M X
  let Rs := (Scheme.toProEt X).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology (Scheme.ProEt.topology X)
  let adj := comparisonAdjunction M X
  let adjs := Scheme.proEtaleSiteComparison X
  let e := abComparisonForgetIso X
  have hu := sheafPullbackForgetIso_unit X.smallEtaleTopology
    (Scheme.ProEt.topology X) (Scheme.toProEt X) (forget M) (R.obj G)
  change V.map (adj.unit.app (R.obj G)) ≫ Rs.map (e.hom.app (R.obj G)) =
    adjs.unit.app (V.obj (R.obj G)) at hu
  have hu' : adjs.unit.app (V.obj (R.obj G)) ≫ Rs.map (e.inv.app (R.obj G)) =
      V.map (adj.unit.app (R.obj G)) := by
    rw [← hu, Category.assoc, ← Rs.map_comp, e.hom_inv_id_app, Rs.map_id]
    exact Category.comp_id _
  apply (adjs.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hu']
  change V.map (adj.unit.app (R.obj G)) ≫ V.map (R.map (adj.counit.app G)) = _
  rw [← V.map_comp, adj.right_triangle_components]
  exact (V.map_id _).trans (adjs.right_triangle_components (W.obj G)).symm

/-- The classicality predicate on an abelian pro-étale sheaf, obtained from the underlying
set-valued sheaf and the canonical affine-presentation continuity maps
(blueprint: `definition-classical-pro-etale-sheaves`, `det-pe-classical-definition-continuity-map`).
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
def IsClassicalAbelian {X : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) : Prop :=
  ProEtale.IsClassical
    ((sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).obj F)

private theorem classical_iff_counit (X : Scheme.{u})
    (G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :
    IsClassicalAbelian G ↔
      IsIso ((comparisonAdjunction AddCommGrpCat.{u + 1} X).counit.app G) := by
  change IsClassical _ ↔ _
  rw [(Scheme.proEtaleClassicalSheavesImage X _).2]
  rw [← abComparisonForgetIso_counit X G, isIso_comp_left_iff]
  exact isIso_iff_of_reflects_iso _
    (sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}))

/-- The nonvanishing predicate for pro-étale cohomology in degree `q`.
Source: blueprint `definition-cohomological-dimension`, first displayed supremum and
derived-notation paragraph (blueprint: definition-cohomological-dimension). -/
def IsNonzeroProEtaleCohomology {X : Scheme.{u}} (F :
    Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) : Prop :=
  ¬ IsZero
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((ProEtale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- The nonvanishing predicate for the `q`th higher direct image on the small pro-étale sites.
Source: blueprint `definition-cohomological-dimension`, second displayed supremum and
derived-notation paragraph (blueprint: definition-cohomological-dimension). -/
def IsNonzeroProEtaleHigherDirectImage {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) : Prop :=
  ¬ IsZero
      ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- The `ℓ`-cohomological dimension of a scheme, as a supremum in `WithTop ℕ`; the
supremum of the empty set is `0`. For a field `K`, `cd_ℓ(K)` denotes this expression
at `Spec (.of K)`.
Source: blueprint `definition-cohomological-dimension`, first displayed supremum and field notation
(blueprint: definition-cohomological-dimension). -/
noncomputable def cohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] : WithTop ℕ :=
  sSup {q : WithTop ℕ |
    ∃ n : ℕ, q = n ∧ ∃ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1},
      IsClassicalAbelian F ∧ IsEllPowerTorsion ℓ hℓ F ∧ IsNonzeroProEtaleCohomology F n}

/-- The relative `ℓ`-cohomological dimension of a morphism of schemes, as a supremum in
`WithTop ℕ`; the supremum of the empty set is `0`.
Source: blueprint `definition-cohomological-dimension`, second displayed supremum (blueprint:
definition-cohomological-dimension). -/
noncomputable def relativeCohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] : WithTop ℕ :=
  sSup {q : WithTop ℕ |
    ∃ n : ℕ, q = n ∧ ∃ F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1},
      IsClassicalAbelian F ∧ IsEllPowerTorsion ℓ hℓ F ∧
        IsNonzeroProEtaleHigherDirectImage g F n}

/-- The corresponding étale cohomological dimension, used in the comparison clause.
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
noncomputable def etaleCohomologicalDimension (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] : WithTop ℕ :=
  sSup {q : WithTop ℕ |
    ∃ n : ℕ, q = n ∧ ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsEllPowerTorsion ℓ hℓ F ∧
        ¬ IsZero ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} X (n : ℤ)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))}

private noncomputable def abComparisonCohomologyIso (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).obj
        ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)) := by
  let L := comparisonUpperStar AddCommGrpCat.{u + 1} X
  let R := comparisonLowerStar AddCommGrpCat.{u + 1} X
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} X
  let M := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  have := isIso_comparisonAdjunction_unit AddCommGrpCat.{u + 1} X
  have := adj.isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance)
    (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective
      AddCommGrpCat.{u + 1} X I) M
  exact (Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).mapIso
      ((DerivedCategory.Plus.ι.mapIso (asIso (adj.derivedPlus.unit.app M))) ≪≫
        R.rightDerivedFunctorPlusCompatibility.app (L.mapDerivedCategoryPlus.obj M)) ≪≫
    (comparisonLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{u + 1} X).app
      (L.mapDerivedCategoryPlus.obj M).obj ≪≫
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).mapIso
      (L.mapDerivedCategoryPlusCompatibility.app M ≪≫
        (L.mapDerivedCategorySingleFunctor 0).app F)

/-- Pro-étale and étale cohomology give the same `ℓ`-cohomological dimension for a qcqs
scheme.
Proof: `theorem-classical-sheaves-essential-image--1` gives the exact equivalence of étale sheaves
with classical pro-étale sheaves. Exactness preserves annihilator kernels, and the
left adjoint preserves the filtered colimit and its canonical map. Thus it preserves
and reflects local prime-power torsion. `theorem-bounded-below-cohomology-comparison` identifies
cohomology in every nonnegative degree. The sets of degrees in the two suprema agree.
The comparison is via the exact classical-sheaf comparison functor
(blueprint: `definition-cohomological-dimension`; Stacks, Tags 099V and 099W).
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
theorem cohomologicalDimension_eq_etaleCohomologicalDimension
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] :
    cohomologicalDimension ℓ hℓ X = etaleCohomologicalDimension ℓ hℓ X := by
  let L := comparisonUpperStar AddCommGrpCat.{u + 1} X
  let R := comparisonLowerStar AddCommGrpCat.{u + 1} X
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} X
  have ht (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ellPowerTorsion_exact_iff L ℓ hℓ F
  have hn (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
      IsNonzeroProEtaleCohomology (L.obj F) n ↔
        ¬ IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} X (n : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) := by
    let e := (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      (abComparisonCohomologyIso X F)
    exact ⟨fun h hz ↦ h (hz.of_iso e.symm), fun h hz ↦ h (hz.of_iso e)⟩
  apply congrArg sSup
  ext q
  constructor
  · rintro ⟨n, rfl, F, hFc, hFt, hFn⟩
    have hi := (classical_iff_counit X F).mp hFc
    let e : L.obj (R.obj F) ≅ F := asIso (adj.counit.app F)
    refine ⟨n, rfl, R.obj F, (ht _).mpr ?_, (hn _ n).mp ?_⟩
    · exact (ellPowerTorsion_iso_iff (Scheme.ProEt.topology X) ℓ hℓ e).mpr hFt
    · intro hz
      apply hFn
      exact hz.of_iso
        ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
          ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).mapIso
            ((DerivedCategory.singleFunctor _ 0).mapIso e))).symm
  · rintro ⟨n, rfl, F, hFt, hFn⟩
    refine ⟨n, rfl, L.obj F, ?_, (ht F).mp hFt, (hn F n).mpr hFn⟩
    apply (classical_iff_counit X _).mpr
    exact adj.isIso_counit_app_iff_mem_essImage.mpr ⟨F, ⟨Iso.refl _⟩⟩

private theorem abComparisonHigherImageIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Nonempty ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj
        ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (DerivedCategory.homologyFunctor _ (n : ℤ)).obj
        ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F)))) := by
  let LX := comparisonUpperStar AddCommGrpCat.{u + 1} X
  let LY := comparisonUpperStar AddCommGrpCat.{u + 1} Y
  let E := Etale.lowerStar AddCommGrpCat.{u + 1} g
  let P := ProEtale.lowerStar AddCommGrpCat.{u + 1} g
  let M := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  obtain ⟨e⟩ := nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar
    AddCommGrpCat.{u + 1} g
  exact ⟨LY.mapIso ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      (E.rightDerivedFunctorPlusCompatibility.app M).symm) ≪≫
    (LY.mapDerivedCategoryPlusHomologyFunctorIso (n : ℤ)).app
      (E.rightDerivedFunctorPlus.obj M) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).mapIso (e.app M) ≪≫
    (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
      (P.rightDerivedFunctorPlusCompatibility.app (LX.mapDerivedCategoryPlus.obj M) ≪≫
        P.rightDerivedFunctor.mapIso (LX.mapDerivedCategoryPlusCompatibility.app M ≪≫
          (LX.mapDerivedCategorySingleFunctor 0).app F))⟩

/-- The relative pro-étale/étale comparison for a qcqs morphism.
Proof: the exact classical-sheaf equivalence preserves and reflects the annihilator
colimit condition. `theorem-comparison-direct-images` identifies each higher direct
image with the exact fully faithful comparison of the étale higher direct image.
Full faithfulness reflects zero objects, so both sets of nonvanishing degrees agree.
Source: blueprint `definition-cohomological-dimension`, displayed definitions and local torsion
convention (blueprint: definition-cohomological-dimension). -/
theorem relativeCohomologicalDimension_eq_etale
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g] :
    relativeCohomologicalDimension ℓ hℓ g =
      sSup {q : WithTop ℕ |
        ∃ n : ℕ, q = n ∧ ∃ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
          IsEllPowerTorsion ℓ hℓ F ∧
            ¬ IsZero
              ((_root_.DerivedCategory.homologyFunctor _ (n : ℤ)).obj
                ((AlgebraicGeometry.Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
                  ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))} := by
  let LX := comparisonUpperStar AddCommGrpCat.{u + 1} X
  let LY := comparisonUpperStar AddCommGrpCat.{u + 1} Y
  let R := comparisonLowerStar AddCommGrpCat.{u + 1} X
  let adj := comparisonAdjunction AddCommGrpCat.{u + 1} X
  have ht (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ellPowerTorsion_exact_iff LX ℓ hℓ F
  have hn (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
      IsNonzeroProEtaleHigherDirectImage g (LX.obj F) n ↔
        ¬ IsZero ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj
          ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) := by
    obtain ⟨e⟩ := abComparisonHigherImageIso g F n
    constructor
    · intro h hz
      exact h ((LY.map_isZero hz).of_iso e.symm)
    · intro h hz
      apply h
      rw [IsZero.iff_id_eq_zero]
      apply LY.map_injective
      rw [LY.map_id, LY.map_zero]
      exact (hz.of_iso e).eq_of_src _ _
  apply congrArg sSup
  ext q
  constructor
  · rintro ⟨n, rfl, F, hFc, hFt, hFn⟩
    have hi := (classical_iff_counit X F).mp hFc
    let e : LX.obj (R.obj F) ≅ F := asIso (adj.counit.app F)
    refine ⟨n, rfl, R.obj F, (ht _).mpr ?_, (hn _ n).mp ?_⟩
    · exact (ellPowerTorsion_iso_iff (Scheme.ProEt.topology X) ℓ hℓ e).mpr hFt
    · intro hz
      apply hFn
      exact hz.of_iso
        ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
          ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.mapIso
            ((DerivedCategory.singleFunctor _ 0).mapIso e))).symm
  · rintro ⟨n, rfl, F, hFt, hFn⟩
    refine ⟨n, rfl, LX.obj F, ?_, (ht F).mp hFt, (hn F n).mpr hFn⟩
    apply (classical_iff_counit X _).mpr
    exact adj.isIso_counit_app_iff_mem_essImage.mpr ⟨F, ⟨Iso.refl _⟩⟩

/-- Over a field of finite `ℓ`-cohomological dimension, a finite-type morphism between
finite-type schemes over that field has finite relative dimension.
Source: blueprint `definition-cohomological-dimension`, final sentence; Stacks Tag 0F10 (blueprint:
definition-cohomological-dimension). Proof: finite-type schemes over a field are Noetherian, hence
qcqs; every morphism from such a source is qcqs, since inverse images of affine opens, also for its
diagonal, are quasi-compact opens of a Noetherian scheme. A locally prime-power torsion sheaf
is torsion by the local-section criterion of `definition-torsion-sheaves--3`.
Apply `theorem-results-from-etale-theory--6` to the underlying étale torsion sheaves and
use the relative comparison (`theorem-comparison-direct-images`) to transport its
uniform vanishing bound to classical prime-power torsion sheaves. -/
theorem relativeCohomologicalDimension_lt_top_of_finiteType
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {K : Type u} [Field K]
    (hK : cohomologicalDimension ℓ hℓ (Spec (.of K)) < ⊤)
    {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of K))]
    [LocallyOfFiniteType g] [QuasiCompact g] :
    @relativeCohomologicalDimension ℓ hℓ X Y g inferInstance
      (@QuasiSeparated.of_quasiSeparatedSpace X Y g
        (@IsLocallyNoetherian.quasiSeparatedSpace X
          (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))))) < ⊤ := by
  have _ := hK
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : QuasiSeparated g := inferInstance
  have hfin := (torsionEtaleCohomologicalDimension_finite_of_finiteType K X Y g).1
  obtain ⟨d, ⟨n, rfl, hn⟩, _⟩ := sInf_lt_iff.mp hfin
  rw [relativeCohomologicalDimension_eq_etale ℓ hℓ g]
  apply lt_of_le_of_lt (sSup_le ?_) (WithTop.coe_lt_top n)
  rintro q ⟨m, rfl, F, hF, hnonzero⟩
  by_contra hle
  have hnm : n < m := by simpa using (lt_of_not_ge hle)
  have hz := hn F (ellPowerTorsion_etale_isTorsion ℓ hℓ F hF)
    (m : ℤ) (by exact_mod_cast hnm)
  apply hnonzero
  exact hz.of_iso
    ((_root_.DerivedCategory.homologyFunctor _ (m : ℤ)).mapIso
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlusCompatibility.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F))).symm

/-- Over a field of finite `ℓ`-cohomological dimension, every finite-type scheme has
finite absolute dimension.
Source: blueprint `definition-cohomological-dimension`, final sentence; Stacks Tag 0F10 (blueprint:
definition-cohomological-dimension). Proof: use `theorem-results-from-etale-theory--6` for a
relative bound e on the structure morphism. The field hypothesis and the comparison give an absolute
bound c for prime-power torsion sheaves on the field. By `lem-sbc-qcqs-higher-images-prime-torsion`,
all higher direct images are again locally prime-power torsion, using exact conservative geometric
stalks and filtered colimits to identify this with the kernel-colimit convention. Apply
`lem-sc-leray-vanishing-bound` to obtain the bound c + e, then use the absolute
comparison. Finite type over a field gives a Noetherian source, so the scheme and
its structure morphism are qcqs, as in the relative finiteness proof.
Empty schemes satisfy the same bound. -/
theorem cohomologicalDimension_lt_top_of_finiteType
    (ℓ : ℕ) (hℓ : Nat.Prime ℓ) {K : Type u} [Field K]
    (hK : cohomologicalDimension ℓ hℓ (Spec (.of K)) < ⊤)
    {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    @cohomologicalDimension ℓ hℓ X
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K)))
      (@IsLocallyNoetherian.quasiSeparatedSpace X
        (LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K)))) < ⊤ := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))
  have : QuasiSeparatedSpace X := inferInstance
  let s := X ↘ Spec (.of K)
  have : QuasiSeparated s := inferInstance
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hK)
  have hc' : etaleCohomologicalDimension ℓ hℓ (Spec (.of K)) = c := by
    rw [← cohomologicalDimension_eq_etaleCohomologicalDimension, ← hc]
    rfl
  have hbase (G : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (hG : IsEllPowerTorsion ℓ hℓ G) (p : ℕ) (hp : c < p) :
      Subsingleton (Sheaf.H G p) := by
    have hz : IsZero ((Etale.cohomology AddCommGrpCat.{u + 1}
        (Spec (.of K)) (p : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj G)) := by
      by_contra hn
      have hpc : (p : WithTop ℕ) ≤ etaleCohomologicalDimension ℓ hℓ (Spec (.of K)) :=
        le_sSup ⟨p, rfl, G, hG, hn⟩
      rw [hc'] at hpc
      exact (not_le_of_gt hp) (WithTop.coe_le_coe.mp hpc)
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso (Spec (.of K)) p
    have hz' := hz.of_iso (e.app G)
    exact (show Subsingleton ((Sheaf.functorH _ p).obj G) from
      AddCommGrpCat.isZero_iff_subsingleton.mp hz')
  have hfin := (torsionEtaleCohomologicalDimension_finite_of_finiteType
    K X (Spec (.of K)) s).1
  obtain ⟨d, ⟨e, rfl, he⟩, _⟩ := sInf_lt_iff.mp hfin
  rw [cohomologicalDimension_eq_etaleCohomologicalDimension]
  apply lt_of_le_of_lt (sSup_le ?_) (WithTop.coe_lt_top (c + e))
  rintro q ⟨n, rfl, F, hF, hn⟩
  by_contra hle
  have hcn : c + e < n := WithTop.coe_lt_coe.mp (lt_of_not_ge hle)
  have hH : Subsingleton (Sheaf.H F n) :=
    Etale.subsingleton_H_of_rightDerived_lowerStar s F
      (fun q hq ↦ (he F (ellPowerTorsion_etale_isTorsion ℓ hℓ F hF)
        (q : ℤ) (by exact_mod_cast hq)).of_iso
          ((Etale.lowerStar AddCommGrpCat.{u + 1} s)
            |>.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm)
      (fun p q hp ↦ hbase _ (ellPowerTorsion_higherDirectImage s ℓ hℓ F hF q) p hp) n hcn
  obtain ⟨eH⟩ := Scheme.nonempty_sheafH_extDerivedIso X n
  have hz : IsZero ((Sheaf.functorH X.smallEtaleTopology n).obj F) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr hH
  exact hn (hz.of_iso (eH.app F).symm)

end ProEtale

end AlgebraicGeometry
