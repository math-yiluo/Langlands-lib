/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesDefinitions
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductions
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsIntegralFiniteModelCompleteness
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralContinuousEncodingConstructible
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelsCommonStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelStrataGeneration
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Nonfinite-coefficient compactness from finite base cohomological dimension

This is the nonfinite-coefficient compactness input needed by the corrected Brown theorem.
The adopted source currently records the corresponding compactness declarations over finite
or separably closed fields; this theorem isolates the finite-cd extension.
(blueprint: lem-sfb-brown-finite-cd-integral-ext)
-/

@[expose] public section

set_option autoImplicit false

attribute [-instance] WeilConjectures.strictDvrSiteSmall
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace CategoryTheory

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

section

-- Use the same coefficient-point tensor instance as the finite-reduction theorem.
private noncomputable abbrev nativeCondensedMonoidal :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall Ab
    (coherentTopology Profinite.{u})

attribute [local instance 40000] nativeCondensedMonoidal

private theorem hom_shift_product_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (r : ℤ) (h : ∀ n, Subsingleton (Q ⟶ (K n) ⟦r⟧))
    (f : Q ⟶ (∏ᶜ K) ⟦r⟧) : f = 0 := by
  apply (isLimitOfPreserves (shiftFunctor (DerivedCategory C) r)
    (productIsProduct K)).hom_ext
  intro n
  exact (h n.as).elim _ _

/-- Vanishing in two adjacent degrees propagates from the levels to their Roos limit.
Source: the final paragraph of the integral Ext-bound proof and Stacks Tag 0149. -/
private theorem hom_roos_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (Q N : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (step : ∀ n, K (n + 1) ⟶ K n)
    (pN : N ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ N⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle step N pN δ) (q : ℤ)
    (hprev : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q - 1⟧))
    (hnext : ∀ n, Subsingleton (Q ⟶ (K n) ⟦q⟧)) :
    Subsingleton (Q ⟶ N⟦q⟧) := by
  let T := CategoryTheory.Pretriangulated.Triangle.mk pN (towerTransitionEndomorphism step) δ
  have hT' : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles
      (C := DerivedCategory C) := hT
  let U := (shiftFunctor (CategoryTheory.Pretriangulated.Triangle (DerivedCategory C))
    (q - 1)).obj T
  have hU : U ∈ CategoryTheory.Pretriangulated.distinguishedTriangles (C := DerivedCategory C) :=
    CategoryTheory.Pretriangulated.Triangle.shift_distinguished T hT' (q - 1)
  let e := (shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app N
  have hz (f : Q ⟶ N⟦q⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₁ U hU
      (f ≫ e.hom) (by
        apply (cancel_mono
          ((shiftFunctorAdd' (DerivedCategory C) (q - 1) 1 q (by omega)).app (∏ᶜ K)).inv).1
        rw [zero_comp]
        exact hom_shift_product_zero Q K q hnext _)
    have hg0 : g = 0 := hom_shift_product_zero Q K (q - 1) hprev g
    apply (cancel_mono e.hom).1
    simpa only [hg0, zero_comp] using hg
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

private theorem subsingleton_of_all_eq {α : Sort*} (z : α) (h : ∀ x, x = z) :
    Subsingleton α :=
  ⟨fun x y ↦ (h x).trans (h y).symm⟩

private def UniformHomBound {C : Type*} [Category C] [HasShift C ℤ]
    (P : C → Prop) (A : C) : Prop :=
  ∃ d : ℕ, ∀ N, P N → ∀ r : ℤ, (d : ℤ) < r → Subsingleton (A ⟶ N⟦r⟧)

private theorem uniformHomBound_iso
    {C : Type*} [Category C] [HasShift C ℤ] (P : C → Prop)
    {A B : C} (e : A ≅ B) (h : UniformHomBound P A) : UniformHomBound P B := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun N hN r hr ↦ ⟨fun f g ↦ ?_⟩⟩
  apply (cancel_epi e.hom).1
  exact (hd N hN r hr).elim _ _

private theorem uniformHomBound_zero
    {C : Type*} [Category C] [HasShift C ℤ] [HasZeroMorphisms C]
    (P : C → Prop) {A : C} (h : IsZero A) : UniformHomBound P A := by
  exact ⟨0, fun _ _ _ _ ↦ ⟨fun f g ↦ h.eq_of_src f g⟩⟩

private theorem uniformHomBound_extension
    {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : C → Prop) (T : Pretriangulated.Triangle C)
    (hT : T ∈ Pretriangulated.distinguishedTriangles)
    (h₁ : UniformHomBound P T.obj₁) (h₃ : UniformHomBound P T.obj₃) :
    UniformHomBound P T.obj₂ := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₃, hd₃⟩ := h₃
  refine ⟨max d₁ d₃, fun N hN r hr ↦ ?_⟩
  have h₁ := hd₁ N hN r (lt_of_le_of_lt (by exact_mod_cast le_max_left d₁ d₃) hr)
  have h₃ := hd₃ N hN r (lt_of_le_of_lt (by exact_mod_cast le_max_right d₁ d₃) hr)
  have hz (f : T.obj₂ ⟶ N⟦r⟧) : f = 0 := by
    obtain ⟨g, hg⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁.elim _ _)
    rw [hg, h₃.elim g 0, comp_zero]
  exact ⟨fun f g ↦ (hz f).trans (hz g).symm⟩

private def reductionBound
    (X Z S : Scheme.{u}) (i : Z ⟶ X) (v : S ⟶ Z) [IsOpenImmersion v]
    (r : ℤ)
    (a : Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))) : Prop :=
  match a with
  | ⟨@CommMon.mk _ _ _ _ Λ mΛ cΛ, @CommMon.mk _ _ _ _ Γ mΓ cΓ,
      ⟨@Mon.Hom.mk _ _ _ _ _ φ hφ⟩⟩ =>
    letI := mΛ
    letI := mΓ
    letI := cΛ
    letI := cΓ
    let φ' : Λ ⟶ Γ := φ
    letI : IsMonHom φ' := hφ
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
    letI : IsCommMonObj (condensedRingObj Λ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    letI : IsCommMonObj (condensedRingObj Γ X) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X)
    ∀ (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj Λ S)), HasFiniteConstantLocalModel Λ S L →
    ∀ (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)), IsConstantModelConstructible Λ X N →
    ∀ f : (DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ i).obj
          ((CondensedRing.openImmersionLowerShriek Λ v).obj L)) ⟶
        ((Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap (Λ := Λ) (Λ' := Γ) φ' X)).mapDerivedCategory.obj
          ((Mod.extendScalars (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (coefficientMap (Λ := Λ) (Λ' := Γ) φ' X)).leftDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj N)))⟦r⟧, f = 0

private noncomputable def coefficientArrow
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :=
  Arrow.mk (CommMon.homMk (A := CommMon.mk R) (B := CommMon.mk S) (Mon.ofHom f))

private noncomputable def continuousArrow
    (A B : Type u) [CommRing A] [CommRing B]
    (tA : TopologicalSpace A) (tB : TopologicalSpace B)
    (hA : @IsTopologicalRing A tA _) (hB : @IsTopologicalRing B tB _)
    (f : A →+* B) (hf : @Continuous A B tA tB f) :
    Arrow (CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) :=
  letI := tA
  letI := tB
  letI := hA
  letI := hB
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Sheaf.monObj_sheafCompose_obj _ (Profinite.continuousMapRingSheafOfUniverse A)
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} B) :=
    Sheaf.monObj_sheafCompose_obj _ (Profinite.continuousMapRingSheafOfUniverse B)
  letI : IsCommMonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Profinite.isCommMonObj_continuousMapRingObjOfUniverse A
  letI : IsCommMonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} B) :=
    Profinite.isCommMonObj_continuousMapRingObjOfUniverse B
  letI : IsMonHom (Profinite.continuousMapRingObjMapOfUniverse.{u, u} f hf) :=
    Sheaf.isMonHom_sheafCompose_map _ (Profinite.continuousMapRingSheafMapOfUniverse f hf)
  coefficientArrow (Profinite.continuousMapRingObjMapOfUniverse f hf)
private theorem continuousArrow_eq
    (A B : Type u) [CommRing A] [CommRing B]
    (tA tA' : TopologicalSpace A) (tB tB' : TopologicalSpace B)
    (ha : tA = tA') (hb : tB = tB')
    (hA : @IsTopologicalRing A tA _) (hA' : @IsTopologicalRing A tA' _)
    (hB : @IsTopologicalRing B tB _) (hB' : @IsTopologicalRing B tB' _)
    (f : A →+* B) (hf : @Continuous A B tA tB f)
    (hf' : @Continuous A B tA' tB' f) :
    continuousArrow A B tA tB hA hB f hf =
      continuousArrow A B tA' tB' hA' hB' f hf' := by
  subst tA'
  subst tB'
  rfl
private theorem reductionArrow_eq
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    coefficientArrow (IntegralQuotient.reduction l E n) =
      coefficientArrow (DerivedNakayama.reductionRing l E (n + 1)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have ht := DerivedNakayama.coefficientTopology l E
  have hi := congrArg (fun t : TopologicalSpace E ↦
    TopologicalSpace.induced
      (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)) t) ht
  have hd : AdicCompletion.finiteTopology l E (n + 1) = ⊥ :=
    @DiscreteTopology.eq_bot _ _ (DerivedNakayama.quotientDiscrete l E (n + 1))
  exact continuousArrow_eq _ _ _ _ _ _ hi hd.symm
    (by let := spectralNorm.normedField (Padic l) E; infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance)
    _ (IntegralQuotient.reduction_continuous l E n) continuous_quot_mk

-- Kernel checking unfolds both scalar-change functors in the coefficient-arrow transport.
private theorem finite_reduction_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower (Padic l) E (PadicAlgCl l)]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [CompactSpace S] [QuasiSeparatedSpace S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c s : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (n : ℕ) (r : ℤ) (hr : (c : ℤ) + (s : ℤ) + 2 < r) :
    reductionBound X Z S i v r (coefficientArrow (DerivedNakayama.reductionRing l E (n + 1))) := by
  have hb : reductionBound X Z S i v r
      (coefficientArrow (IntegralQuotient.reduction l E n)) := by
    intro L hL N hN f
    exact integralStratumFiniteCdReductions l E X Z S V hl i v j hcomp
      L hL c s hc hs N hN n r hr f
  exact (congrArg (reductionBound X Z S i v r) (reductionArrow_eq l E n)).mp hb

attribute [local instance 40000] AdicCompletion.ringMonoidalObject
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.modulesDerived
  AdicCompletion.finiteModulesDerived AdicCompletion.modulesMonoidal

-- Compare the finite-bound presentation with the native completion-level API once.
private theorem completion_reduction_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower (Padic l) E (PadicAlgCl l)]
    (X Z S V : Scheme.{u}) [IsNoetherian X] [CompactSpace S] [QuasiSeparatedSpace S]
    (hl : IsUnit (l : Γ(X, ⊤)))
    (i : Z ⟶ X) (v : S ⟶ Z) (j : V ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion v] [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range j.base = (Set.range i.base)ᶜ)
    (c s : ℕ)
    (hc : relativeCohomologicalDimension l (Fact.out : l.Prime) j ≤ c)
    (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (n : ℕ) (r : ℤ) (hr : (c : ℤ) + (s : ℤ) + 2 < r) :
    letI : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
    ∀ L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (condensedRingObj (DerivedNakayama.integerRing l E) S),
      HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) S L →
    ∀ N : AdicCompletion.Modules l E X,
      IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N →
    Subsingleton ((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) i).obj
          ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) v).obj L)) ⟶
        (AdicCompletion.integralLevel l E X
          ((DerivedCategory.singleFunctor _ 0).obj N) n)⟦r⟧) := by
  intro L hL N hN
  have hf := finite_reduction_bound l E X Z S V hl i v j hcomp c s hc hs n r hr
  exact subsingleton_of_all_eq _ (hf L hL N hN)

-- Transport uniqueness before specializing to the large scalar-change functor.
private theorem hom_subsingleton_of_faithful_iso
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Faithful] {X Y : C} {X' Y' : D}
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y') (h : Subsingleton (X' ⟶ Y')) :
    Subsingleton (X ⟶ Y) := by
  refine ⟨fun f g ↦ F.map_injective ?_⟩
  apply (cancel_epi a.inv).mp
  apply (cancel_mono b.hom).mp
  exact h.elim _ _

private theorem hom_roos_iso_zero
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (A N Q : DerivedCategory C) (K : ℕ → DerivedCategory C) [HasProduct K]
    (step : ∀ n, K (n + 1) ⟶ K n)
    (p : Q ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ Q⟦(1 : ℤ)⟧)
    (htri : IsDerivedLimitTriangle step Q p δ) (e : N ≅ Q) (r : ℤ)
    (hprev : ∀ n, Subsingleton (A ⟶ K n⟦r - 1⟧))
    (hnext : ∀ n, Subsingleton (A ⟶ K n⟦r⟧)) :
    Subsingleton (A ⟶ N⟦r⟧) := by
  have hQ := hom_roos_zero A Q K step p δ htri r hprev hnext
  exact ⟨fun f g ↦ by
    apply (cancel_mono ((shiftFunctor _ r).mapIso e).hom).mp
    exact hQ.elim _ _⟩

-- Comparing the native Roos levels with the scalar-change bounds unfolds large functors.
private theorem model_uniform_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra E (PadicAlgCl l)] [IsScalarTower (Padic l) E (PadicAlgCl l)]
    {k : Type u} [Field k] [Fact (ringChar k ≠ l)]
    (hcd : cohomologicalDimension l (Fact.out : l.Prime) (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (M : AdicCompletion.Modules l E X)
    (hM : IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M) :
    ∃ d : ℕ, ∀ N : AdicCompletion.Modules l E X,
      IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N →
      ∀ r : ℤ, (d : ℤ) < r →
        Subsingleton ((DerivedCategory.singleFunctor _ 0).obj M ⟶
          ((DerivedCategory.singleFunctor _ 0).obj N)⟦r⟧) := by
  classical
  let : X.Over (Spec (.of k)) := ⟨aX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType aX)
  have : QuasiCompact (X ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact aX)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  have hl : IsUnit (l : Γ(X, ⊤)) := by
    have hn : (l : k) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime k
      (Fact.out : l.Prime) (Fact.out : ringChar k ≠ l)
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ aX.appTop).hom
  let P : DerivedCategory (AdicCompletion.Modules l E X) → Prop := fun K ↦
    ∃ N, IsConstantModelConstructible (DerivedNakayama.integerRing l E) X N ∧
      K = (DerivedCategory.singleFunctor _ 0).obj N
  let Q : ObjectProperty (DerivedCategory (AdicCompletion.Modules l E X)) :=
    UniformHomBound P
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ uniformHomBound_iso P e h⟩
  obtain ⟨R, _, ⟨Z, i, v, hi, hv, hr⟩, hmodels, _⟩ :=
    CondensedRing.finiteConstantModels_commonReducedStratification
      (DerivedNakayama.integerRing l E) X 1
      (fun _ ↦ M) (fun _ ↦ hM)
  have hQ : Q ((DerivedCategory.singleFunctor _ 0).obj M) := by
    apply CondensedRing.finiteConstantModel_fixedStrata_generation
      (DerivedNakayama.integerRing l E) X R Z i v hi hv hr Q
      (fun _ hz ↦ uniformHomBound_zero P hz)
      (fun T hT h₁ h₃ ↦ uniformHomBound_extension P T hT h₁ h₃) M
    intro a
    have : IsClosedImmersion (i a.castSucc) := (hi a.castSucc).1
    have : IsOpenImmersion (v a) := (hv a).1
    have : TopologicalSpace.NoetherianSpace (Z a.castSucc) :=
      (i a.castSucc).isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    have : TopologicalSpace.NoetherianSpace (R.domain a) :=
      (v a).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    let U : X.Opens := ⟨(Set.range (i a.castSucc))ᶜ,
      (i a.castSucc).isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have : TopologicalSpace.NoetherianSpace U.toScheme :=
      U.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    have : QuasiCompact U.ι := inferInstance
    have : QuasiCompact (v a) := inferInstance
    let : (Z a.castSucc).Over (Spec (.of k)) := ⟨i a.castSucc ≫ aX⟩
    let : (R.domain a).Over (Spec (.of k)) := ⟨v a ≫ i a.castSucc ≫ aX⟩
    let : U.toScheme.Over (Spec (.of k)) := ⟨U.ι ≫ aX⟩
    have : LocallyOfFiniteType ((Z a.castSucc) ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (i a.castSucc ≫ aX))
    have : QuasiCompact ((Z a.castSucc) ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (i a.castSucc ≫ aX))
    have : LocallyOfFiniteType ((R.domain a) ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (v a ≫ i a.castSucc ≫ aX))
    have : QuasiCompact ((R.domain a) ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (v a ≫ i a.castSucc ≫ aX))
    have : LocallyOfFiniteType (U.toScheme ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ aX))
    have : QuasiCompact (U.toScheme ↘ Spec (.of k)) :=
      inferInstanceAs (QuasiCompact (U.ι ≫ aX))
    have : U.ι.IsOver (Spec (.of k)) := ⟨rfl⟩
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp
      (ne_of_lt (relativeCohomologicalDimension_lt_top_of_finiteType l Fact.out hcd U.ι))
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
      (ne_of_lt (cohomologicalDimension_lt_top_of_finiteType l Fact.out hcd
        (X := R.domain a)))
    refine ⟨c + s + 3, ?_⟩
    rintro K ⟨N, hN, rfl⟩ r hdeg
    obtain ⟨B, hB, ⟨eB⟩, hη⟩ := complete_sheaf l E X N hN
    let := AdicCompletion.modules_countableAB4Star l E X
    let := derivedCategory_hasCountableProducts (AdicCompletion.Modules l E X)
    obtain ⟨p, δ, htri, _⟩ := AdicCompletion.roos_isDerivedLimit l E X
      ((DerivedCategory.singleFunctor _ 0).obj N) B hB eB
    have : IsIso (AdicCompletion.completionMap l E X
        ((DerivedCategory.singleFunctor _ 0).obj N) B eB) := by
      dsimp only [AdicCompletion.completionMap]
      infer_instance
    let e := asIso (AdicCompletion.completionMap l E X
      ((DerivedCategory.singleFunctor _ 0).obj N) B eB)
    apply hom_roos_iso_zero ((DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.lowerStar (DerivedNakayama.integerRing l E) (i a.castSucc)).obj
        ((CondensedRing.openImmersionLowerShriek (DerivedNakayama.integerRing l E) (v a)).obj
          ((CondensedRing.upperStar (DerivedNakayama.integerRing l E) (R.immersion a)).obj M))))
      ((DerivedCategory.singleFunctor _ 0).obj N)
      (DerivedCategory.Q.obj (AdicCompletion.roos l E X B))
      (AdicCompletion.integralLevel l E X ((DerivedCategory.singleFunctor _ 0).obj N))
      (AdicCompletion.integralStep l E X ((DerivedCategory.singleFunctor _ 0).obj N)) p δ htri e r
    · intro n
      have hf := completion_reduction_bound l E X (Z a.castSucc) (R.domain a) U.toScheme
        hl (i a.castSucc) (v a) U.ι (by exact U.range_ι) c s (le_of_eq hc.symm)
        (le_of_eq hs.symm) n (r - 1) (by push_cast at hdeg; omega)
      exact hf _ (hmodels 0 a) N hN
    · intro n
      have hf := completion_reduction_bound l E X (Z a.castSucc) (R.domain a) U.toScheme
        hl (i a.castSucc) (v a) U.ι (by exact U.range_ι) c s (le_of_eq hc.symm)
        (le_of_eq hs.symm) n r (by push_cast at hdeg; omega)
      exact hf _ (hmodels 0 a) N hN
  obtain ⟨d, hd⟩ := hQ
  exact ⟨d, fun N hN r hr ↦ hd _ ⟨N, hN, rfl⟩ r hr⟩

end

attribute [local instance 30000] brownHypothesesCondensedMonoidal
  brownHypothesesCondensedBraided brownHypothesesSheafMonoidal
  brownHypothesesSheafBraided brownHypothesesCoefficientMonObj
  brownHypothesesModuleMonoidalClosed
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

-- The derived coefficient equivalence compares large canonical single-functor constructions.
/-- Uniform Ext bounds for valuation-ring coefficients over a field of finite
ℓ-cohomological dimension.

Source: blueprint latest, `sk-lem-int-ext.proof.md`, bound paragraph, and
`sk-lem-brown-hypotheses.proof.md`, integral compactness.
(blueprint: lem-sfb-brown-finite-cd-integral-ext).

Proof: filter the first constructible sheaf by degree-zero extensions from finitely
many locally closed strata. On a stratum use a finite presentation of its coefficient
module. The finite reductions of the second sheaf are controlled by the closed-support
triangle and the finite absolute and relative ℓ-cohomological dimensions of the stratum
and boundary. Their bound is independent of the second sheaf and the reduction exponent.
Recover the integral target by its derived inverse system of reductions. The Milnor
triangle adds at most one to the bound; no immersion inverse image is commuted with
this inverse limit. Take a maximum over the finitely many pieces of the filtration
and apply Hom exactness along its triangles. The empty filtration gives the zero case.
The cohomological-dimension assumption supplies all bounds by Stacks 0F10. -/
theorem brownHypotheses_integral_uniformExtBound_of_finite_cd
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
    (hcd : cohomologicalDimension ℓ (Fact.out : ℓ.Prime) (Spec (.of k)) < ⊤)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      HasUniformConstructibleExtBound
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : IsNoetherian X := ⟨⟩
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} X.ProEt
  intro E
  let F := ULift.{u} E.val
  let : Algebra F (PadicAlgCl ℓ) :=
    (E.val.val.toRingHom.comp ULift.ringEquiv.toRingHom).toAlgebra
  let : IsScalarTower ℚ_[ℓ] F (PadicAlgCl ℓ) :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let eR := integerRingSheafIso.{u} ℓ ⟨E.val, E.property⟩
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom e.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap e.inv X)
  have : G.IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (coefficientMap e.inv X)).isEquivalence_functor
  have : G.mapDerivedCategory.IsEquivalence := Functor.isEquivalence_mapDerivedCategory G
  intro M hM
  have hMG := integral_internal_constant_models ℓ F X (G.obj M)
    (constructible_comap (coefficientMap e.inv X) hM)
  obtain ⟨d, hd⟩ := model_uniform_bound ℓ F hcd aX (G.obj M) hMG
  refine ⟨-(d : ℤ) - 1, ?_⟩
  intro N hN n hn f
  have hNG := integral_internal_constant_models ℓ F X (G.obj N)
    (constructible_comap (coefficientMap e.inv X) hN)
  let a := (G.mapDerivedCategorySingleFunctor 0).app M
  let b := (G.mapDerivedCategorySingleFunctor n).app N
  let c := ((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app (G.obj N)
  have hv := hd (G.obj N) hNG (-n) (by omega)
  exact (hom_subsingleton_of_faithful_iso G.mapDerivedCategory a (b ≪≫ c.symm) hv).elim f 0

end CategoryTheory
