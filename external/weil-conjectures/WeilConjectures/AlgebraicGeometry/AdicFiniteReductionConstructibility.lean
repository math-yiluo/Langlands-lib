/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.AdicGradedLayerConstructibility
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import all WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.AlgebraicGeometry.CoefficientSurjectiveRestrictionConstructible
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import all WeilConjectures.AlgebraicGeometry.NoetherianGlobalConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.ConstructibleSheaf.Refinement

/-! # Constructibility of the higher derived coefficient reductions

Source: Stacks Project, Tag 09BR, lemma-compare-truncations-constructible.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme

namespace AdicReductionConstructibility

-- The local-model Serre argument works for every Noetherian coefficient ring.
-- Keep the constant-ring equivalence and the actual refinement projections explicit.

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem finiteTypeIso {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [CommRing κ] [IsNoetherianRing κ]
    {F G : ringedSiteModules ((constantSheaf J RingCat.{w}).obj (RingCat.of κ))}
    (e : F ≅ G) (h : SheafOfModules.IsFiniteTypeLocallyConstant J κ F) :
    SheafOfModules.IsFiniteTypeLocallyConstant J κ G := by
  intro U
  obtain ⟨S, hS, hs⟩ := h U
  refine ⟨S, hS, fun V f hf ↦ ?_⟩
  obtain ⟨M, hM, ⟨i⟩⟩ := hs V f hf
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso e.symm ≪≫ i⟩⟩

private theorem finiteSerre {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (κ : Type w) [CommRing κ] [IsNoetherianRing κ] :
    (∀ (F G : Sheaf J (ModuleCat κ)) (f : F ⟶ G),
      IsCoefficientModelLocallyConstantFinite J κ F →
      IsCoefficientModelLocallyConstantFinite J κ G →
      IsCoefficientModelLocallyConstantFinite J κ (kernel f) ∧
      IsCoefficientModelLocallyConstantFinite J κ (cokernel f)) ∧
    (∀ S : ShortComplex (Sheaf J (ModuleCat κ)), S.ShortExact →
      IsCoefficientModelLocallyConstantFinite J κ S.X₁ →
      IsCoefficientModelLocallyConstantFinite J κ S.X₃ →
      IsCoefficientModelLocallyConstantFinite J κ S.X₂) := by
  obtain ⟨⟨e, he, hae, hai, _⟩, _⟩ := constant_ring_module_sheaves J κ
  let E := e.inverse
  have : E.Additive := hai
  have h (F : Sheaf J (ModuleCat κ)) :
      IsCoefficientModelLocallyConstantFinite J κ F ↔
        SheafOfModules.IsFiniteTypeLocallyConstant J κ (E.obj F) := by
    rw [← ProFiniteModels.fixedModels_constantRing]
    change ProFiniteModels.fixedModels J κ F ↔ _
    rw [← he]
    exact ⟨ProFiniteModels.fixedModels_of_iso J κ (e.counitIso.app F).symm,
      ProFiniteModels.fixedModels_of_iso J κ (e.counitIso.app F)⟩
  obtain ⟨hk, hx⟩ :=
    SheafOfModules.finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions J κ
  constructor
  · intro F G f hF hG
    obtain ⟨hK, hC⟩ := hk _ _ (E.map f) ((h F).mp hF) ((h G).mp hG)
    exact ⟨(h _).mpr (finiteTypeIso J κ
      (PreservesKernel.iso E f).symm hK),
      (h _).mpr (finiteTypeIso J κ
        (PreservesCokernel.iso E f).symm hC)⟩
  · intro S hS h₁ h₃
    exact (h _).mpr (hx (S.map E) (hS.map_of_exact E)
      ((h _).mp h₁) ((h _).mp h₃))

private instance pullbackExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [CommRing κ] [IsNoetherianRing κ] :
    PreservesFiniteLimits (coefficientProEtaleFixedModulePullback.{u, v} f κ) := by
  have := ProEtale.model_preserves.{u, v} f
  have : RepresentablyFlat (coefficientProEtaleModelBaseChange.{u, v} f) :=
    flat_of_preservesFiniteLimits _
  have : PreservesFiniteLimits
      ((coefficientProEtaleModelBaseChange.{u, v} f).op.lan :
        _ ⥤ _ ⥤ ModuleCat.{max v (u + 1)} κ) :=
    preservesFiniteLimits_op_lan_of_flat _
  dsimp only [coefficientProEtaleFixedModulePullback]
  infer_instance

private instance pullbackColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [CommRing κ] [IsNoetherianRing κ] :
    PreservesFiniteColimits (coefficientProEtaleFixedModulePullback.{u, v} f κ) := by
  have : (coefficientProEtaleFixedModulePullback.{u, v} f κ).IsLeftAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat.{max v (u + 1)} κ)
      _ _).isLeftAdjoint
  infer_instance

private instance pullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (κ : Type (max v (u + 1))) [CommRing κ] [IsNoetherianRing κ] :
    (coefficientProEtaleFixedModulePullback.{u, v} f κ).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem commonStrata (X : Scheme.{u}) [IsNoetherian X]
    (κ : Type (max v (u + 1))) [CommRing κ] [IsNoetherianRing κ]
    (F G : Mod (constant (coefficientProEtaleModelTopology.{u, v} X) κ))
    (hF : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ F)
    (hG : IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X κ G) :
    ∃ S : Stratification X, ∀ i : Fin S.n,
      IsCoefficientModelLocallyConstantFinite _ κ
        ((coefficientProEtaleFixedModulePullback (S.immersion i) κ).obj
          ((coefficientModelFixedScalars _ κ).obj F)) ∧
      IsCoefficientModelLocallyConstantFinite _ κ
        ((coefficientProEtaleFixedModulePullback (S.immersion i) κ).obj
          ((coefficientModelFixedScalars _ κ).obj G)) := by
  obtain ⟨S, _, hs⟩ := (proEtale_noetherian_global_constructibility X κ F).mp hF
  obtain ⟨T, _, ht⟩ := (proEtale_noetherian_global_constructibility X κ G).mp hG
  refine ⟨S.inter T, fun a ↦ ?_⟩
  let i := (finProdFinEquiv.symm a).1
  let j := (finProdFinEquiv.symm a).2
  have hF' := ProEtale.coefficientProEtale_finite_comp
    (pullback.fst (S.immersion i) (T.immersion j)) (S.immersion i) κ _
    ((finiteLocalModels_iff_presentation _ κ _).mpr (hs i))
  have hG' := ProEtale.coefficientProEtale_finite_comp
    (pullback.snd (S.immersion i) (T.immersion j)) (T.immersion j) κ _
    ((finiteLocalModels_iff_presentation _ κ _).mpr (ht j))
  rw [← pullback.condition] at hG'
  exact ⟨hF', hG'⟩

private theorem constructibleSerre (X : Scheme.{u}) [IsNoetherian X]
    (κ : Type (max v (u + 1))) [CommRing κ] [IsNoetherianRing κ] :
    (∀
    (F G : Mod (constant (coefficientProEtaleModelTopology.{u, v} X) κ)) (f : F ⟶ G),
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ F →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ G →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ (kernel f) ∧
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (constant (coefficientProEtaleModelTopology.{u, v} X) κ)),
      S.ShortExact →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ S.X₁ →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ S.X₃ →
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X κ S.X₂) := by
  let E := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} X) κ
  have : E.IsEquivalence := coefficientModelFixedScalars_isEquivalence _ κ
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  constructor
  · intro F G f hF hG
    obtain ⟨S, hs⟩ := commonStrata X κ F G hF hG
    constructor
    all_goals
      apply (proEtale_noetherian_global_constructibility X κ _).mpr
      refine ⟨S, S.isConstructible_stratum, fun i ↦ ?_⟩
      apply (finiteLocalModels_iff_presentation _ κ _).mp
      let L := E ⋙ coefficientProEtaleFixedModulePullback.{u, v} (S.immersion i) κ
      obtain ⟨hK, hC⟩ := (finiteSerre _ κ).1 _ _ (L.map f) (hs i).1 (hs i).2
      first
      | exact ProEtale.coefficientProEtale_finite_iso κ
          (PreservesKernel.iso L f).symm hK
      | exact ProEtale.coefficientProEtale_finite_iso κ
          (PreservesCokernel.iso L f).symm hC
  · intro S hS h₁ h₃
    obtain ⟨T, ht⟩ := commonStrata X κ S.X₁ S.X₃ h₁ h₃
    apply (proEtale_noetherian_global_constructibility X κ _).mpr
    refine ⟨T, T.isConstructible_stratum, fun i ↦ ?_⟩
    apply (finiteLocalModels_iff_presentation _ κ _).mp
    let L := E ⋙ coefficientProEtaleFixedModulePullback.{u, v} (T.immersion i) κ
    exact (finiteSerre _ κ).2 (S.map L) (hS.map_of_exact L) (ht i).1 (ht i).2

private theorem constructibleTriangle (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (T : Pretriangulated.Triangle (adicFiniteAmbient.{u, v} X A))
    (hT : T ∈ distTriang _)
    (h₁ : ∀ q : ℤ, IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
      ((coefficientModelCohomology _ q).obj T.obj₁))
    (h₃ : ∀ q : ℤ, IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
      ((coefficientModelCohomology _ q).obj T.obj₃)) :
    ∀ q : ℤ, IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
      ((coefficientModelCohomology _ q).obj T.obj₂) := by
  let R := constant (coefficientProEtaleModelTopology.{u, v} X) A
  let := HasDerivedCategory.standard (Mod R)
  let P : ObjectProperty (Mod R) :=
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X A
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    ProEtale.coefficientProEtale_constructible_of_iso X A e h⟩
  obtain ⟨hk, hx⟩ := constructibleSerre X A
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, h, hfg⟩
    exact P.prop_of_iso (h.conePointUniqueUpToIso (kernelIsKernel f)).symm
      (hk _ _ f hfg.1 hfg.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, h, hfg⟩
    exact P.prop_of_iso (h.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
      (hk _ _ f hfg.1 hfg.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun h h₁ h₃ ↦ hx _ h h₁ h₃⟩
  exact (DerivedCategory.homologyProperty P).ext_of_isTriangulatedClosed₂ T hT h₁ h₃

end AdicReductionConstructibility

/-- Constructibility propagates from the bounded residue reduction to every higher
coefficient reduction. This assertion concerns only cohomology sheaves; it supplies
neither a Tor bound nor an etale origin.

Source: Stacks Project, proetale.tex, Tag 09BR,
lemma-compare-truncations-constructible, with its exponent n shifted by one.
(auxiliary; not a blueprint node).

Proof: For r >= 1 use the short exact sequence
0 -> J^r/J^(r+1) -> A/J^(r+1) -> A/J^r -> 0. Tensoring it in the derived
category with N gives the coefficient-filtration distinguished triangle. The left
term is the restriction of scalars of
N_0 tensor^L over A/J with the constant module J^r/J^(r+1): derived associativity
identifies the two expressions, since J annihilates the graded piece. Noetherianity
makes this graded piece a finite, hence finitely presented, A/J-module. Its constant
sheaf is constructible and concentrated in degree zero. On each affine open,
refine the finitely many stratifications for the nonzero residue cohomology
sheaves to one finite stratification. Inverse image is exact and commutes with
derived tensor. On every stratum apply the bounded-above locally constant finite
type tensor theorem (Tag 094H) to the restricted residue complex and the constant
graded module. This shows that every layer cohomology is constructible. This is
the special case of Tag 09BQ used in Tag 09BR; it avoids the fixed truncation
cutoff printed in the proof of 09BQ, since the residue complex is already bounded.
Restriction of scalars through the surjective quotient maps preserves finite
presentation over the Noetherian quotient rings and keeps the same affine-local
strata and constant trivializations. The constructible weak Serre property
(Tag 09B5) and the long exact cohomology sequence therefore give the induction step
from reduction r to reduction r+1. The base r=1 is the hypothesis. The named
reductions are the same derived tensors by their K-flat computation and balancing
isomorphisms. This proves every degree at every level. If J is the unit ideal all
quotients vanish; if J is zero the reductions are unchanged. The argument also
allows the empty scheme and the zero ring. -/
theorem adicFiniteReduction_constructible_cohomology
    (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (hres : ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X
      (adicFiniteCoeff J 0) (adicFiniteReduction.{u, v} X J N 0)) :
    ∀ (n : ℕ) (q : ℤ),
      IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X
        (adicFiniteCoeff J n)
        ((coefficientModelCohomology _ q).obj (adicFiniteReduction.{u, v} X J N n)) := by
  intro n
  induction n with
  | zero => exact hres.1
  | succ n ih =>
    obtain ⟨f, g, δ, hT⟩ := adicFiniteGradedLayer_triangle.{u, v} X J N n
    apply AdicReductionConstructibility.constructibleTriangle X
      (adicFiniteCoeff J (n + 1)) (Pretriangulated.Triangle.mk f g δ) hT
    · exact adicFiniteGradedLayer_constructible.{u, v} X A J N hres n
    · intro q
      exact coefficientSurjectiveRestriction_constructible.{u, v} X
        (adicFiniteCoeff J (n + 1)) (adicFiniteCoeff J n)
        (adicFiniteFactor J (Nat.le_succ n))
        (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ _)))
        (adicFiniteReduction.{u, v} X J N n) q (ih q)

end AlgebraicGeometry.Scheme
