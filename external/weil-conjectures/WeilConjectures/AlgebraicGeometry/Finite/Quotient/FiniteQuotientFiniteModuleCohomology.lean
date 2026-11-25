/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalWeakSerre
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCohomologyFiltrationTriangle
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-! # Finite etale-local cohomology of the successor coefficient quotient

Source: Stacks Project, Tags 094I, 094H and 09C2
(blueprint: lem-weil-pbc-finite-quotient-finite-module-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

-- Retain the published named chart-map binder in the conclusion.
set_option linter.unusedVariables false in
/-- The successor quotient has bounded finite etale-local cohomology. This
statement constructs only local models of individual cohomology sheaves, not a
complex model or any differentials.

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I) and
lemma-locally-constant-tensor (094H); proetale.tex,
lemma-describe-constructible-complexes (09C2).
(blueprint: lem-weil-pbc-finite-quotient-finite-module-cohomology).

Proof: intersect the residue and previous-level etale covers and restrict the
specified derived isomorphisms to this common refinement. Resolve M by a flat-term
K-flat complex. Tensor the short exact coefficient sequence with terms
I^(n+1)/I^(n+2), A/I^(n+2), and A/I^(n+1). Flatness gives a short exact sequence
of complexes. Balancing and the two coefficient compatibility squares identify
its kernel with the perfect residue model tensored over A/I with the first,
finite A/I-module, and identify the other two terms with the specified actual
successor and previous reductions. The residue model is termwise projective, so
this ordinary tensor computes derived tensor and is zero outside [a,b]. Its
cohomology modules are finite, since the coefficient ring is finite Noetherian.
The previous perfect model has the same bounded finite cohomology property.
The long exact cohomology sequence gives vanishing for the middle term outside
[a,b]. Kernels, cokernels and extensions of finite locally constant coefficient
modules are finite locally constant. For etale locality, finite constant module
sheaves descend along the finite-coefficient etale/pro-etale comparison; exact
comparison and its bounded-below full faithfulness preserve these kernels,
cokernels and extension classes. Thus each middle cohomology sheaf is etale
locally constant with finite module values. Exact slice restriction and
composition of the covering refinements give the asserted descriptions on every
chart over V. Coefficient identification by φ supplies exactly the displayed
module realizations. Empty charts have zero cohomology, with zero module value;
for a zero quotient ring every term is zero. -/
theorem finiteQuotient_finiteModule_cohomology_succ
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b) (n : ℕ)
    (hprevious : FinitePerfectModelsOn X d φ M n V a b) :
    let B := A ⧸ d.ideal ^ (n + 1 + 1)
    let R₀ := completedAdicFiniteRing X d (n + 1)
    let K := (completedAdicQuotientReduction X d (n + 1)).obj M
    (∀ q : ℤ, q < a ∨ b < q → IsZero
        ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)).obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) ∧
      ∀ (q : ℤ) (W : X.Etale) (g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((DerivedCategory.homologyFunctor _ q).obj K) ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ (n + 1))).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                  ModuleCat.restrictScalars.{t + 1}
                    (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                  koszulConstantFunctor X B).obj N))) := by
  let B := A ⧸ d.ideal ^ (n + 1 + 1)
  let R₀ := completedAdicFiniteRing X d (n + 1)
  let K := (completedAdicQuotientReduction X d (n + 1)).obj M
  let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
    ∀ (W : X.Etale) (_g : W ⟶ V),
      ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
        ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
          ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
            ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
              (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                ((completedAdicChange X (φ (n + 1))).obj
                  ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                    ModuleCat.restrictScalars.{t + 1}
                      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                    koszulConstantFunctor X B).obj N)))
  let F := SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj V)
  change (∀ q : ℤ, q < a ∨ b < q →
      IsZero (F.obj ((DerivedCategory.homologyFunctor _ q).obj K))) ∧
    ∀ q : ℤ, P ((DerivedCategory.homologyFunctor _ q).obj K)
  obtain ⟨T, hT, ⟨e⟩, hvan, h₁, h₃⟩ :=
    finiteQuotient_cohomology_filtration_triangle
      X d φ hφ hcompat M V a b hab hresidue n hprevious
  have : F.Additive := (ringedOverFunctor_exactGeneral R₀ ((toProEt X).obj V)).1
  have : PreservesFiniteLimits F :=
    (ringedOverFunctor_exactGeneral R₀ ((toProEt X).obj V)).2.1
  have : PreservesFiniteColimits F :=
    (ringedOverFunctor_exactGeneral R₀ ((toProEt X).obj V)).2.2
  constructor
  · intro q hq
    obtain ⟨hz₁, hz₃⟩ := hvan q hq
    have hseq := (DerivedCategory.HomologySequence.exact₂ T hT q).map F
    have hz₂ := hseq.isZero_of_both_isZero hz₁ hz₃
    exact hz₂.of_iso (F.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso e)).symm
  · have : Finite B := d.quotientFinite (n + 1)
    obtain ⟨hker, hcoker, hext⟩ := finiteCoefficient_etaleLocal_weakSerre X B
      (completedAdicFiniteCommRing X d (n + 1)) (φ (n + 1)) (hφ (n + 1)) V
    have : P.IsClosedUnderKernels := hker
    have : P.IsClosedUnderCokernels := hcoker
    have : P.IsClosedUnderExtensions := hext
    have : P.IsClosedUnderIsomorphisms := by
      constructor
      intro L N i h W g
      obtain ⟨S, hS, hs⟩ := h W g
      refine ⟨S, hS, fun Z f hf ↦ ?_⟩
      obtain ⟨N₀, hN₀, ⟨j⟩⟩ := hs Z f hf
      exact ⟨N₀, hN₀, ⟨(SheafOfModules.overFunctor.{t + 1} R₀
        ((toProEt X).obj Z)).mapIso i.symm ≪≫ j⟩⟩
    have h₂ := (DerivedCategory.homologyProperty P).ext_of_isTriangulatedClosed₂
      T hT h₁ h₃
    intro q
    exact P.prop_of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e) (h₂ q)

end AlgebraicGeometry.Scheme
