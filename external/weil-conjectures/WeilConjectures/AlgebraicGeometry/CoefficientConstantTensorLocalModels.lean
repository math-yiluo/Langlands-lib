/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientRestrictedTensorFlatModel
import all WeilConjectures.AlgebraicGeometry.NilpotentReductionStep
import all WeilConjectures.AlgebraicGeometry.ProEtaleRestrictedTensorFiniteLocalConstancy

/-! # The local constant tensor calculation on coefficient-sized sites

Source: Stacks Project, sites-cohomology.tex, Tag 094H, and proetale.tex, Tag 09BQ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.ConstantCompletion
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

private theorem local_models_iff
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] (F : Mod (constant J A)) :
    SheafOfModules.IsLocallyConstantFiniteTypeModules J A F ↔
      IsCoefficientModelLocallyConstantFinite J A
        ((coefficientModelFixedScalars J A).obj F) := by
  exact small_models J A F

private theorem finite_constant_tensor
    {C : Type v} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
    (A : Type v) [CommRing A] [IsNoetherianRing A]
    (M : ModuleCat.{v} A) (hM : Module.Finite A M)
    (P : CochainComplex (Mod (constant J A)) ℤ)
    (hP : P.IsKFlatTensor)
    (hb : ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (P.X j))
    (hl : ∀ j : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules J A (P.homology j)) :
    let := SheafOfModules.monoidalCategory (constant J A)
    ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules J A
      ((((tensorLeft ((commutativeSiteConstantModuleFunctor J A).obj M)).mapHomologicalComplex
        (.up ℤ)).obj P).homology q) := by
  have hJ : J.toPrecoverage.toGrothendieck = J := by
    apply le_antisymm J.toGrothendieck_toPrecoverage_le
    intro U S hS
    simpa only [Sieve.generate_sieve] using
      J.toPrecoverage.generate_mem_toGrothendieck
        ((J.arrows_mem_toPrecoverage_iff S).mpr hS)
  revert P
  rw [← hJ]
  intro P hP hb hl
  let := HasDerivedCategory.standard (Mod (constant J.toPrecoverage.toGrothendieck A))
  exact SheafOfModules.finite_tensor_lisse J.toPrecoverage A M hM P hP hb hl

namespace AlgebraicGeometry.Scheme

/-- The local calculation after an arbitrary scheme restriction. The hypotheses concern
local systems on the whole source of `f`; no stratification or constructibility predicate
occurs. Only an upper bound on `K` is needed, and no bound below on the result is asserted.

Source: Stacks Project, sites-cohomology.tex, Tag 094H,
lemma-locally-constant-tensor-product; proetale.tex, Tag 09BQ, lemma-tensor-c.
(auxiliary; not a blueprint node).

Proof: The inverse image on the coefficient-sized sites is exact: base change preserves
finite limits, and the constant coefficient ring comparison is invertible. It therefore
commutes with cohomology and preserves the displayed upper bound. Zero cohomology objects
have the constant zero module as a finite local model, so the hypothesis supplies locally
constant finite type cohomology in every degree after restriction. The exact constant
realization of M has cohomology M in degree zero and zero in other degrees, and its
restriction is the constant realization of the same M. Choose flat-term K-flat resolutions
of these two restricted factors. The canonical tensor-pullback comparison identifies their
total tensor with the restriction of the displayed derived tensor. Apply Tag 094H to these
bounded-above factors. Transport its finite constant cohomology models through the exact
constant-scalar equivalence and its slice comparisons. This gives the stated finite local
models for the fixed-scalar inverse image of each cohomology sheaf. Empty covering sieves,
the zero module, the zero ring and empty schemes are allowed throughout; no finite
projective dimension of M or lower bound for the tensor is used. -/
theorem coefficientConstantTensor_restricted_finite
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (K : adicFiniteAmbient.{u, v} X A)
    (hK : ∃ b : ℤ, ∀ j : ℤ, b < j →
      CategoryTheory.Limits.IsZero ((coefficientModelCohomology _ j).obj K))
    (hloc : ∀ j : ℤ,
      ¬ CategoryTheory.Limits.IsZero ((coefficientModelCohomology _ j).obj K) →
      IsCoefficientModelLocallyConstantFinite
        (coefficientProEtaleModelTopology.{u, v} Y) A
        ((coefficientProEtaleFixedModulePullback.{u, v} f A).obj
          ((coefficientModelFixedScalars _ A).obj
            ((coefficientModelCohomology _ j).obj K))))
    (M : ModuleCat.{max v (u + 1)} A) (hM : Module.Finite A M) (q : ℤ) :
    let R := constant (coefficientProEtaleModelTopology.{u, v} X) A
    letI := HasDerivedCategory.standard (Mod R)
    IsCoefficientModelLocallyConstantFinite
      (coefficientProEtaleModelTopology.{u, v} Y) A
      ((coefficientProEtaleFixedModulePullback.{u, v} f A).obj
        ((coefficientModelFixedScalars _ A).obj
          ((coefficientModelCohomology _ q).obj
            (((SheafOfModules.KFlatFixedTensor.derivedTensor R).obj K).obj
              ((Q R).obj ((HomologicalComplex.single (Mod R) (.up ℤ) 0).obj
                ((commutativeSiteConstantModuleFunctor
                  (coefficientProEtaleModelTopology.{u, v} X) A).obj M))))))) := by
  dsimp only
  classical
  let R := constant (coefficientProEtaleModelTopology.{u, v} Y) A
  let S := constant (coefficientProEtaleModelTopology.{u, v} X) A
  let E := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} Y) A
  let F := coefficientModelFixedScalars (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    coefficientProEtaleFixedModulePullback.{u, v} f A
  let := HasDerivedCategory.standard (Mod S)
  let := HasDerivedCategory.standard
    (Sheaf (coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat A))
  let := SheafOfModules.monoidalCategory R
  obtain ⟨P, hb, hP, eK, eT⟩ := coefficient_restricted_tensor_flat_model f A K hK
  let : Abelian (Sheaf (coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat A)) :=
    inferInstance
  let H (j : ℤ) := DerivedCategory.homologyFunctor
    (Sheaf (coefficientProEtaleModelTopology.{u, v} Y) (ModuleCat A)) j
  let eH (V : CochainComplex (Mod R) ℤ) (j : ℤ) :
      (H j).obj (DerivedCategory.Q.obj ((E.mapHomologicalComplex (.up ℤ)).obj V)) ≅
        E.obj (V.homology j) :=
    (DerivedCategory.homologyFunctorFactors _ j).app _ ≪≫ (V.sc j).mapHomologyIso E
  let he (j : ℤ) : Nonempty (E.obj (P.homology j) ≅
      F.obj ((coefficientModelCohomology _ j).obj K)) :=
    ⟨(eH P j).symm ≪≫ (H j).mapIso eK.some.symm ≪≫
      ((F.mapDerivedCategoryHomologyFunctorIso j).app K).symm⟩
  let T := (((SheafOfModules.KFlatFixedTensor.derivedTensor S).obj K).obj
    ((Q S).obj ((HomologicalComplex.single (Mod S) (.up ℤ) 0).obj
      ((commutativeSiteConstantModuleFunctor
        (coefficientProEtaleModelTopology.{u, v} X) A).obj M))))
  let ht : Nonempty (F.obj ((coefficientModelCohomology _ q).obj T) ≅
      E.obj ((((tensorLeft ((commutativeSiteConstantModuleFunctor
        (coefficientProEtaleModelTopology.{u, v} Y) A).obj M)).mapHomologicalComplex
          (.up ℤ)).obj P).homology q)) :=
    ⟨((F.mapDerivedCategoryHomologyFunctorIso q).app T) ≪≫
      (H q).mapIso (eT M).some ≪≫ eH _ q⟩
  have hl (j : ℤ) : SheafOfModules.IsLocallyConstantFiniteTypeModules
      (coefficientProEtaleModelTopology.{u, v} Y) A (P.homology j) := by
    apply (local_models_iff _ A _).mpr
    intro V
    by_cases hz : IsZero ((coefficientModelCohomology _ j).obj K)
    · have hzero : IsZero (P.homology j) := by
        have hm := Functor.map_isZero (coefficientModelFixedScalars _ A) hz
        have hp := Functor.map_isZero (coefficientProEtaleFixedModulePullback f A) hm
        have hp' := hp.of_iso (he j).some
        exact IsZero.of_full_of_faithful_of_isZero
          (coefficientModelFixedScalars _ A) _ hp'
      exact (local_models_iff _ A _).mp (SheafOfModules.zero_lisse _ A _ hzero) V
    · obtain ⟨S, hS, hs⟩ := hloc j hz V
      refine ⟨S, hS, ?_⟩
      intro U g hg
      obtain ⟨N, hN, ⟨eN⟩⟩ := hs U g hg
      exact ⟨N, hN, ⟨((coefficientProEtaleModelTopology.{u, v} Y).overPullback
        (ModuleCat A) U).mapIso (he j).some ≪≫ eN⟩⟩
  have hfinite := finite_constant_tensor
    (coefficientProEtaleModelTopology.{u, v} Y) A M hM P hP hb hl q
  have hout := (local_models_iff _ A _).mp hfinite
  intro V
  obtain ⟨S, hS, hs⟩ := hout V
  refine ⟨S, hS, ?_⟩
  intro U g hg
  obtain ⟨N, hN, ⟨eN⟩⟩ := hs U g hg
  exact ⟨N, hN, ⟨((coefficientProEtaleModelTopology.{u, v} Y).overPullback
    (ModuleCat A) U).mapIso ht.some ≪≫ eN⟩⟩

end AlgebraicGeometry.Scheme
