/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentation
import WeilConjectures.AlgebraicGeometry.ConstantExactCoefficientRealization
import WeilConjectures.AlgebraicGeometry.ConstantKoszulCoefficientConeComparison
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorConeComparison
import all WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero

/-! # Derived-limit invertibility of the normalized strict augmentation

Source: Stacks Project, proetale.tex, Tag 099M, and sites-modules.tex, Tag 093M.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local instance] HasDerivedCategory.standard
  flatConstantCochainMonoidal flatConstantCochainMonoidalStruct
attribute [local irreducible] HasDerivedCategory.standard strictLimit

private theorem proZero_of_exact_realization
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (E : B ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : ℕ → CochainComplex B ℤ) (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (T : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.obj (op n))
    (he : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map (t n m h) ≫ (e n).hom =
      (e m).hom ≫ T.map (homOfLE h).op)
    (hz : ∀ n, ∃ m h, DerivedCategory.Q.map (t n m h) = 0) :
    ∀ n, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map (T.map (homOfLE h).op) = 0 := by
  intro n
  obtain ⟨m, h, hm⟩ := hz n
  refine ⟨m, h, ?_⟩
  have hE : ∀ {K L : CochainComplex B ℤ} (f : K ⟶ L),
      QuasiIso f → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
    intro K L f hf
    have : QuasiIso f := hf
    infer_instance
  have hzE := localizedZero_map (E.mapHomologicalComplex (.up ℤ)) hE (t n m h) hm
  have hn := congrArg (fun f ↦ DerivedCategory.Q.map f) (he n m h)
  rw [Functor.map_comp, Functor.map_comp, hzE, zero_comp] at hn
  exact (cancel_epi (DerivedCategory.Q.map (e m).hom)).1 (hn.symm.trans (by simp))

/-- A normalized strict augmentation becomes invertible after total derived inverse
limit on a flat-term K-flat complex. This concerns strict complexes, before descent
and independently of either chosen Koszul or quotient presentation.
Source: Stacks Project, Tag 099M (lemma-naive-completion), proof; Tag 093M
(lemma-completion-flat); More on Algebra, the sequence of Koszul complexes.
(auxiliary; not a blueprint node).

Proof: apply noetherian_koszul_augmentation_pro_zero to A and the ordered generators.
The exterior model identifies its negative complex and diagonal transitions with the
dual of the positive tensor Koszul system. Apply the exact constant-module realization
and then extend scalars to the coefficient sheaf. The extension is flat: it is the
identity for b=false, and flat_and_quotients gives flatness and the finite quotient
identifications for b=true. Tensor with P. The zero-summand and unit normalization
identify the resulting map with the supplied augmentation: the dual complex has no
positive degrees, its degree-zero term is the unit, and the tensor coproduct inclusions
jointly determine every component. Tensor commutes with cones using the sign (-1)^p
on the shifted-source summand in P-degree p. Thus flatConstantTensorProZeroCones makes
the cone tower pro-zero and makes total right derived inverse limit invert this map.
The right-derived universal property identifies that functor with the specified rlim.
The empty list generates I=0, when the coefficient augmentation is an isomorphism;
for the zero ring all complexes vanish. No exactness of products is used. -/
theorem koszulQuotientAugmentation_isIso [IsNoetherianRing A] (b : Bool) (r : ℕ)
    (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (P : Cx (coefficients J A I b)) (hP : P.IsKFlatTensor)
    (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    IsIso ((rlim (coefficients J A I b)).map
      ((TQ (coefficients J A I b)).map (α.app P))) := by
  let O := coefficients J A I b
  let U := ringedSiteRingComplex O
  obtain ⟨εA, tA, qA, hεA, htA, hqA, hc, hz⟩ :=
    ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero A r a
  obtain ⟨E, hadd, hlim, hcolim, cE, qE, hs, hq⟩ :=
    constantExactCoefficientRealization J A I b
  obtain ⟨e, he⟩ :=
    constantKoszulCoefficientConeComparison J A I b E cE qE hs hq r a ha
      εA tA qA hεA htA hqA hc (α.app U) (hα.1 U)
  have hcoef : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), (Q O).map
      ((CochainComplex.mappingCone (α.app U)).asFunctor.map (homOfLE h).op) = 0 :=
    proZero_of_exact_realization E _ _ _ e he hz
  obtain ⟨c⟩ := constantKoszulTensorConeComparison J A I b r a α hα P
  have hP' := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
    (R := O) P).2 hP
  have ht : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), (Q O).map
      ((CochainComplex.mappingCone (α.app P)).asFunctor.map (homOfLE h).op) = 0 := by
    apply proZero_of_towerIso c
    intro n
    obtain ⟨m, h, hm⟩ := hcoef n
    refine ⟨m, h, ?_⟩
    have : (tensorLeft P).PreservesZeroMorphisms := by
      constructor
      intro K L
      change HomologicalComplex.mapBifunctorMap (𝟙 P) (0 : K ⟶ L)
        (curriedTensor _) (.up ℤ) = 0
      exact mapBifunctorMap_id_zero (curriedTensor _) P K L
    exact localizedZero_map (tensorLeft P)
      (fun f hf ↦ flatConstantTensor_preservesQuasiIso (O := O) J P hP' f hf)
      ((CochainComplex.mappingCone (α.app U)).asFunctor.map (homOfLE h).op) hm
  let v := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app P)
  have hv : FlatConstantConeProZero v := by
    change ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), (Q O).map
      ((CochainComplex.mappingCone (α.app P)).asFunctor.map (homOfLE h).op) = 0
    exact ht
  have _ := hflat
  exact ringedLimit_proZero_isIso J (siteModuleRings O)
    (fun U a b ↦ @mul_comm (O.obj.obj U) _ a b)
    (rlim O) (limitComparison O) (strictLimit O).universal v hv

end CategoryTheory.ConstantCompletion
