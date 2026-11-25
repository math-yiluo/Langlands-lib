/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueKoszulCoefficientAugmentation
import WeilConjectures.AlgebraicGeometry.AdicResidueKoszulCoefficientConeComparison
import all WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero

/-! # The Noetherian cone calculation for the tensor of the coefficient augmentation

Source: Stacks Project, more-algebra.tex, lemma-sequence-Koszul-complexes,
and proetale.tex, lemma-naive-completion (099M).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] homComplexFunctor ringedKoszulDualTower
  ringedKoszulTensorTowerComplex completed adicResidueQuotientCoefficientTower
  HomologicalComplex.single HomologicalComplex.extendMap ExteriorAlgebra.koszulComplex
  ringedKoszulDualUnit adicResidueQuotientCoefficientUnit
  coefficientMap algebraSection ringedKoszulSliceSection adicResidueKoszulTensorTranspose

private theorem proZero_of_exact_comparison
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : CochainComplex C ℤ ⥤ CochainComplex D ℤ) [F.PreservesZeroMorphisms]
    (hF : ∀ {K L : CochainComplex C ℤ} (g : K ⟶ L), QuasiIso g → QuasiIso (F.map g))
    (K : ℕ → CochainComplex C ℤ) (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (T : ℕᵒᵖ ⥤ CochainComplex D ℤ) (e : ∀ n, F.obj (K n) ≅ T.obj (op n))
    (he : ∀ n m h, F.map (t n m h) ≫ (e n).hom =
      (e m).hom ≫ T.map (homOfLE h).op)
    (hz : ∀ n, ∃ m h, DerivedCategory.Q.map (t n m h) = 0) :
    ∀ n, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map (T.map (homOfLE h).op) = 0 := by
  intro n
  obtain ⟨m, h, hm⟩ := hz n
  refine ⟨m, h, ?_⟩
  have hzF := localizedZero_map F hF _ hm
  have hn := congrArg (fun f ↦ DerivedCategory.Q.map f) (he n m h)
  rw [Functor.map_comp, Functor.map_comp, hzF, zero_comp] at hn
  exact (cancel_epi (DerivedCategory.Q.map (e m).hom)).1 (hn.symm.trans (by simp))

/-- Keep exact-functor instances abstract while transporting the derived zero maps. -/
private theorem proZero_of_exact_realization
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (K : ℕ → CochainComplex C ℤ) (t : ∀ n m : ℕ, n ≤ m → (K m ⟶ K n))
    (T : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (e : ∀ n, (E.mapHomologicalComplex (.up ℤ)).obj (K n) ≅ T.obj (op n))
    (he : ∀ n m h, (E.mapHomologicalComplex (.up ℤ)).map (t n m h) ≫ (e n).hom =
      (e m).hom ≫ T.map (homOfLE h).op)
    (hz : ∀ n, ∃ m h, DerivedCategory.Q.map (t n m h) = 0) :
    ∀ n, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map (T.map (homOfLE h).op) = 0 := by
  exact proZero_of_exact_comparison (E.mapHomologicalComplex (.up ℤ))
    (fun g hg ↦ by
      have : QuasiIso g := hg
      infer_instance) K t T e he hz

/-- Construct the cone comparison before specializing the coefficient category. -/
private def coneIsoOfSource
    {B : Type*} [Category B] [Abelian B]
    {K K' L : CochainComplex B ℤ} (f : K' ⟶ L) (e : K ≅ K') :
    CochainComplex.mappingCone (e.hom ≫ f) ≅ CochainComplex.mappingCone f :=
  HomologicalComplex.homotopyCofiber.mapArrowIso (e.hom ≫ f) f
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    (Arrow.isoMk e (Iso.refl _) (by simp))

-- Comparing the normalized finite complexes and their exact realizations is instance-heavy.
/-- The cone calculation for a specified coefficient augmentation. There is no
existence or scalar-adjoint-tower assertion in this statement.

Source: Stacks Project, more-algebra.tex, lemma-sequence-Koszul-complexes,
and proetale.tex, lemma-naive-completion (099M).
(auxiliary; not a blueprint node).

Proof: the negative exterior model of the dual finite Koszul complex is supported
in degrees [-r,0], and its degree-zero dual unit is an isomorphism onto the
term R. A map from this complex to B_n[0] is therefore uniquely determined by
its composite with that unit. The normalization of epsilon identifies it with
the degree-zero quotient augmentation in the exterior model, and identifies
all its strict squares with the canonical diagonal/quotient squares.
Apply noetherian_koszul_augmentation_pro_zero over A. Exact constant realization
and flat extension along the completed coefficient map carry its zero derived
cone maps to zero derived maps on the slice. The quotient identification in
flat_and_quotients identifies the targets with the actual B_n. Exact restriction
to the slice preserves those comparisons. Tensoring by the fixed K-flat P
descends to an additive functor on the derived category and thus preserves zero
maps. The natural tensor-cone comparison multiplies the shifted source summand
in tensor degree p by (-1)^p, and identifies the resulting maps with the actual
strict cone transitions of adicResidueKoszulTensorAugmentation. Its degreewise
transpose does not change these maps. This proves the assertion. For r=0 the
augmentation is an isomorphism since J=0; for J=A the quotients are zero and the
same algebraic pro-zero theorem applies. The zero ring and zero P require no
exception. No tensor product is interchanged with an infinite product. -/
theorem adicResidue_koszul_tensor_cone_proZero
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = J)
    (P : Cx ((completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U))
    (hP : P.IsKFlatTensor) (hflat : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    let R := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let b := fun i ↦ ringedKoszulSliceSection
      (completed (coefficientProEtaleModelTopology.{u, v} X) A J)
      (algebraSection (coefficientMap (coefficientProEtaleModelTopology.{u, v} X) A J)
        (a i)) U
    ∀ (ε : ringedKoszulDualTower R r b ⟶ adicResidueQuotientCoefficientTower X J U)
      (_hε : ∀ n : ℕ, ringedKoszulDualUnit R r b n ≫ ε.app (op n) =
        adicResidueQuotientCoefficientUnit X J U n),
      ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), (Q R).map
        ((CochainComplex.mappingCone (C := ℕᵒᵖ ⥤ Mod R)
          (adicResidueKoszulTensorAugmentation X J U r b P ε)).asFunctor.map
            (homOfLE h).op) = 0 := by
  intro R b ε hε
  have _ := hflat
  obtain ⟨εA, tA, qA, hεA, htA, hqA, hc, hz⟩ :=
    ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero A r a
  obtain ⟨E, hE, hlim, hcolim, e, he⟩ :=
    adicResidue_koszul_coefficient_cone_comparison.{u, v} X (A := A) J U r a ha
      εA tA qA hεA htA hqA hc ε hε
  have hcoef : FlatConstantConeProZero ε :=
    proZero_of_exact_realization E _ _ _ e he hz
  have ht := flatConstantConeProZero_tensor (C := Over U) (O := R)
    ((coefficientProEtaleModelTopology.{u, v} X).over U) P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat (R := R) P).2 hP) ε hcoef
  let f := (HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).inverse.map
    (Functor.whiskerRight ε ((ringedKoszulTensor R).obj P))
  let α := adicResidueKoszulTensorAugmentation X J U r b P ε
  let c : CochainComplex.mappingCone α ≅ CochainComplex.mappingCone f := by
    unfold α adicResidueKoszulTensorAugmentation
    exact coneIsoOfSource f (adicResidueKoszulTensorTranspose X J U r b P)
  exact proZero_of_towerIso
    ((HomologicalComplex.functorEquivalence (Mod R) (.up ℤ) ℕᵒᵖ).functor.mapIso c).symm ht

end AlgebraicGeometry.Scheme
