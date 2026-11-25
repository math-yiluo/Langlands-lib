/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientTensorOrdinaryCoherence
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationStrictSigma

/-!
# Strict tensor and truncation coherence on complexes

Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03EK.
(blueprint: lem-pur-coefficient-evaluation-ordinary-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C]
  {O : Type w} [CommRing O] {ell : O}
local notation "ev" => coefficientEvaluation (J := J) (O := O) (ell := ell)
local notation "tensor" => coefficientTensor (J := J) (O := O) (ell := ell)

/-- The normalized ordinary tensor comparisons, strict truncation inclusions and their
termwise complex lifts. Source: Zheng, Construction 4.1; Stacks Tag 03EK
(blueprint: lem-pur-coefficient-evaluation-ordinary-coherence). -/
structure CoefficientEvaluationOrdinaryCoherenceData
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] where
  tensorUnit : ∀ n, (tensor (Nat.le_refl n)) ≅ 𝟭 _
  tensorUnit_normalized : CoefficientTensorUnitNormalized tensorUnit
  tensorAssoc : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m),
    (tensor h₁) ⋙ (tensor h₂) ≅ (tensor (h₂.trans h₁))
  tensorAssoc_normalized : CoefficientTensorAssocNormalized tensorAssoc
  strictSigma : ∀ {m n} (h : n ≤ m),
    (tensor h) ⋙ ordinary.extension n ⟶ ordinary.extension m
  strictSigma_below : ∀ {m n q} (h : n ≤ m) (hq : q ≤ n) F,
    (ordinary.below hq).inv.app ((tensor h).obj F) ≫
      (ev q).map ((strictSigma h).app F) ≫ (ordinary.below (hq.trans h)).hom.app F =
        (tensorAssoc h hq).hom.app F
  strictSigma_above : ∀ {m n q} (h : n ≤ m) (_hq : n < q) F,
    (ev q).map ((strictSigma h).app F) = 0
  strictSigma_transpose : ∀ {m n} (h : n ≤ m) F,
    (ordinary.adj n).homEquiv _ _ ((strictSigma h).app F) =
      (ordinary.below h).inv.app F
  strictSigmaComplex : ∀ {m n} (h : n ≤ m) P,
    ((ordinary.extension n).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((tensor h).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ⟶
    ((ordinary.extension m).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  strictSigmaComplex_f : ∀ {m n} (h : n ≤ m) P i,
    (strictSigmaComplex h P).f i = (strictSigma h).app (P.X i)
  tensorUnitComplex : ∀ n P,
    ((tensor (Nat.le_refl n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ≅ P
  tensorUnitComplex_f : ∀ n P i,
    ((tensorUnitComplex n P).hom).f i = (tensorUnit n).hom.app (P.X i)
  tensorAssocComplex : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P,
    ((tensor h₂).mapHomologicalComplex (ComplexShape.up
      ℤ)).obj
      (((tensor h₁).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅
    ((tensor (h₂.trans h₁)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P
  tensorAssocComplex_f : ∀ {l m n} (h₁ : m ≤ l) (h₂ : n ≤ m) P i,
    ((tensorAssocComplex h₁ h₂ P).hom).f i = (tensorAssoc h₁ h₂).hom.app (P.X i)

/-- The normalized tensor comparisons and truncation inclusions lift termwise to complexes.
Source: Zheng, Construction 4.1, p. 21; Stacks Tag 03EK
(blueprint: lem-pur-coefficient-evaluation-ordinary-coherence).
Proof: choose the normalized ordinary tensor unit and associator. Transpose the inverse
below-level comparison to obtain each strict truncation inclusion; its components below
the smaller index are the associator, and above that index its source is zero. Apply the
functor on homological complexes to these transformations and isomorphisms. Naturality
makes them chain maps, and their degree components are the original maps. Compose the
unit lift with the canonical identity-complex comparison. -/
theorem coefficientEvaluationOrdinaryCoherence
    (ordinary : CoefficientOrdinaryEvaluationData (J := J) (O := O) (ell := ell))
    [∀ n, (ordinary.extension n).Additive] :
    Nonempty (CoefficientEvaluationOrdinaryCoherenceData ordinary) := by
  classical
  obtain ⟨unit, hu, assoc, ha⟩ :=
    coefficientTensorOrdinaryCoherence (J := J) (O := O) (ell := ell)
  obtain ⟨sigma, hs, hz, ht⟩ := coefficientEvaluationStrictSigma ordinary
    (fun {_ _ _} h₁ h₂ ↦ assoc h₁ h₂) ha
  exact ⟨{
    tensorUnit := unit
    tensorUnit_normalized := hu
    tensorAssoc := fun h₁ h₂ ↦ assoc h₁ h₂
    tensorAssoc_normalized := ha
    strictSigma := fun h ↦ sigma h
    strictSigma_below := hs
    strictSigma_above := hz
    strictSigma_transpose := ht
    strictSigmaComplex := fun h P ↦ ((sigma h).mapHomologicalComplex (.up ℤ)).app P
    strictSigmaComplex_f := fun _ _ _ ↦ rfl
    tensorUnitComplex := fun n P ↦
      (NatIso.mapHomologicalComplex (unit n) (.up ℤ) ≪≫
        CategoryTheory.Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P
    tensorUnitComplex_f := fun _ _ _ ↦ Category.comp_id _
    tensorAssocComplex := fun h₁ h₂ P ↦
      (NatIso.mapHomologicalComplex (assoc h₁ h₂) (.up ℤ)).app P
    tensorAssocComplex_f := fun _ _ _ _ ↦ rfl }⟩

end SheafOfModules
