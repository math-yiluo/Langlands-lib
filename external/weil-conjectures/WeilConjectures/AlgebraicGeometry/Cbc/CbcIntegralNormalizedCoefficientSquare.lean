/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedCoefficientFamilies
import WeilConjectures.AlgebraicGeometry.Cbc.CbcProperCoefficientSquare
import WeilConjectures.AlgebraicGeometry.Cbc.CbcOpenCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
/-! Integral normalized square, after the proper and open coefficient mates.
Source: coefficient-coherence proof steps 5--10.
(blueprint: lem-cbc-integral-normalized-coefficient-square).
Proof: paste the unit-normalized proper and open coefficient squares, use naturality
of the proper pushforward comparison, then substitute the four beta specifications
and cancel the endpoint conjugations. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcIntegralDatum
  AdicCoefficientDatum.completedPull cbcDerivedOpenShriek

private theorem app_heq
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (t : F ⟶ G) {x y : A} (h : x = y) : HEq (t.app x) (t.app y) := by
  cases h
  rfl

private theorem identity_square
    {A B : Type*} [Category A] [Category B] {U V : A ⥤ B}
    (S : A ⥤ A) (T : B ⥤ B) (bU : U ⋙ T ≅ S ⋙ U) (bV : V ⋙ T ≅ S ⋙ V)
    (hS : S = 𝟭 A) (hT : T = 𝟭 B)
    (hU : ∀ x, HEq (bU.hom.app x) (𝟙 (U.obj x)))
    (hV : ∀ x, HEq (bV.hom.app x) (𝟙 (V.obj x))) (t : U ⟶ V) (x : A) :
    T.map (t.app x) ≫ bV.hom.app x = bU.hom.app x ≫ t.app (S.obj x) := by
  subst S
  subst T
  rw [eq_of_heq (hU x), eq_of_heq (hV x)]
  change t.app x ≫ 𝟙 _ = 𝟙 _ ≫ t.app x
  rw [Category.comp_id, Category.id_comp]

private theorem ambientSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb)
    (P : CbcCompletedScalarComparison l Ω g)
    (P' : CbcCompletedScalarComparison l Ω g')
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (s : ℕ) (b : Fin s → PbcIntegralRing l (pbcFiniteField.{u} l Ω F))
    (hb : Ideal.span (Set.range b) = (pbcStageDatum.{u} l Ω F).ideal)
    (K : pbcAmbientStage l Ω X E)
    (hK : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K)
    (hCK : cbcCompleteProperty (pbcStageDatum.{u} l Ω F) X s b hb
      ((pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) X).obj K)) :
    completedCompactSupportExchange (pbcStageDatum.{u} l Ω F) c c' gb sp sj
        s b hb ⟨_, hCK⟩ ≫
      cbcScalarTargetInverse l _ _ (pbcFiniteFieldInclusion l Ω h) g' c'
        (P'.map h) K =
    cbcScalarSourceInverse l _ _ (pbcFiniteFieldInclusion l Ω h) g c
        (P.map h) K ≫
      (pbcEmbeddingAmbientTensor l _ _ (pbcFiniteFieldInclusion l Ω h) Y').map
        (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E) c c' gb sp sj
          r a ha ⟨K, hK⟩) := by
  let := c.isProper
  let := c.isOpenImmersion
  let := c'.isOpenImmersion
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨Q, hQ⟩ := cbcProperCoefficientSquare l Ω sp P
  have hJ := ((completedOpenExchangeComparison (pbcStageDatum.{u} l Ω E) sj
    r a ha).2 ⟨K, hK⟩).1
  have hp := hQ h ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E)
    c.i c.isOpenImmersion).obj K)
      (cbcTowerComplete_of_property (pbcStageDatum.{u} l Ω E) c.Z r a ha _ hJ)
  have ho := cbcOpenCoefficientSquare l Ω sj Q P' h r a ha s b hb K hK hCK
  have hn := cbcCompletedExchange_naturality (pbcStageDatum.{u} l Ω F) sp
    ((cbcScalarOpenInverse l _ _ (pbcFiniteFieldInclusion l Ω h) c.i).app K)
  have hd := (pbcScalarDirectImageIso l _ _ (pbcFiniteFieldInclusion l Ω h) c'.g).inv.naturality
    ((cbcDatumCompletedExchange (pbcStageDatum.{u} l Ω E) sj r a ha).app ⟨K, hK⟩)
  dsimp only [Functor.comp_map] at hd
  unfold completedCompactSupportExchange cbcScalarTargetInverse cbcScalarSourceInverse
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [ho]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  erw [hd]
  erw [reassoc_of% hp]
  rfl

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]

end AlgebraicGeometry.Scheme
