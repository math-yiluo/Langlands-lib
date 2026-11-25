/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.EtaleTensorShiftCancellationNaturality
import WeilConjectures.AlgebraicGeometry.Etale.EtaleTensorHomTransposeNaturality

/-! # Tensor-Hom shift comparison from evaluation

The categorical diagram chase underlying the étale Hom comparison shift square.
(blueprint: lem-coef-tensor-hom-shift-comparison-component) -/

@[expose] public section
set_option autoImplicit false
universe u u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

section
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]

private theorem normalized_transpose_aux
    (T : D ⥤ D ⥤ D) [∀ K, (T.obj K).Additive]
    (H : Dᵒᵖ ⥤ D ⥤ D) (ad : ∀ K, T.obj K ⊣ H.obj (op K))
    (c : ∀ K L : D, ∀ n : ℤ, (T.obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ (T.obj K).obj L)
    (M K P : D) (s : (H.flip.obj M).CommShift ℤ) (n : ℤ)
    (hs : (T.obj (K⟦-n⟧)).map
      (((n * (n + 1)) / 2).negOnePow • ((s.commShiftIso n).hom.app (op K))) ≫
      c K ((H.flip.obj M).obj (op K)) n ≫ (ad K).counit.app M =
        (ad (K⟦-n⟧)).counit.app M)
    (f : P ⟶ ((H.flip.obj M).obj (op K))⟦n⟧) :
    (T.obj (K⟦-n⟧)).map (((n * (n + 1)) / 2).negOnePow • f) ≫
        c K ((H.flip.obj M).obj (op K)) n ≫ (ad K).counit.app M =
      ((ad (K⟦-n⟧)).homEquiv _ _).symm (f ≫ (s.commShiftIso n).inv.app (op K)) := by
  rw [Adjunction.homEquiv_counit, ← hs]
  rw [← Functor.map_comp_assoc]
  congr 2
  simp only [Category.assoc, Linear.comp_units_smul]
  erw [Iso.inv_hom_id_app, Category.comp_id]

omit [Preadditive D] in
private theorem hom_shift_ext_aux
    (T : D ⥤ D ⥤ D) (H : Dᵒᵖ ⥤ D ⥤ D)
    (ad : ∀ K, T.obj K ⊣ H.obj (op K)) (M K P Q : D)
    (s : (H.flip.obj M).CommShift ℤ) (n : ℤ)
    (f : P ⟶ ((H.flip.obj M).obj (op K))⟦n⟧) (g : P ⟶ Q)
    (j : Q ⟶ (H.obj (op (K⟦-n⟧))).obj M)
    (h : ((ad (K⟦-n⟧)).homEquiv _ _).symm
        (f ≫ (s.commShiftIso n).inv.app (op K)) =
      ((ad (K⟦-n⟧)).homEquiv _ _).symm (g ≫ j)) :
    f = g ≫ j ≫ (s.commShiftIso n).hom.app (op K) := by
  have he := ((ad (K⟦-n⟧)).homEquiv _ _).symm.injective h
  calc
    f = (f ≫ (s.commShiftIso n).inv.app (op K)) ≫
        (s.commShiftIso n).hom.app (op K) := by
      rw [Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id f).symm
    _ = (g ≫ j) ≫ (s.commShiftIso n).hom.app (op K) := congrArg (· ≫ _) he
    _ = g ≫ j ≫ (s.commShiftIso n).hom.app (op K) := Category.assoc _ _ _

private theorem evaluation_chase
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasShift D ℤ] (F : C ⥤ D) [F.Additive] (n : ℤ)
    (T : C ⥤ C) (U V W : D ⥤ D) [U.Additive]
    {H Hn H' P M : C} {J : D}
    (a : H' ⟶ Hn) (q : F.obj Hn ⟶ (F.obj H)⟦n⟧)
    (v : F.obj H ⟶ J) (p : W ⟶ U)
    (c : ∀ L : D, U.obj (L⟦n⟧) ⟶ V.obj L)
    (μ : V.obj (F.obj H) ⟶ F.obj P)
    (μn : W.obj (F.obj Hn) ⟶ F.obj (T.obj Hn))
    (μ' : W.obj (F.obj H') ⟶ F.obj (T.obj H'))
    (d : T.obj Hn ⟶ P) (e : P ⟶ M) (e' : T.obj H' ⟶ M)
    (eB : V.obj J ⟶ F.obj M) (ε : ℤˣ)
    (hc : U.map (v⟦n⟧') ≫ c J = c (F.obj H) ≫ V.map v)
    (hv : μ ≫ F.map e = V.map v ≫ eB)
    (hs : p.app (F.obj Hn) ≫ U.map q ≫ c (F.obj H) ≫ μ = μn ≫ F.map d)
    (hμ : W.map (F.map (ε • a)) ≫ μn = μ' ≫ F.map (T.map (ε • a)))
    (he : T.map (ε • a) ≫ d ≫ e = e') :
    p.app (F.obj H') ≫ U.map (ε • ((F.map a ≫ q) ≫ v⟦n⟧')) ≫ c J ≫ eB =
      μ' ≫ F.map e' := by
  simp only [Category.assoc]
  rw [← Linear.units_smul_comp, ← Functor.map_units_smul]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, ← hv]
  rw [← p.naturality_assoc, reassoc_of% hs, reassoc_of% hμ]
  simp only [← Functor.map_comp]
  rw [he]

private theorem iso_left_cancel {D : Type*} [Category D]
    {P Q R : D} (p : P ≅ Q) (f : Q ⟶ R) (g : P ⟶ R)
    (h : p.hom ≫ f = g) : f = p.inv ≫ g := by
  rw [← h, p.inv_hom_id_assoc]

end

/-- An evaluation transpose preserves normalized Hom shifts when the tensor comparison
preserves cancellation of opposite shifts.
Source: Stacks Project, Tags 08JC and 08J9; blueprint `lemma-change-coefficients-internal-hom--1`,
proof paragraph 2.

Proof. Cancel the target Hom shift and transpose using evaluation normalization. Tensor
cancellation naturality moves the shifted comparison past cancellation. Cancel the scalar
shift in the first tensor variable, use the evaluation-transpose equation, scalar tensor
cancellation, and naturality of the tensor comparison. The source evaluation normalization
finishes the chase; adjunction injectivity gives the original square.
(blueprint: lem-coef-tensor-hom-shift-comparison-component) -/
private theorem tensorHomShiftComparison_aux
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    (TA : C ⥤ C ⥤ C) [∀ K, (TA.obj K).Additive] (HA : Cᵒᵖ ⥤ C ⥤ C)
    (TB : D ⥤ D ⥤ D) [∀ K, (TB.obj K).Additive] (HB : Dᵒᵖ ⥤ D ⥤ D)
    (adA : ∀ K, TA.obj K ⊣ HA.obj (op K))
    (adB : ∀ K, TB.obj K ⊣ HB.obj (op K))
    (μ : ∀ K L, (TB.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((TA.obj K).obj L))
    (cA : ∀ K L : C, ∀ n : ℤ, (TA.obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ (TA.obj K).obj L)
    (cB : ∀ K L : D, ∀ n : ℤ, (TB.obj (K⟦-n⟧)).obj (L⟦n⟧) ⟶ (TB.obj K).obj L)
    (M : C) (v : HA.flip.obj M ⋙ F ⟶ F.op ⋙ HB.flip.obj (F.obj M))
    (hv : ∀ K, (μ K ((HA.obj (op K)).obj M)).hom ≫ F.map ((adA K).counit.app M) =
      ((adB (F.obj K)).homEquiv ((HA.flip.obj M ⋙ F).obj (op K)) (F.obj M)).symm
        (v.app (op K)))
    (sA : (HA.flip.obj M).CommShift ℤ) (sB : (HB.flip.obj (F.obj M)).CommShift ℤ)
    (K : C) (n : ℤ)
    (hA : (TA.obj (K⟦-n⟧)).map
      (((n * (n + 1)) / 2).negOnePow • ((sA.commShiftIso n).hom.app (op K))) ≫
      cA K ((HA.flip.obj M).obj (op K)) n ≫ (adA K).counit.app M =
        (adA (K⟦-n⟧)).counit.app M)
    (hB : (TB.obj ((F.obj K)⟦-n⟧)).map
      (((n * (n + 1)) / 2).negOnePow •
        ((sB.commShiftIso n).hom.app (op (F.obj K)))) ≫
      cB (F.obj K) ((HB.flip.obj (F.obj M)).obj (op (F.obj K))) n ≫
        (adB (F.obj K)).counit.app (F.obj M) =
        (adB ((F.obj K)⟦-n⟧)).counit.app (F.obj M))
    (hnB : ∀ (K L P : D) (f : K ⟶ L) (g : P ⟶ (HB.obj (op L)).obj (F.obj M)),
      ((adB K).homEquiv _ _).symm (g ≫ (HB.flip.obj (F.obj M)).map f.op) =
        (TB.map f).app P ≫ ((adB L).homEquiv _ _).symm g)
    (hcB : ∀ (K L L' : D) (g : L ⟶ L') (n : ℤ),
      (TB.obj (K⟦-n⟧)).map (g⟦n⟧') ≫ cB K L' n = cB K L n ≫ (TB.obj K).map g)
    (hμ : ∀ (K L L' : C) (g : L ⟶ L'),
      (TB.obj (F.obj K)).map (F.map g) ≫ (μ K L').hom =
        (μ K L).hom ≫ F.map ((TA.obj K).map g))
    (hs : ∀ (K L : C) (n : ℤ),
      (TB.map ((F.commShiftIso (-n)).hom.app K)).app (F.obj (L⟦n⟧)) ≫
        (TB.obj ((F.obj K)⟦-n⟧)).map ((F.commShiftIso n).hom.app L) ≫
        cB (F.obj K) (F.obj L) n ≫ (μ K L).hom =
      (μ (K⟦-n⟧) (L⟦n⟧)).hom ≫ F.map (cA K L n))
    :
    (F.map ((sA.commShiftIso n).hom.app (op K)) ≫
      (F.commShiftIso n).hom.app ((HA.flip.obj M).obj (op K))) ≫ (v.app (op K))⟦n⟧' =
    v.app (op (K⟦-n⟧)) ≫ (HB.flip.obj (F.obj M)).map
      (((F.commShiftIso (-n)).inv.app K).op) ≫
        (sB.commShiftIso n).hom.app (op (F.obj K)) := by
  let H := (HA.flip.obj M).obj (op K)
  let H' := (HA.flip.obj M).obj (op (K⟦-n⟧))
  let a : H' ⟶ H⟦n⟧ := (sA.commShiftIso n).hom.app (op K)
  let ε := ((n * (n + 1)) / 2).negOnePow
  let p := (TB.mapIso ((F.commShiftIso (-n)).app K)).app (F.obj H')
  apply hom_shift_ext_aux TB HB adB (F.obj M) (F.obj K) _ _ sB n
  refine (normalized_transpose_aux TB HB adB cB (F.obj M) (F.obj K) _ sB n
    hB _).symm.trans ?_
  have hy := (hnB ((F.obj K)⟦-n⟧) (F.obj (K⟦-n⟧)) (F.obj H')
    ((F.commShiftIso (-n)).inv.app K) (v.app (op (K⟦-n⟧)))).trans
      (congrArg (_ ≫ ·) (hv (K⟦-n⟧)).symm)
  refine Eq.trans ?_ hy.symm
  apply iso_left_cancel p
  have hv₀ := hv K
  rw [Adjunction.homEquiv_counit] at hv₀
  exact evaluation_chase F n (TA.obj (K⟦-n⟧))
    (TB.obj ((F.obj K)⟦-n⟧)) (TB.obj (F.obj K)) (TB.obj (F.obj (K⟦-n⟧)))
    a ((F.commShiftIso n).hom.app H) (v.app (op K))
    (TB.map ((F.commShiftIso (-n)).hom.app K)) (fun L ↦ cB (F.obj K) L n)
    (μ K H).hom (μ (K⟦-n⟧) (H⟦n⟧)).hom (μ (K⟦-n⟧) H').hom
    (cA K H n) ((adA K).counit.app M) ((adA (K⟦-n⟧)).counit.app M)
    ((adB (F.obj K)).counit.app (F.obj M)) ε
    (hcB (F.obj K) _ _ (v.app (op K)) n) hv₀ (hs K H n)
    (hμ (K⟦-n⟧) _ _ (ε • a)) hA

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.instMonoidalCategory
  _root_.DerivedCategory.commShift₂CurriedTensor

/-- `EtaleHomShiftNormalization` in the form used by the abstract chase. Stated once for both
coefficient categories, so the kernel unfolds the normalization only here. -/
private theorem etaleHomShiftNormalization_apply
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (s : ((derivedHom C X).flip.obj M).CommShift ℤ) (h : EtaleHomShiftNormalization C X M s)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) :
    ((derivedTensor C X).obj (K⟦-n⟧)).map
      (((n * (n + 1)) / 2).negOnePow • ((s.commShiftIso n).hom.app (op K))) ≫
      etaleHomTensorShiftCancellation C X K (((derivedHom C X).flip.obj M).obj (op K)) n ≫
        (derivedTensorHomAdjunction C (X := X) K).counit.app M =
      (derivedTensorHomAdjunction C (X := X) (K⟦-n⟧)).counit.app M := by
  exact h K n

/-- Derived tensor-Hom comparison respects normalized shifts.
Source: Stacks Project, Tags 08JC and 08J9; blueprint `lemma-change-coefficients-internal-hom--1`,
proof paragraph 2.

Proof. Apply the abstract tensor-Hom evaluation chase to the derived tensor and Hom
bifunctors. First-variable adjunction naturality and tensor-shift cancellation naturality
supply its two categorical compatibility hypotheses; the other hypotheses are given.
The abstract chase cancels the target Hom shift and the tensor image of the first scalar
shift, then uses cancellation naturality, the evaluation-transpose equation, scalar tensor
cancellation, binary comparison naturality, and the source evaluation normalization.
Adjunction injectivity recovers the shift square.
(blueprint: lem-coef-tensor-hom-shift-comparison-component) -/
theorem derivedTensorHomShiftComparison_component
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [SymmetricCategory D] [Abelian.HasFunctorialFlatResolution D]
    (X : Scheme.{u})
    (F : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology D)) [F.Additive] [F.CommShift ℤ]
    (μ : ∀ K L, ((derivedTensor D X).obj (F.obj K)).obj (F.obj L) ≅
      F.obj (((derivedTensor C X).obj K).obj L))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (v : (derivedHom C X).flip.obj M ⋙ F ⟶ F.op ⋙ (derivedHom D X).flip.obj (F.obj M))
    (hv : ∀ K, (μ K (((derivedHom C X).obj (op K)).obj M)).hom ≫
      F.map ((derivedTensorHomAdjunction C (X := X) K).counit.app M) =
      ((derivedTensorHomAdjunction D (X := X) (F.obj K)).homEquiv
        (((derivedHom C X).flip.obj M ⋙ F).obj (op K)) (F.obj M)).symm (v.app (op K)))
    (sA : ((derivedHom C X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom D X).flip.obj (F.obj M)).CommShift ℤ)
    (hA : EtaleHomShiftNormalization C X M sA)
    (hB : EtaleHomShiftNormalization D X (F.obj M) sB)
    (hμ : ∀ K L L' (g : L ⟶ L'),
      ((derivedTensor D X).obj (F.obj K)).map (F.map g) ≫ (μ K L').hom =
        (μ K L).hom ≫ F.map (((derivedTensor C X).obj K).map g))
    (hs : ∀ K L (n : ℤ),
      ((derivedTensor D X).map ((F.commShiftIso (-n)).hom.app K)).app (F.obj (L⟦n⟧)) ≫
        ((derivedTensor D X).obj ((F.obj K)⟦-n⟧)).map ((F.commShiftIso n).hom.app L) ≫
        etaleHomTensorShiftCancellation D X (F.obj K) (F.obj L) n ≫ (μ K L).hom =
      (μ (K⟦-n⟧) (L⟦n⟧)).hom ≫ F.map (etaleHomTensorShiftCancellation C X K L n))
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (n : ℤ) :
    (F.map ((sA.commShiftIso n).hom.app (op K)) ≫
      (F.commShiftIso n).hom.app (((derivedHom C X).flip.obj M).obj (op K))) ≫
      (v.app (op K))⟦n⟧' =
    v.app (op (K⟦-n⟧)) ≫ ((derivedHom D X).flip.obj (F.obj M)).map
      (((F.commShiftIso (-n)).inv.app K).op) ≫
      (sB.commShiftIso n).hom.app (op (F.obj K)) := by
  exact tensorHomShiftComparison_aux F
    (derivedTensor C X) (derivedHom C X) (derivedTensor D X) (derivedHom D X)
    (derivedTensorHomAdjunction C (X := X)) (derivedTensorHomAdjunction D (X := X))
    μ (etaleHomTensorShiftCancellation C X) (etaleHomTensorShiftCancellation D X)
    M v hv sA sB K n (etaleHomShiftNormalization_apply C X M sA hA K n)
    (etaleHomShiftNormalization_apply D X (F.obj M) sB hB (F.obj K) n)
    (fun K L P f g ↦ etaleTensorHomTranspose_naturality D X K L (F.obj M) P f g)
    (fun K L L' g n ↦ etaleHomTensorShiftCancellation_naturality D X K g n)
    hμ hs

end AlgebraicGeometry.Etale
