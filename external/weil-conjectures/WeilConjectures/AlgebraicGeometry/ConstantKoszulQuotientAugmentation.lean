/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantKoszulAugmentationConstruction
import all WeilConjectures.AlgebraicGeometry.FlatLocalizationKoszulHomotopy
import all WeilConjectures.AlgebraicGeometry.OrderedKoszulHomologyTorsion
import WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import WeilConjectures.CategoryTheory.RingedNegativeKoszulLowDegrees

/-! # The normalized strict Koszul-to-quotient augmentation

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion), proof.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open MonoidalCategory

private theorem quotientDualLowDegrees
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℕ) :
    let U := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let D := (ringedKoszulDualTower O r s).obj (op n)
    ∃ (e₀ : D.X 0 ≅ U) (e₁ : (⨁ fun _ : Fin r ↦ U) ≅ D.X (-1)),
      (ringedKoszulDualUnit O r s n).f 0 ≫ e₀.hom =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 U).hom ∧
      ∀ i : Fin r, biproduct.ι _ i ≫ e₁.hom ≫ D.d (-1) 0 ≫ e₀.hom =
        ((ringedKoszulScalar O (s i)) ^ (n + 1)).asHom := by
  obtain ⟨e, _, hu⟩ :
      ∃ e : ∀ m : ℕ, ringedNegativeKoszul O r s m ≅
          (ringedKoszulDualTower O r s).obj (op m),
        (∀ m, ringedNegativeKoszulTransition O r s m ≫ (e m).hom =
          (e (m + 1)).hom ≫ (ringedKoszulDualTower O r s).map
            (homOfLE (Nat.le_succ m)).op) ∧
        (∀ m, ringedNegativeKoszulBasis O r s m ∅ 0 ≫ (e m).hom.f 0 =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
            (ringedKoszulDualUnit O r s m).f 0) := by
    cases r with
    | zero => exact ringedNegativeKoszulZeroDuality O s
    | succ r => exact ringedNegativeKoszulSuccDuality O r s
  obtain ⟨e₀, e₁, h₀, h₁⟩ := ringedNegativeKoszulLowDegrees O r s n
  let d₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso (e n)
  let d₁ := (HomologicalComplex.eval _ (.up ℤ) (-1)).mapIso (e n)
  refine ⟨d₀.symm ≪≫ e₀, e₁ ≪≫ d₁, ?_, ?_⟩
  · have hh := hu n
    rw [← h₀] at hh
    apply (cancel_epi (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv).1
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← reassoc_of% hh]
    change e₀.inv ≫ d₀.hom ≫ d₀.inv ≫ e₀.hom = 𝟙 _
    simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  · intro i
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have ht := (e n).hom.comm (-1) 0
    change d₁.hom ≫ _ = _ ≫ d₀.hom at ht
    change _ ≫ _ ≫ d₁.hom ≫ _ ≫ d₀.inv ≫ _ = _
    rw [reassoc_of% ht, Iso.hom_inv_id_assoc]
    exact h₁ i

end CategoryTheory

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A) (b : Bool)
variable (r : ℕ) (a : Fin r → A)

open MonoidalCategory SheafOfModules.LocalizationCech

private theorem finiteMap_base (n : ℕ) :
    baseMap J A I b ≫ finiteMap J A I b n = quotient J A I n := by
  cases b with
  | false => exact Category.id_comp _
  | true => exact limit.lift_π (quotientCone J A I) (op n)

private theorem quotient_constantSection (n : ℕ) (x : A) (U : Cᵒᵖ) :
    (quotient J A I n).hom.app U ((constantSection (J := J) x).val U) =
      (constantSection (J := J) (Ideal.Quotient.mk (I ^ (n + 1)) x)).val U := by
  have hn := toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  exact (congrArg (fun k ↦ k.app U x) hn).symm

private theorem finiteMap_power_zero (ha : Ideal.span (Set.range a) = I)
    (n : ℕ) (i : Fin r) (U : Cᵒᵖ) :
    (finiteMap J A I b n).hom.app U
      ((algebraSection (baseMap J A I b) (a i)).val U ^ (n + 1)) = 0 := by
  have hi : a i ∈ I := by rw [← ha]; exact Ideal.subset_span ⟨i, rfl⟩
  have hp : Ideal.Quotient.mk (I ^ (n + 1)) (a i ^ (n + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hi _)
  change (finiteMap J A I b n).hom.app U
    ((baseMap J A I b).hom.app U ((constantSection (J := J) (a i)).val U) ^ (n + 1)) = 0
  rw [← map_pow]
  have hpow : (constantSection (J := J) (a i)).val U ^ (n + 1) =
      (constantSection (J := J) (a i ^ (n + 1))).val U := by
    exact (((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U).hom.map_pow
      _ _).symm
  rw [hpow]
  change ((baseMap J A I b ≫ finiteMap J A I b n).hom.app U)
    ((constantSection (J := J) (a i ^ (n + 1))).val U) = 0
  rw [finiteMap_base, quotient_constantSection, hp]
  exact ((toSheafify J ((Functor.const Cᵒᵖ).obj
    (CommRingCat.of (A ⧸ I ^ (n + 1))))).app U).hom.map_zero

private theorem reduction_scalar_zero (ha : Ideal.span (Set.range a) = I)
    (n : ℕ) (i : Fin r) (M : Mod (coefficients J A I b)) :
    (sectionScalarNat (coefficients J A I b)
      ⟨(algebraSection (baseMap J A I b) (a i)).val,
        (algebraSection (baseMap J A I b) (a i)).property⟩ (n + 1)).app
          ((reduction J A I b n).obj M) = 0 := by
  let N := (change (finiteMap J A I b n)).obj M
  ext U x
  change ((finiteMap J A I b n).hom.app U
    ((algebraSection (baseMap J A I b) (a i)).val U ^ (n + 1))) •
      (show N.val.obj U from x) = (0 : N.val.obj U)
  rw [finiteMap_power_zero J A I b r a ha n i U, zero_smul]

private theorem reduction_tensor_scalar_zero (ha : Ideal.span (Set.range a) = I)
    (n : ℕ) (i : Fin r) (M : Mod (coefficients J A I b))
    (η : 𝟭 (Mod (coefficients J A I b)) ⟶ reduction J A I b n) :
    let := SheafOfModules.monoidalCategory (coefficients J A I b)
    M ◁ ((ringedKoszulScalar (coefficients J A I b)
      (algebraSection (baseMap J A I b) (a i))) ^ (n + 1)).asHom ≫
        (ρ_ M).hom ≫ η.app M = 0 := by
  let O := coefficients J A I b
  let s : (SheafOfModules.unit (rings O)).sections :=
    ⟨(algebraSection (baseMap J A I b) (a i)).val,
      (algebraSection (baseMap J A I b) (a i)).property⟩
  let z := sectionScalarNat O s (n + 1)
  let := SheafOfModules.monoidalCategory O
  have hs : z.app (SheafOfModules.unit (rings O)) =
      ((ringedKoszulScalar O (algebraSection (baseMap J A I b) (a i))) ^ (n + 1)).asHom :=
    sectionScalarNat_unit O s (n + 1)
  change M ◁ _ ≫ (ρ_ M).hom ≫ η.app M = 0
  rw [← hs]
  change M ◁ (sectionScalarNat O s (n + 1)).app (𝟙_ (Mod O)) ≫
    (ρ_ M).hom ≫ η.app M = 0
  rw [sectionScalarNat_tensor_right]
  change z.app _ ≫ (ρ_ M).hom ≫ η.app M = 0
  have hρ := z.naturality (ρ_ M).hom
  have hη := z.naturality (η.app M)
  simp only [Functor.id_map] at hρ hη
  change η.app M ≫ z.app _ = z.app M ≫ η.app M at hη
  rw [← reassoc_of% hρ]
  calc
    (ρ_ M).hom ≫ z.app M ≫ η.app M =
        (ρ_ M).hom ≫ η.app M ≫ z.app ((reduction J A I b n).obj M) :=
      congrArg ((ρ_ M).hom ≫ ·) hη.symm
    _ = 0 := by
      rw [show z.app ((reduction J A I b n).obj M) = 0 from
        reduction_scalar_zero J A I b r a ha n i M, comp_zero, comp_zero]

private theorem tensor_boundary_zero
    (O : Sheaf J CommRingCat.{u}) (D : ringedSiteComplex O)
    (e₀ : D.X 0 ≅ SheafOfModules.unit (rings O))
    (e₁ : (⨁ fun _ : Fin r ↦ SheafOfModules.unit (rings O)) ≅ D.X (-1))
    (s : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℕ)
    (he : ∀ i : Fin r, biproduct.ι _ i ≫ e₁.hom ≫ D.d (-1) 0 ≫ e₀.hom =
      ((ringedKoszulScalar O (s i)) ^ (n + 1)).asHom)
    (F : Mod O ⥤ Mod O) (η : 𝟭 (Mod O) ⟶ F)
    (hz : ∀ (i : Fin r) (M : Mod O),
      let := SheafOfModules.monoidalCategory O
      M ◁ ((ringedKoszulScalar O (s i)) ^ (n + 1)).asHom ≫
        (ρ_ M).hom ≫ η.app M = 0) (M : Mod O) :
    let := SheafOfModules.monoidalCategory O
    M ◁ (D.d (-1) 0 ≫ e₀.hom) ≫ (ρ_ M).hom ≫ η.app M = 0 := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let T := tensorLeft M
  apply (cancel_epi (T.map e₁.hom)).1
  apply (isColimitOfPreserves T (biproduct.isColimit
    (fun _ : Fin r ↦ SheafOfModules.unit (rings O)))).hom_ext
  intro ⟨i⟩
  change M ◁ (biproduct.ι _ i) ≫ M ◁ e₁.hom ≫
      M ◁ (D.d (-1) 0 ≫ e₀.hom) ≫ (ρ_ M).hom ≫ η.app M = _
  simp only [← whiskerLeft_comp_assoc, he, comp_zero]
  exact hz i M

/-- The strict augmentation preserves the actual ordinary-limit unit and vanishes on
all tensor summands of nonzero Koszul degree. These formulas normalize the augmentation,
without involving any presentation or derived completion functor.
Source: Stacks Project, Tag 099M, proof.
(auxiliary; not a blueprint node). -/
def KoszulQuotientAugmentationLaws
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ)) : Prop :=
  (∀ P : Cx (coefficients J A I b),
    ringedKoszulLimitUnit (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) P ≫
      (ordinaryLimit (coefficients J A I b)).map (α.app P) = ordinaryUnit J A I b P) ∧
  (∀ (P : Cx (coefficients J A I b)) (n : ℕ) (p q : ℤ), q ≠ 0 →
    HomologicalComplex.ιMapBifunctor P
        ((ringedKoszulDualTower (coefficients J A I b) r
          (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n))
        (@MonoidalCategory.curriedTensor _ _
          (SheafOfModules.monoidalCategory (coefficients J A I b)))
        (.up ℤ) p q (p + q) rfl ≫ ((α.app P).f (p + q)).app (op n) = 0)

/-- The degree-zero quotient defines a natural strict tower augmentation, including
its normalization on total-tensor summands. No Noetherian assumption is needed here.
Source: Stacks Project, Tag 099M (lemma-naive-completion), construction in the proof;
More on Algebra, Tag 0913, the tensor description of the Koszul complex.
(auxiliary; not a blueprint node).

Proof: dualize the ordered positive Koszul tensor factors. The resulting negative
complex has its coefficient sheaf in degree zero, and its differential into degree
zero is generated by the powers of the given sections. Send degree zero to the
specified finite quotient sheaf and every negative degree to zero. Each generator
power vanishes in I^(n+1), so this is a chain map. Dual transitions act identically in
degree zero; the quotient transitions therefore make these chain maps a strict tower
map. Tensor with P and use the balancing isomorphism from P tensor the finite quotient
to restriction of scalar extension of P. The map on the summand of Koszul degree zero
is this balancing map followed by the quotient, and all other summands map to zero.
The coproduct universal property proves naturality in P. The degree-zero unit sends
p to p tensor 1, which goes to 1 tensor p, the actual reduction unit. Composing with
every ordinary-limit projection proves the asserted unit equation. For r=0 the map
is precisely the quotient of the empty tensor, and for the zero ring all terms vanish. -/
theorem koszulQuotientAugmentation (ha : Ideal.span (Set.range a) = I) :
    ∃ α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ),
      KoszulQuotientAugmentationLaws J A I b r a α := by
  classical
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let D := ringedKoszulDualTower O r s
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  have hlow := fun n ↦ quotientDualLowDegrees O r s n
  choose e₀ e₁ hu hd using hlow
  let η := quotientReductionUnit J A I b
  have hz (n : ℕ) (M : Mod O) :
      M ◁ ((D.obj (op n)).d (-1) 0 ≫ (e₀ n).hom) ≫
        (ρ_ M).hom ≫ (η n).app M = 0 :=
    tensor_boundary_zero J r O (D.obj (op n)) (e₀ n) (e₁ n) s n (hd n)
      (reduction J A I b n) (η n)
      (fun i M ↦ reduction_tensor_scalar_zero J A I b r a ha n i M (η n)) M
  have hdual {m k : ℕᵒᵖ} (f : m ⟶ k) :
      ringedKoszulDualUnit O r s k.unop =
        ringedKoszulDualUnit O r s m.unop ≫ D.map f := by
    dsimp [ringedKoszulDualUnit, D, ringedKoszulDualTower]
    rw [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      ringedKoszulProjection_naturality]
  have he {m k : ℕᵒᵖ} (f : m ⟶ k) :
      (D.map f).f 0 ≫ (e₀ k.unop).hom = (e₀ m.unop).hom := by
    apply (cancel_epi (e₀ m.unop).inv).1
    have hinv (n : ℕ) : (e₀ n).inv =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r s n).f 0 := by
      apply (cancel_mono (e₀ n).hom).1
      rw [Iso.inv_hom_id, Category.assoc, hu, Iso.inv_hom_id]
    rw [hinv]
    have hf := congrArg (fun g ↦ g.f 0) (hdual f)
    simp only [HomologicalComplex.comp_f] at hf
    rw [Category.assoc, ← Category.assoc ((ringedKoszulDualUnit O r s m.unop).f 0),
      ← hf]
    simp only [Category.assoc, hu, Iso.inv_hom_id]
  exact constantKoszulAugmentationFromLowDegrees J A I b r a e₀ hz he hu

end CategoryTheory.ConstantCompletion
