/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
public import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.AlgebraicGeometry.RingCechCoordinateTensorStep
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-! # Ordered coordinates of the tensor localization complex over a ring

Source: Stacks Project, algebraization.tex, Tags 0996 and 099D(d).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite
open scoped BigOperators
namespace CategoryTheory

/-- An element of a ring as a section of its one-point ring sheaf.
Source: Stacks Project, Tag 0996.
(auxiliary; not a blueprint node). -/
def ringTensorCechSection (A : CommRingCat.{u}) (x : A) :
    ((CochainComplex.onePointRingSheaf A).obj ⋙ forget CommRingCat).sections :=
  ⟨fun _ ↦ x, fun _ ↦ rfl⟩

/-- The actual ordered tensor of the two-term localization complexes on the ring site.
This uses the existing tensor construction, with its existing augmentation.
Source: Stacks Project, Tag 0996.
(auxiliary; not a blueprint node). -/
def ringTensorCech (A : CommRingCat.{u}) (r : ℕ) (f : Fin r → A) :
    Σ K : CochainComplex (RingSiteModules A) ℤ, K ⟶ ringComplexSingle A :=
  ringedExtendedCech (CochainComplex.onePointRingSheaf A) r
    (fun i ↦ ringTensorCechSection A (f i))

private theorem tensorZero_ι_isIso
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    (K L : CochainComplex D ℤ) [HomologicalComplex.HasTensor K L]
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] :
    IsIso (HomologicalComplex.ιTensorObj K L 0 0 0 rfl) := by
  classical
  let p : (HomologicalComplex.tensorObj K L).X 0 ⟶
      MonoidalCategory.tensorObj (K.X 0) (L.X 0) :=
    HomologicalComplex.mapBifunctorDesc (fun i j _ ↦
      if h : i = 0 ∧ j = 0 then
        eqToHom (by obtain ⟨rfl, rfl⟩ := h; rfl) else 0)
  have hp : HomologicalComplex.ιTensorObj K L 0 0 0 rfl ≫ p = 𝟙 _ := by
    dsimp only [p, HomologicalComplex.ιTensorObj]
    rw [HomologicalComplex.ι_mapBifunctorDesc]
    simp
  have hp' : p ≫ HomologicalComplex.ιTensorObj K L 0 0 0 rfl = 𝟙 _ := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j hij
    by_cases h : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h
      simpa only [Category.assoc, Category.id_comp, Category.comp_id]
        using congrArg (fun z ↦ z ≫ HomologicalComplex.ιTensorObj K L 0 0 0 rfl) hp
    · apply IsZero.eq_of_src
      have hij' : i + j = 0 := hij
      by_cases hi : i < 0
      · exact ((MonoidalCategory.curriedTensor D).map_isZero
          (K.isZero_of_isStrictlyGE 0 i hi)).obj _
      · exact ((MonoidalCategory.curriedTensor D).obj _).map_isZero
          (L.isZero_of_isStrictlyGE 0 j (by omega))
  exact ⟨⟨p, hp, hp'⟩⟩

private theorem tensorHom_zero_isIso
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    {K L K' L' : CochainComplex D ℤ}
    [HomologicalComplex.HasTensor K L] [HomologicalComplex.HasTensor K' L']
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] [K'.IsStrictlyGE 0] [L'.IsStrictlyGE 0]
    (f : K ⟶ K') (g : L ⟶ L') [IsIso (f.f 0)] [IsIso (g.f 0)] :
    IsIso ((HomologicalComplex.tensorHom f g).f 0) := by
  let := tensorZero_ι_isIso K L
  let := tensorZero_ι_isIso K' L'
  have h : HomologicalComplex.ιTensorObj K L 0 0 0 rfl ≫
      (HomologicalComplex.tensorHom f g).f 0 =
      (f.f 0 ⊗ₘ g.f 0) ≫ HomologicalComplex.ιTensorObj K' L' 0 0 0 rfl :=
    by
      simpa only [tensorHom_def_assoc, curriedTensor_map_app, curriedTensor_obj_map]
        using HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor D) (.up ℤ)
          0 0 0 rfl
  have : IsIso (HomologicalComplex.ιTensorObj K L 0 0 0 rfl ≫
      (HomologicalComplex.tensorHom f g).f 0) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left (HomologicalComplex.ιTensorObj K L 0 0 0 rfl) _

private theorem ringTensorCech_nonnegative (A : CommRingCat.{u}) (r : ℕ)
    (f : Fin r → A) :
    ((ringTensorCech A r f).1).IsStrictlyGE 0 := by
  let O := CochainComplex.onePointRingSheaf A
  let : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  induction r with
  | zero =>
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A) n
      (by omega)
  | succ r ih =>
    let P := ringedLocalizationTwoTerm O (ringTensorCechSection A (f 0))
    have : P.IsStrictlyGE 0 := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      change IsZero (ringedLocalizationTwoTermX O (ringTensorCechSection A (f 0)) n)
      simp only [ringedLocalizationTwoTermX, show n ≠ 0 by omega,
        show n ≠ 1 by omega, ↓reduceIte]
      exact Limits.isZero_zero _
    let := ih (fun i ↦ f i.succ)
    exact CochainComplex.isStrictlyGE_tensorObj P
      (ringTensorCech A r (fun i ↦ f i.succ)).1 0 0

private theorem ringTensorCech_augmentation_zero_isIso (A : CommRingCat.{u})
    (r : ℕ) (f : Fin r → A) : IsIso ((ringTensorCech A r f).2.f 0) := by
  let O := CochainComplex.onePointRingSheaf A
  let : IsGrothendieckAbelian.{u} (RingSiteModules A) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  have hsingle : (ringComplexSingle A).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A) n
      (by omega)
  induction r with
  | zero =>
    change IsIso (𝟙 _)
    infer_instance
  | succ r ih =>
    let s := ringTensorCechSection A (f 0)
    let P := ringedLocalizationTwoTerm O s
    let a := ringedLocalizationTwoTermAugmentation O s
    have : P.IsStrictlyGE 0 := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro n hn
      change IsZero (ringedLocalizationTwoTermX O s n)
      simp only [ringedLocalizationTwoTermX, show n ≠ 0 by omega,
        show n ≠ 1 by omega, ↓reduceIte]
      exact Limits.isZero_zero _
    have : IsIso (a.f 0) := by
      change IsIso (ringedLocalizationTwoTermAugmentationF O s 0)
      simp only [ringedLocalizationTwoTermAugmentationF, ↓reduceDIte,
        eqToHom_refl, Category.id_comp, Category.comp_id]
      infer_instance
    let := ringTensorCech_nonnegative A r (fun i ↦ f i.succ)
    let := ih (fun i ↦ f i.succ)
    let := tensorHom_zero_isIso a (ringTensorCech A r (fun i ↦ f i.succ)).2
    change IsIso ((HomologicalComplex.tensorHom a
      (ringTensorCech A r (fun i ↦ f i.succ)).2 ≫
        (HomologicalComplex.leftUnitor (ringComplexSingle A)).hom).f 0)
    rw [HomologicalComplex.comp_f]
    infer_instance

/-- The tensor complex over a ring has the ordered localization coordinates.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099D(d).
(auxiliary; not a blueprint node).

Proof: evaluation on the one-object bottom-topology site identifies module sheaves
with A-modules, their tensor with module tensor, and sheafification with the identity.
Induct on r in the actual recursive tensor construction. A summand in degree n
chooses n factors in degree one and the remaining factors in degree zero. Sort the
chosen indices to identify it with an order embedding Fin n into Fin r. The
localization universal property identifies the tensor of their localizations with
localization at their product: the forward map multiplies fractions, and the inverse
sends a/product(f_i)^k to the tensor with numerator a in one factor and denominators
f_i^k in all factors. These formulas also cover zero generators and the zero ring.
The tensor differential inserts one missing index; its Koszul sign is the number of
chosen preceding indices, precisely the index of the deleted element in the target
ordered subset. This proves the two displayed differential formulas. Finite direct
sums are finite products. No negative-degree summand occurs. In degree zero all
factors are A and multiplication identifies their tensor with A. The tensor of the
factor projections followed by the unit constraint is this identification, proving
the augmentation equation. For r=0 the tensor is A[0], with zero empty positive
products and the identity augmentation. Repeated generators cause no change to the
indexing or the fraction identities. -/
theorem ringTensorCech_coordinates (A : CommRingCat.{u}) (r : ℕ) (f : Fin r → A) :
    let K := (ringTensorCech A r f).1
    let a := (ringTensorCech A r f).2
    ∃ (e₀ : (K.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A)
      (e : ∀ q : ℕ, (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
        ((t : Fin (q + 1) ↪o Fin r) → Localization.Away (∏ i, f (t i))))
      (l : ∀ (q : ℕ) (t : Fin (q + 2) ↪o Fin r) (j : Fin (q + 2)),
        Localization.Away (∏ i, f (t (Fin.succAboveOrderEmb j i))) →ₐ[A]
          Localization.Away (∏ i, f (t i))),
      (∀ n : ℤ, n < 0 → CategoryTheory.Limits.IsZero (K.X n)) ∧
      (∀ (x : (K.X 0).val.obj (op ⟨PUnit.unit⟩)) (t : Fin 1 ↪o Fin r),
        e 0 ((K.d 0 1).val.app (op ⟨PUnit.unit⟩) x) t =
          algebraMap A (Localization.Away (∏ i, f (t i))) (e₀ x)) ∧
      (∀ (q : ℕ) (x : (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩))
        (t : Fin (q + 2) ↪o Fin r),
        e (q + 1) ((K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).val.app (op ⟨PUnit.unit⟩) x) t =
          ∑ j : Fin (q + 2), (-1 : ℤ) ^ j.val •
            l q t j (e q x ((Fin.succAboveOrderEmb j).trans t))) ∧
      (∀ x : (K.X 0).val.obj (op ⟨PUnit.unit⟩),
        ringComplexAugmentationValue a x = e₀ x) := by
  classical
  induction r with
  | zero =>
    dsimp only
    let K := (ringTensorCech A 0 f).1
    let ev : RingSiteModules A ⥤ ModuleCat.{u} A := SheafOfModules.evaluation
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)) (op ⟨PUnit.unit⟩)
    let e₀ : (K.X 0).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A] A :=
      (ev.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (ringComplexUnit A))).toLinearEquiv
    have hz (q : ℕ) : IsZero (K.X ((q : ℤ) + 1)) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A) _ (by omega)
    have : ev.Additive := { map_add := fun {_ _ _ _} ↦ rfl }
    have hs (q : ℕ) : Subsingleton ((K.X ((q : ℤ) + 1)).val.obj
        (op ⟨PUnit.unit⟩)) :=
      ModuleCat.subsingleton_of_isZero (ev.map_isZero (hz q))
    let e (q : ℕ) : (K.X ((q : ℤ) + 1)).val.obj (op ⟨PUnit.unit⟩) ≃ₗ[A]
        ((t : Fin (q + 1) ↪o Fin 0) → Localization.Away (∏ i, f (t i))) := by
      letI := hs q
      haveI : IsEmpty (Fin (q + 1) ↪o Fin 0) := ⟨fun t ↦ Fin.elim0 (t 0)⟩
      exact LinearEquiv.ofSubsingleton _ _
    refine ⟨e₀, e, (fun q t j ↦ Fin.elim0 (t 0)), ?_, ?_, ?_, ?_⟩
    · intro n hn
      exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ringComplexUnit A) n
        (by omega)
    · intro x t
      exact Fin.elim0 (t 0)
    · intro q x t
      exact Fin.elim0 (t 0)
    · intro x
      change ((HomologicalComplex.id (ringComplexSingle A)).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A)).hom).val.app
          (op ⟨PUnit.unit⟩) x = _
      rfl
  | succ r ih =>
    obtain ⟨e₀, e, l, hneg, hd₀, hd, ha⟩ := ih (fun i ↦ f i.succ)
    obtain ⟨e', l', hd₀', hd'⟩ := ringCechCoordinates_tensor_step A r f
      (ringTensorCech A r (fun i ↦ f i.succ)).1
      (ringTensorCech A r (fun i ↦ f i.succ)).2 e₀ e l hneg hd₀ hd ha
    let := ringTensorCech_augmentation_zero_isIso A (r + 1) f
    let ev : RingSiteModules A ⥤ ModuleCat.{u} A := SheafOfModules.evaluation
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)) (op ⟨PUnit.unit⟩)
    let e₀' := (ev.mapIso (asIso ((ringTensorCech A (r + 1) f).2.f 0) ≪≫
      HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ringComplexUnit A))).toLinearEquiv
    refine ⟨e₀', e', l', ?_, hd₀', hd', ?_⟩
    · let := ringTensorCech_nonnegative A (r + 1) f
      exact fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn
    · intro x
      rfl

end CategoryTheory
