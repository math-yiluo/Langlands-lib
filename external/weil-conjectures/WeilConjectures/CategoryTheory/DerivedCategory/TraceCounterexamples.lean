/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Counterexamples for the categorical trace in the derived category

Let `ℓ` be a prime and `A = ℤ/ℓ²`. This file formalizes two blueprint statements showing that
the categorical trace in `D(A)` (for the Koszul braiding `DerivedCategory.braidedCategory'`) is
not as well behaved as over a field.

## Main results

- `DerivedCategory.trace_not_determined_by_homology` (blueprint
  `example-trace-not-determined-cohomology`): on the perfect complex `P = [A --ℓ--> A]` in
  degrees `0` and `1`, the endomorphisms `1_P = (1, 1)` and `v = (1 + ℓ, 1)` induce the same
  maps (the identity) on cohomology, but `tr (1_P ∣ P) = 0` and `tr (v ∣ P) = ℓ ≠ 0`.
- `DerivedCategory.exists_triangle_endomorphism_trace_ne_add` (blueprint
  `remark-coherent-additivity`): there are a distinguished triangle `T` of dualizable objects of
  `D(A)` and an endomorphism `φ : T ⟶ T` of triangles with
  `tr φ.hom₂ ≠ tr φ.hom₁ + tr φ.hom₃`.

## Implementation notes

The triangle is the one attached to the degreewise split short exact sequence
`0 ⟶ A[-1] ⟶ P ⟶ A ⟶ 0`, and `φ = (1, v, 1)`. The square `A[-1] ⟶ P` commutes on the nose,
but the square `P ⟶ A` only commutes up to the homotopy `id : P¹ = A ⟶ A`, so `φ` does not come
from an endomorphism of the short exact sequence. The traces are `-1`, `ℓ` and `1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

namespace DerivedCategory

section General

variable {R : Type u} [CommRing R]

private lemma free_finite_of_isZero_or_iso {M : ModuleCat.{u} R}
    (h : IsZero M ∨ Nonempty (M ≅ ModuleCat.of R R)) :
    Module.Free R M ∧ Module.Finite R M := by
  obtain h | h := h
  · have := ModuleCat.subsingleton_of_isZero h
    exact ⟨Module.Free.of_subsingleton R M, inferInstance⟩
  · obtain ⟨e⟩ := h
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

private lemma homologyMap_eq_zero_of_iCycles_comp {C ι : Type*} [Category C]
    [HasZeroMorphisms C] {c : ComplexShape ι} {K L : HomologicalComplex C c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] (h : K.iCycles i ≫ φ.f i = 0) :
    HomologicalComplex.homologyMap φ i = 0 := by
  have : HomologicalComplex.cyclesMap φ i = 0 := by
    rw [← cancel_mono (L.iCycles i), HomologicalComplex.cyclesMap_i, h, zero_comp]
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality, this, zero_comp,
    comp_zero]

private lemma linearMapTrace_smul_id [Nontrivial R] {M : ModuleCat.{u} R} [Module.Free R M]
    [Module.Finite R M] (e : M ≅ ModuleCat.of R R) (c : R) :
    LinearMap.trace R M (ModuleCat.Hom.hom (c • 𝟙 M)) = c := by
  rw [ModuleCat.hom_smul, ModuleCat.hom_id, map_smul, LinearMap.trace_id,
    e.toLinearEquiv.finrank_eq, Module.finrank_self, Nat.cast_one, smul_eq_mul, mul_one]

variable [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- A bounded complex of finite free modules is dualizable in `D(R)`. -/
lemma nonempty_hasRightDual_Q_obj [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hfree : ∀ i, Module.Free R (K.X i)) (hfin : ∀ i, Module.Finite R (K.X i)) :
    Nonempty (HasRightDual (Q.obj K)) := by
  let _ (n : ℤ) : HasRightDual (K.X n) := ModuleCat.hasRightDualOfFree (K.X n)
  obtain ⟨e⟩ := nonempty_exactPairing_Q_obj_rightDual K a b
  exact ⟨⟨Q.obj K.rightDual⟩⟩

/-- The canonical map `R → End (𝟙_ D(R))` is injective. -/
lemma algebraMap_end_unit_injective [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)] :
    Function.Injective (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R))))) := by
  intro r r' h
  replace h := congr($(h).asHom)
  rw [← ε_Qh_comp_map_single_map_algebraMap_comp_inv,
    ← ε_Qh_comp_map_single_map_algebraMap_comp_inv] at h
  replace h := (cancel_mono (inv (Functor.LaxMonoidal.ε Qh))).1
    ((cancel_epi (Functor.LaxMonoidal.ε Qh)).1 h)
  have key (x : 𝟙_ (ModuleCat.{u} R) ⟶ 𝟙_ (ModuleCat.{u} R)) :
      (singleFunctor (ModuleCat.{u} R) 0).map x =
        (quotientCompQhIso _).inv.app _ ≫ Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).map x)) ≫
          (quotientCompQhIso _).hom.app _ :=
    (NatIso.naturality_1 (quotientCompQhIso _) _).symm
  have h₃ := congrArg (fun f : 𝟙_ (ModuleCat.{u} R) ⟶ 𝟙_ (ModuleCat.{u} R) ↦ f.hom 1)
    ((singleFunctor (ModuleCat.{u} R) 0).map_injective
      ((key _).trans ((congrArg (fun f ↦ _ ≫ f ≫ _) h).trans (key _).symm)))
  simp only [Algebra.algebraMap_eq_smul_one, End.smul_asHom, End.one_asHom] at h₃
  change (r • 𝟙 (ModuleCat.of R R)).hom 1 = (r' • 𝟙 (ModuleCat.of R R)).hom 1 at h₃
  simpa using h₃

end General

section Counterexample

variable (ℓ : ℕ)

namespace TraceCounterexample

lemma natCast_mul_self_eq_zero : (ℓ : ZMod (ℓ ^ 2)) * ℓ = 0 := by
  rw [← Nat.cast_mul, ← sq, ZMod.natCast_self]

lemma fact_one_lt_sq [Fact ℓ.Prime] : Fact (1 < ℓ ^ 2) :=
  ⟨Nat.one_lt_pow two_ne_zero (Fact.out : ℓ.Prime).one_lt⟩

lemma natCast_ne_zero_of_sq [Fact ℓ.Prime] : (ℓ : ZMod (ℓ ^ 2)) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  intro h
  have h₁ := (Fact.out : ℓ.Prime).one_lt
  have h₂ := Nat.le_of_dvd (by omega) h
  nlinarith

lemma rel_zero_one : (ComplexShape.up ℤ).Rel 0 1 := by simp

/-- The complex `P = [A --ℓ--> A]` over `A = ℤ/ℓ²`, in degrees `0` and `1`. -/
noncomputable abbrev complexMulNat : CochainComplex (ModuleCat.{0} (ZMod (ℓ ^ 2))) ℤ :=
  HomologicalComplex.double
    ((ℓ : ZMod (ℓ ^ 2)) • 𝟙 (ModuleCat.of (ZMod (ℓ ^ 2)) (ZMod (ℓ ^ 2)))) rel_zero_one

/-- The endomorphism `v = (1 + ℓ, 1)` of `P = [A --ℓ--> A]`. -/
noncomputable def endComplexMulNat : complexMulNat ℓ ⟶ complexMulNat ℓ :=
  HomologicalComplex.mkHomFromDouble _ zero_ne_one
    ((1 + ℓ : ZMod (ℓ ^ 2)) • (HomologicalComplex.doubleXIso₀ _ _).inv)
    (HomologicalComplex.doubleXIso₁ _ _ zero_ne_one).inv (by
      rw [HomologicalComplex.double_d _ _ zero_ne_one, Linear.smul_comp, Iso.inv_hom_id_assoc]
      simp only [Linear.smul_comp, Category.id_comp, smul_smul, add_mul, one_mul,
        natCast_mul_self_eq_zero, add_zero])
    (fun k _ ↦ by
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ one_ne_zero, Limits.comp_zero])

lemma endComplexMulNat_f_zero :
    (endComplexMulNat ℓ).f 0 = (1 + ℓ : ZMod (ℓ ^ 2)) • 𝟙 _ := by
  simp [endComplexMulNat]

lemma endComplexMulNat_f_one : (endComplexMulNat ℓ).f 1 = 𝟙 _ := by
  simp [endComplexMulNat]

lemma endComplexMulNat_sub_id_f_zero :
    (endComplexMulNat ℓ - 𝟙 _).f 0 = (ℓ : ZMod (ℓ ^ 2)) • 𝟙 _ := by
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, endComplexMulNat_f_zero, add_smul,
    one_smul, add_sub_cancel_left]

lemma isZero_complexMulNat_X (i : ℤ) (h₀ : i ≠ 0) (h₁ : i ≠ 1) :
    IsZero ((complexMulNat ℓ).X i) :=
  HomologicalComplex.isZero_double_X _ _ _ h₀ h₁

lemma free_finite_complexMulNat_X (i : ℤ) :
    Module.Free (ZMod (ℓ ^ 2)) ((complexMulNat ℓ).X i) ∧
      Module.Finite (ZMod (ℓ ^ 2)) ((complexMulNat ℓ).X i) := by
  refine free_finite_of_isZero_or_iso ?_
  by_cases h₀ : i = 0
  · subst h₀
    exact .inr ⟨HomologicalComplex.doubleXIso₀ _ _⟩
  by_cases h₁ : i = 1
  · subst h₁
    exact .inr ⟨HomologicalComplex.doubleXIso₁ _ _ zero_ne_one⟩
  exact .inl (isZero_complexMulNat_X ℓ i h₀ h₁)

lemma iCycles_comp_endComplexMulNat_sub_id_f (i : ℤ) :
    (complexMulNat ℓ).iCycles i ≫ (endComplexMulNat ℓ - 𝟙 _).f i = 0 := by
  by_cases h₀ : i = 0
  · subst h₀
    have : (ℓ : ZMod (ℓ ^ 2)) • 𝟙 ((complexMulNat ℓ).X 0) = (complexMulNat ℓ).d 0 1 ≫
        (HomologicalComplex.doubleXIso₁ _ _ zero_ne_one).hom ≫
          (HomologicalComplex.doubleXIso₀ _ _).inv := by
      rw [HomologicalComplex.double_d _ _ zero_ne_one]
      simp
    rw [endComplexMulNat_sub_id_f_zero, this, HomologicalComplex.iCycles_d_assoc, zero_comp]
  by_cases h₁ : i = 1
  · subst h₁
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, endComplexMulNat_f_one, sub_self,
      comp_zero]
  exact (isZero_complexMulNat_X ℓ i h₀ h₁).eq_of_tgt _ _

lemma homologyMap_endComplexMulNat (i : ℤ) :
    HomologicalComplex.homologyMap (endComplexMulNat ℓ) i = 𝟙 _ := by
  rw [← sub_add_cancel (endComplexMulNat ℓ) (𝟙 _), HomologicalComplex.homologyMap_add,
    homologyMap_eq_zero_of_iCycles_comp _ _
      (iCycles_comp_endComplexMulNat_sub_id_f ℓ i), HomologicalComplex.homologyMap_id, zero_add]

instance : (complexMulNat ℓ).IsStrictlyGE 0 :=
  ((complexMulNat ℓ).isStrictlyGE_iff 0).2 fun i hi ↦
    isZero_complexMulNat_X ℓ i (by omega) (by omega)

instance : (complexMulNat ℓ).IsStrictlyLE 1 :=
  ((complexMulNat ℓ).isStrictlyLE_iff 1).2 fun i hi ↦
    isZero_complexMulNat_X ℓ i (by omega) (by omega)

/-- The complex `A[-n]`: the module `A = ℤ/ℓ²` placed in degree `n`. -/
noncomputable abbrev singleUnit (n : ℤ) : CochainComplex (ModuleCat.{0} (ZMod (ℓ ^ 2))) ℤ :=
  (HomologicalComplex.single _ (.up ℤ) n).obj (ModuleCat.of (ZMod (ℓ ^ 2)) (ZMod (ℓ ^ 2)))

lemma free_finite_singleUnit_X (n i : ℤ) :
    Module.Free (ZMod (ℓ ^ 2)) ((singleUnit ℓ n).X i) ∧
      Module.Finite (ZMod (ℓ ^ 2)) ((singleUnit ℓ n).X i) := by
  refine free_finite_of_isZero_or_iso ?_
  by_cases h : i = n
  · subst h
    exact .inr ⟨HomologicalComplex.singleObjXSelf _ _ _⟩
  · exact .inl (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)

/-- The inclusion `A[-1] ⟶ P` of the degree `1` term of `P = [A --ℓ--> A]`. -/
noncomputable def singleUnitToComplexMulNat : singleUnit ℓ 1 ⟶ complexMulNat ℓ :=
  HomologicalComplex.mkHomFromSingle (HomologicalComplex.doubleXIso₁ _ _ zero_ne_one).inv
    (fun k _ ↦ by rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ one_ne_zero, comp_zero])

/-- The projection `P ⟶ A` onto the degree `0` term of `P = [A --ℓ--> A]`. -/
noncomputable def complexMulNatToSingleUnit : complexMulNat ℓ ⟶ singleUnit ℓ 0 :=
  HomologicalComplex.mkHomFromDouble _ zero_ne_one
    (HomologicalComplex.singleObjXSelf _ _ _).inv 0 (by simp) (fun _ _ ↦ zero_comp)

/-- The degreewise split short exact sequence `0 ⟶ A[-1] ⟶ P ⟶ A ⟶ 0`. -/
noncomputable abbrev shortComplexMulNat :
    ShortComplex (CochainComplex (ModuleCat.{0} (ZMod (ℓ ^ 2))) ℤ) where
  f := singleUnitToComplexMulNat ℓ
  g := complexMulNatToSingleUnit ℓ
  zero := HomologicalComplex.from_single_hom_ext (by
    simp [singleUnitToComplexMulNat, complexMulNatToSingleUnit])

lemma shortComplexMulNat_shortExact : (shortComplexMulNat ℓ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ ?_
  by_cases h₀ : i = 0
  · subst h₀
    have hg : IsIso ((complexMulNatToSingleUnit ℓ).f 0) := by
      simp only [complexMulNatToSingleUnit, HomologicalComplex.mkHomFromDouble_f₀]
      infer_instance
    have h₁ := HomologicalComplex.isZero_single_obj_X (.up ℤ) 1
      (ModuleCat.of (ZMod (ℓ ^ 2)) (ZMod (ℓ ^ 2))) 0 zero_ne_one
    exact .mk' ((ShortComplex.exact_iff_mono _ (h₁.eq_of_src _ _)).2
      (show Mono ((complexMulNatToSingleUnit ℓ).f 0) from inferInstance))
      (h₁.mono _) (show Epi ((complexMulNatToSingleUnit ℓ).f 0) from inferInstance)
  by_cases h₁ : i = 1
  · subst h₁
    have hf : IsIso ((singleUnitToComplexMulNat ℓ).f 1) := by
      simp only [singleUnitToComplexMulNat, HomologicalComplex.mkHomFromSingle_f]
      infer_instance
    have h₃ := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (ModuleCat.of (ZMod (ℓ ^ 2)) (ZMod (ℓ ^ 2))) 1 one_ne_zero
    exact .mk' ((ShortComplex.exact_iff_epi _ (h₃.eq_of_tgt _ _)).2
      (show Epi ((singleUnitToComplexMulNat ℓ).f 1) from inferInstance))
      (show Mono ((singleUnitToComplexMulNat ℓ).f 1) from inferInstance) (h₃.epi _)
  exact .mk' (ShortComplex.exact_of_isZero_X₂ _ (isZero_complexMulNat_X ℓ i h₀ h₁))
    ((HomologicalComplex.isZero_single_obj_X (.up ℤ) _ _ _ h₁).mono _)
    ((HomologicalComplex.isZero_single_obj_X (.up ℤ) _ _ _ h₀).epi _)

/-- The null-homotopic map `(ℓ, 0) : P ⟶ A`, with homotopy `id : P¹ = A ⟶ A`. -/
noncomputable def nullHomotopicComplexMulNatToSingleUnit : complexMulNat ℓ ⟶ singleUnit ℓ 0 :=
  Homotopy.nullHomotopicMap' fun i j _ ↦
    if h : i = 1 ∧ j = 0 then
      eqToHom (congrArg (complexMulNat ℓ).X h.1) ≫
        (HomologicalComplex.doubleXIso₁ _ rel_zero_one zero_ne_one).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (ModuleCat.of (ZMod (ℓ ^ 2)) (ZMod (ℓ ^ 2)))).inv ≫
        eqToHom (congrArg (singleUnit ℓ 0).X h.2.symm)
    else 0

lemma endComplexMulNat_sub_id_comp_complexMulNatToSingleUnit :
    (endComplexMulNat ℓ - 𝟙 _) ≫ complexMulNatToSingleUnit ℓ =
      nullHomotopicComplexMulNatToSingleUnit ℓ := by
  refine HomologicalComplex.from_double_hom_ext ?_ ?_
  · rw [HomologicalComplex.comp_f, endComplexMulNat_sub_id_f_zero,
      nullHomotopicComplexMulNatToSingleUnit,
      Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) rel_zero_one,
      HomologicalComplex.double_d _ _ zero_ne_one]
    simp [complexMulNatToSingleUnit]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) _ _ _ one_ne_zero).eq_of_tgt _ _

lemma Q_map_endComplexMulNat_comp_complexMulNatToSingleUnit
    [HasDerivedCategory.{0} (ModuleCat.{0} (ZMod (ℓ ^ 2)))] :
    Q.map (endComplexMulNat ℓ) ≫ Q.map (complexMulNatToSingleUnit ℓ) =
      Q.map (complexMulNatToSingleUnit ℓ) := by
  rw [← Q.map_comp, ← sub_add_cancel (endComplexMulNat ℓ) (𝟙 _), Preadditive.add_comp,
    Category.id_comp, Functor.map_add, endComplexMulNat_sub_id_comp_complexMulNatToSingleUnit,
    nullHomotopicComplexMulNatToSingleUnit, Q_map_eq_of_homotopy (h := Homotopy.nullHomotopy' _),
    Functor.map_zero, zero_add]

variable [HasDerivedCategory.{0} (ModuleCat.{0} (ZMod (ℓ ^ 2)))]

/-- The distinguished triangle `A[-1] ⟶ P ⟶ A ⟶ A[-1][1]` in `D(A)`. -/
noncomputable abbrev triangleMulNat : Triangle (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2)))) :=
  triangleOfSES (shortComplexMulNat_shortExact ℓ)

/-- The endomorphism `(1, v, 1)` of the triangle `A[-1] ⟶ P ⟶ A ⟶ A[-1][1]`. Its middle square
commutes only up to homotopy. -/
noncomputable def triangleMulNatEnd : triangleMulNat ℓ ⟶ triangleMulNat ℓ where
  hom₁ := 𝟙 _
  hom₂ := Q.map (endComplexMulNat ℓ)
  hom₃ := 𝟙 _
  comm₁ := by
    change Q.map (singleUnitToComplexMulNat ℓ) ≫ Q.map (endComplexMulNat ℓ) =
      𝟙 _ ≫ Q.map (singleUnitToComplexMulNat ℓ)
    rw [← Q.map_comp, Category.id_comp]
    congr 1
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [HomologicalComplex.comp_f, endComplexMulNat_f_one, Category.comp_id]
  comm₂ := by
    change Q.map (complexMulNatToSingleUnit ℓ) ≫ 𝟙 _ =
      Q.map (endComplexMulNat ℓ) ≫ Q.map (complexMulNatToSingleUnit ℓ)
    rw [Category.comp_id, Q_map_endComplexMulNat_comp_complexMulNatToSingleUnit]
  comm₃ := by
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

lemma trace_Q_map_complexMulNat [Fact ℓ.Prime] (v : complexMulNat ℓ ⟶ complexMulNat ℓ)
    (a b : ZMod (ℓ ^ 2)) (h₀ : v.f 0 = a • 𝟙 _) (h₁ : v.f 1 = b • 𝟙 _)
    [hP : HasRightDual (Q.obj (complexMulNat ℓ))] :
    letI := braidedCategory' (ModuleCat.{0} (ZMod (ℓ ^ 2)))
    MonoidalCategory.trace (Q.map v) =
      (algebraMap (ZMod (ℓ ^ 2)) (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))))))
        (a - b)).asHom := by
  have := fact_one_lt_sq ℓ
  rw [trace_eq_algebraMap_sum_negOnePow_linearMapTrace (complexMulNat ℓ) v {0, 1}
    (fun i hi ↦ isZero_complexMulNat_X ℓ i (by simp_all) (by simp_all))
    (fun i ↦ (free_finite_complexMulNat_X ℓ i).1) (fun i ↦ (free_finite_complexMulNat_X ℓ i).2)
    _ (Q.map v) (Iso.refl _) (by simp), Finset.sum_pair zero_ne_one, h₀, h₁]
  have := (free_finite_complexMulNat_X ℓ 0).1
  have := (free_finite_complexMulNat_X ℓ 0).2
  have := (free_finite_complexMulNat_X ℓ 1).1
  have := (free_finite_complexMulNat_X ℓ 1).2
  rw [linearMapTrace_smul_id (HomologicalComplex.doubleXIso₀ _ _),
    linearMapTrace_smul_id (HomologicalComplex.doubleXIso₁ _ _ zero_ne_one)]
  simp [sub_eq_add_neg]

lemma trace_id_Q_obj_singleUnit [Fact ℓ.Prime] (n : ℤ)
    [hP : HasRightDual (Q.obj (singleUnit ℓ n))] :
    letI := braidedCategory' (ModuleCat.{0} (ZMod (ℓ ^ 2)))
    MonoidalCategory.trace (𝟙 (Q.obj (singleUnit ℓ n))) =
      (algebraMap (ZMod (ℓ ^ 2)) (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))))))
        ((n.negOnePow : ℤ) : ZMod (ℓ ^ 2))).asHom := by
  have := fact_one_lt_sq ℓ
  rw [← Q.map_id, trace_eq_algebraMap_sum_negOnePow_linearMapTrace (singleUnit ℓ n) (𝟙 _) {n}
    (fun i hi ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa using hi))
    (fun i ↦ (free_finite_singleUnit_X ℓ n i).1) (fun i ↦ (free_finite_singleUnit_X ℓ n i).2)
    _ (Q.map (𝟙 _)) (Iso.refl _) (by simp), Finset.sum_singleton,
    HomologicalComplex.id_f]
  have := (free_finite_singleUnit_X ℓ n n).1
  have := (free_finite_singleUnit_X ℓ n n).2
  rw [← one_smul (ZMod (ℓ ^ 2)) (𝟙 ((singleUnit ℓ n).X n)),
    linearMapTrace_smul_id (HomologicalComplex.singleObjXSelf _ _ _)]
  simp

lemma nonempty_hasRightDual_Q_obj_complexMulNat :
    Nonempty (HasRightDual (Q.obj (complexMulNat ℓ))) :=
  nonempty_hasRightDual_Q_obj _ 0 1 (fun i ↦ (free_finite_complexMulNat_X ℓ i).1)
    (fun i ↦ (free_finite_complexMulNat_X ℓ i).2)

lemma nonempty_hasRightDual_Q_obj_singleUnit (n : ℤ) :
    Nonempty (HasRightDual (Q.obj (singleUnit ℓ n))) :=
  nonempty_hasRightDual_Q_obj _ n n (fun i ↦ (free_finite_singleUnit_X ℓ n i).1)
    (fun i ↦ (free_finite_singleUnit_X ℓ n i).2)

end TraceCounterexample

open TraceCounterexample

variable [Fact ℓ.Prime]

/-- Blueprint `example-trace-not-determined-cohomology`: over `A = ℤ/ℓ²`, the trace of an
endomorphism of a perfect complex is not determined by the maps it induces on cohomology. Let
`P = [A --ℓ--> A]` in degrees `0` and `1`, and `v = (1 + ℓ, 1)`. Then `v` induces the identity on
all cohomology objects of `P`, `P` is dualizable in `D(A)`, and for any choice of right dual,
`tr (1_P ∣ P) = 1 - 1 = 0` while `tr (v ∣ P) = (1 + ℓ) - 1 = ℓ ≠ 0`. -/
theorem trace_not_determined_by_homology :
    (∀ i, HomologicalComplex.homologyMap (endComplexMulNat ℓ) i = 𝟙 _) ∧
      Nonempty (HasRightDual (Q.obj (complexMulNat ℓ))) ∧
      ∀ [HasRightDual (Q.obj (complexMulNat ℓ))],
        letI := braidedCategory' (ModuleCat.{0} (ZMod (ℓ ^ 2)))
        MonoidalCategory.trace (𝟙 (Q.obj (complexMulNat ℓ))) = 0 ∧
        MonoidalCategory.trace (Q.map (endComplexMulNat ℓ)) =
          (algebraMap (ZMod (ℓ ^ 2)) (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))))))
            (ℓ : ZMod (ℓ ^ 2))).asHom ∧
        MonoidalCategory.trace (Q.map (endComplexMulNat ℓ)) ≠
          MonoidalCategory.trace (𝟙 (Q.obj (complexMulNat ℓ))) := by
  refine ⟨homologyMap_endComplexMulNat ℓ, nonempty_hasRightDual_Q_obj_complexMulNat ℓ, ?_⟩
  intro _
  let := braidedCategory' (ModuleCat.{0} (ZMod (ℓ ^ 2)))
  have h₁ : MonoidalCategory.trace (𝟙 (Q.obj (complexMulNat ℓ))) = 0 := by
    rw [← Q.map_id, trace_Q_map_complexMulNat ℓ (𝟙 _) 1 1 (by simp) (by simp), sub_self,
      map_zero, End.zero_asHom]
  have h₂ : MonoidalCategory.trace (Q.map (endComplexMulNat ℓ)) =
      (algebraMap (ZMod (ℓ ^ 2)) (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))))))
        (ℓ : ZMod (ℓ ^ 2))).asHom := by
    rw [trace_Q_map_complexMulNat ℓ _ (1 + ℓ) 1 (endComplexMulNat_f_zero ℓ)
      (by rw [endComplexMulNat_f_one, one_smul]), add_sub_cancel_left]
  refine ⟨h₁, h₂, ?_⟩
  rw [h₁, h₂]
  exact fun h ↦ natCast_ne_zero_of_sq ℓ
    (algebraMap_end_unit_injective (End.ext (h.trans (by simp))))

/-- Blueprint `remark-coherent-additivity`: over `A = ℤ/ℓ²`, the trace is not additive for
endomorphisms of distinguished triangles whose squares only commute in `D(A)`. There are a
distinguished triangle `T` of dualizable objects of `D(A)` and an endomorphism `φ : T ⟶ T` of
triangles such that, for any choice of right duals, `tr φ.hom₂ ≠ tr φ.hom₁ + tr φ.hom₃`.

Here `T` is the triangle `A[-1] ⟶ P ⟶ A ⟶ A[-1][1]` of the degreewise split short exact
sequence, with `P = [A --ℓ--> A]` in degrees `0` and `1`, and `φ = (1, v, 1)` with
`v = (1 + ℓ, 1)`; the traces are `-1`, `ℓ` and `1`. -/
theorem exists_triangle_endomorphism_trace_ne_add :
    ∃ (T : Triangle (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))))) (φ : T ⟶ T),
      T ∈ distTriang _ ∧ Nonempty (HasRightDual T.obj₁) ∧ Nonempty (HasRightDual T.obj₂) ∧
        Nonempty (HasRightDual T.obj₃) ∧
        ∀ [HasRightDual T.obj₁] [HasRightDual T.obj₂] [HasRightDual T.obj₃],
          letI := braidedCategory' (ModuleCat.{0} (ZMod (ℓ ^ 2)))
          MonoidalCategory.trace φ.hom₂ ≠
            MonoidalCategory.trace φ.hom₁ + MonoidalCategory.trace φ.hom₃ := by
  refine ⟨triangleMulNat ℓ, triangleMulNatEnd ℓ, triangleOfSES_distinguished _,
    nonempty_hasRightDual_Q_obj_singleUnit ℓ 1, nonempty_hasRightDual_Q_obj_complexMulNat ℓ,
    nonempty_hasRightDual_Q_obj_singleUnit ℓ 0, fun {h₁ h₂ h₃} ↦ ?_⟩
  let := braidedCategory' (ModuleCat.{0} (ZMod (ℓ ^ 2)))
  have e₁ : MonoidalCategory.trace (triangleMulNatEnd ℓ).hom₁ = (algebraMap (ZMod (ℓ ^ 2))
      (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2)))))) (-1)).asHom :=
    (trace_id_Q_obj_singleUnit ℓ 1 (hP := h₁)).trans (by simp)
  have e₂ : MonoidalCategory.trace (triangleMulNatEnd ℓ).hom₂ =
      (algebraMap (ZMod (ℓ ^ 2)) (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2))))))
        ((1 + ℓ : ZMod (ℓ ^ 2)) - 1)).asHom :=
    trace_Q_map_complexMulNat ℓ _ (1 + ℓ) 1 (endComplexMulNat_f_zero ℓ)
      (by rw [endComplexMulNat_f_one, one_smul]) (hP := h₂)
  have e₃ : MonoidalCategory.trace (triangleMulNatEnd ℓ).hom₃ = (algebraMap (ZMod (ℓ ^ 2))
      (End (𝟙_ (DerivedCategory (ModuleCat.{0} (ZMod (ℓ ^ 2)))))) 1).asHom :=
    (trace_id_Q_obj_singleUnit ℓ 0 (hP := h₃)).trans (by simp)
  rw [e₁, e₂, e₃, add_sub_cancel_left]
  exact fun h ↦ natCast_ne_zero_of_sq ℓ
    (algebraMap_end_unit_injective (End.ext (h.trans (by simp))))

end Counterexample

end DerivedCategory
