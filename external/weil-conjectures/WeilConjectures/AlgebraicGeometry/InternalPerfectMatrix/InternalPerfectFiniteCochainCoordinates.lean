/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectOrdinaryMatrixData
import Mathlib.Algebra.Homology.Embedding.IsSupported

/-! # Finite integral coordinates for bounded Hom cochains
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.InternalPerfectMatrix

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite set of matrix entries in degree q of a bounded Hom complex. -/
abbrev CoordinateIndex (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (a b q : ℤ) :=
  Σ i : ↥(Finset.Icc a b),
    Fin (Module.finrank (A l E) (P.X i.val)) ×
      Fin (Module.finrank (A l E) (P.X (i.val + q)))

/-- All integral entries in the fixed bases. -/
def cochainCoordinates (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) :
    (CochainComplex.moduleHomComplex P P).X q →ₗ[A l E]
      (CoordinateIndex l E P a b q → A l E) where
  toFun z k := integralEntry l E P hfree q k.1.val (k.1.val + q) rfl k.2.1 k.2.2 z
  map_add' z w := by
    funext k
    exact (integralEntry l E P hfree q k.1.val (k.1.val + q) rfl k.2.1 k.2.2).map_add z w
  map_smul' c z := by
    funext k
    exact (integralEntry l E P hfree q k.1.val (k.1.val + q) rfl k.2.1 k.2.2).map_smul c z

/-- Reassemble a cochain from its finitely many integral matrix entries, using zero
outside the specified degree interval. -/
def cochainFromCoordinates (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (x : CoordinateIndex l E P a b q → A l E) :
    CochainComplex.HomComplex.Cochain P P q :=
  CochainComplex.HomComplex.Cochain.mk fun i j hij ↦ by
    subst j
    exact if hi : i ∈ Finset.Icc a b then
      ModuleCat.ofHom ((basis l E P hfree i).constr (A l E) fun s ↦
        (basis l E P hfree (i + q)).equivFun.symm fun t ↦ x ⟨⟨i, hi⟩, s, t⟩)
    else 0

/-- Fixed finite integral matrices give all Hom cochains, uniquely. -/
theorem cochainCoordinates_bijective
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    Function.Bijective (cochainCoordinates l E P hfree a b q) := by
  classical
  constructor
  · intro x y hxy
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    subst j
    by_cases hi : i ∈ Finset.Icc a b
    · apply ModuleCat.hom_ext
      apply (basis l E P hfree i).ext
      intro s
      apply (basis l E P hfree (i + q)).repr.injective
      apply Finsupp.ext
      intro t
      exact congrFun hxy ⟨⟨i, hi⟩, s, t⟩
    · have hz : IsZero (P.X i) := by
        by_cases hia : i < a
        · exact (P.isStrictlyGE_iff a).mp ha i hia
        · exact (P.isStrictlyLE_iff b).mp hb i (by
            simp only [Finset.mem_Icc] at hi
            omega)
      exact hz.eq_of_src _ _
  · intro x
    refine ⟨cochainFromCoordinates l E P hfree a b q x, ?_⟩
    funext k
    rcases k with ⟨i, s, t⟩
    change (basis l E P hfree (i.val + q)).repr
      (((cochainFromCoordinates l E P hfree a b q x).v i.val (i.val + q) rfl)
        ((basis l E P hfree i.val) s)) t = _
    simp only [cochainFromCoordinates, CochainComplex.HomComplex.Cochain.mk_v,
      dite_eq_left i.property]
    change (basis l E P hfree (i.val + q)).repr
      (((basis l E P hfree i.val).constr (A l E) fun s ↦
        (basis l E P hfree (i.val + q)).equivFun.symm fun t ↦ x ⟨i, s, t⟩)
          ((basis l E P hfree i.val) s)) t = _
    rw [Module.Basis.constr_basis, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]

/-- The integral Hom cochain module in finite matrix coordinates. -/
def cochainCoordinateEquiv
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) :
    (CochainComplex.moduleHomComplex P P).X q ≃ₗ[A l E]
      (CoordinateIndex l E P a b q → A l E) :=
  LinearEquiv.ofBijective _ (cochainCoordinates_bijective l E P hfree a b q ha hb)

/-- Coordinates of the actual quotient Hom cochain, formed by entrywise cokernel descent. -/
def quotientCoordinates
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (n : ℕ) :
    (Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
      (CochainComplex.moduleHomComplex P P) (n + 1)).X q →ₗ[A l E]
        (CoordinateIndex l E P a b q → Padic.coefficientExtensionRing l E (n + 1)) where
  toFun z k := quotientEntry l E P hfree n q k.1.val (k.1.val + q) rfl k.2.1 k.2.2 z
  map_add' z w := by
    funext k
    exact (quotientEntry l E P hfree n q k.1.val (k.1.val + q) rfl
      k.2.1 k.2.2).hom.map_add z w
  map_smul' c z := by
    funext k
    exact (quotientEntry l E P hfree n q k.1.val (k.1.val + q) rfl
      k.2.1 k.2.2).hom.map_smul c z

/-- Quotient matrix coordinates on an integral representative are its entrywise residues. -/
theorem quotientCoordinates_projection
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (n : ℕ) (x : (CochainComplex.moduleHomComplex P P).X q)
    (k : CoordinateIndex l E P a b q) :
    quotientCoordinates l E P hfree a b q n
      ((cokernel.π ((Padic.coefficientExtensionUniformizer l E) ^ (n + 1) •
        𝟙 (CochainComplex.moduleHomComplex P P))).f q x) k =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
        (cochainCoordinates l E P hfree a b q x k) := by
  exact congrArg (fun f ↦ f x)
    (quotientEntry_projection l E P hfree n q k.1.val (k.1.val + q) rfl k.2.1 k.2.2)

/-- A bounded finite free Hom complex has precisely finite matrices over the scalar
quotient in each degree, including for the actual categorical cokernel construction. -/
theorem quotientCoordinates_bijective
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) (n : ℕ) :
    Function.Bijective (quotientCoordinates l E P hfree a b q n) := by
  classical
  let c := cochainCoordinateEquiv l E P hfree a b q ha hb
  let t := Padic.coefficientExtensionUniformizer l E
  let Q := CochainComplex.moduleHomComplex P P
  let φ := t ^ (n + 1) • 𝟙 Q
  let π := (cokernel.π φ).f q
  have hπ : Function.Surjective π := (ModuleCat.epi_iff_surjective π).mp inferInstance
  have hzero : ∀ z, quotientCoordinates l E P hfree a b q n z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x, rfl⟩ := hπ z
    have hdiv : ∀ k : CoordinateIndex l E P a b q,
        ∃ y : A l E, t ^ (n + 1) * y = c x k := by
      intro k
      have hk := congrFun hz k
      change quotientCoordinates l E P hfree a b q n (π x) k = 0 at hk
      rw [quotientCoordinates_projection] at hk
      have hm := Ideal.Quotient.eq_zero_iff_mem.mp hk
      rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hm
      obtain ⟨y, hy⟩ := hm
      exact ⟨y, hy.symm⟩
    choose y hy using hdiv
    let v := c.symm y
    have hv : t ^ (n + 1) • v = x := by
      apply c.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      funext k
      exact hy k
    have hkill : φ.f q ≫ π = 0 :=
      congrArg (fun f ↦ f.f q) (cokernel.condition φ)
    have hk := congrArg (fun f ↦ f v) hkill
    change π (t ^ (n + 1) • v) = 0 at hk
    rw [hv] at hk
    exact hk
  constructor
  · intro z w hzw
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hzw, sub_self]
  · intro z
    have hlift : ∀ k : CoordinateIndex l E P a b q,
        ∃ x : A l E, Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x = z k :=
      fun k ↦ Ideal.Quotient.mk_surjective (z k)
    choose x hx using hlift
    refine ⟨π (c.symm x), ?_⟩
    funext k
    rw [quotientCoordinates_projection]
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (c (c.symm x) k) = z k
    rw [LinearEquiv.apply_symm_apply]
    exact hx k

/-- Coordinates of maps between the finite free terms of a bounded complex. -/
def freeCochainEquiv {C : Type v} [Category.{w} C] [Preadditive C]
    [HasFiniteBiproducts C] (R : C) (K : CochainComplex C ℤ) (r : ℤ → ℕ)
    (e : ∀ i, K.X i ≅ ⨁ fun _ : Fin (r i) ↦ R)
    (a b q : ℤ) (hs : ∀ i, i ∉ Finset.Icc a b → IsZero (K.X i)) :
    CochainComplex.HomComplex.Cochain K K q ≃
      ((Σ i : ↥(Finset.Icc a b), Fin (r i.val) × Fin (r (i.val + q))) → End R) := by
  classical
  let forward := fun (z : CochainComplex.HomComplex.Cochain K K q)
      (k : Σ i : ↥(Finset.Icc a b), Fin (r i.val) × Fin (r (i.val + q))) ↦
    End.of (biproduct.components
      ((e k.1.val).inv ≫ z.v k.1.val (k.1.val + q) rfl ≫ (e (k.1.val + q)).hom)
        k.2.1 k.2.2)
  let backward :
      ((Σ i : ↥(Finset.Icc a b), Fin (r i.val) × Fin (r (i.val + q))) → End R) →
        CochainComplex.HomComplex.Cochain K K q := fun x ↦
    CochainComplex.HomComplex.Cochain.mk fun i j hij ↦ by
      subst j
      exact if hi : i ∈ Finset.Icc a b then
        (e i).hom ≫ biproduct.matrix (fun s t ↦ (x ⟨⟨i, hi⟩, s, t⟩).asHom) ≫ (e (i + q)).inv
      else 0
  refine ⟨forward, backward, ?_, ?_⟩
  · intro z
    apply CochainComplex.HomComplex.Cochain.ext
    intro i j hij
    subst j
    by_cases hi : i ∈ Finset.Icc a b
    · dsimp only [backward, CochainComplex.HomComplex.Cochain.mk_v]
      rw [dite_eq_left hi]
      dsimp only [forward]
      rw [biproduct.components_matrix
        ((e i).inv ≫ z.v i (i + q) rfl ≫ (e (i + q)).hom)]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    · dsimp only [backward, CochainComplex.HomComplex.Cochain.mk_v]
      rw [dite_eq_right hi]
      exact (hs i hi).eq_of_src _ _
  · intro x
    funext k
    rcases k with ⟨i, s, t⟩
    apply End.ext
    dsimp only [forward, backward, CochainComplex.HomComplex.Cochain.mk_v]
    rw [dite_eq_left i.property]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    erw [biproduct.matrix_components]

/-- Explicit matrix evaluation is bijective in every degree of a bounded finite free
complex. This is a statement about graded cochains; differential compatibility is separate. -/
theorem evaluation_bijective (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (A l E)) ℤ)
    (hfree : ∀ i, Module.Finite (A l E) (P.X i) ∧ Module.Free (A l E) (P.X i))
    (a b q : ℤ) (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b) (n : ℕ) :
    Function.Bijective (evaluationHom l E W P hfree n q) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let T := ConnectedComponents W
  let M := (Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
    (CochainComplex.moduleHomComplex P P) (n + 1)).X q
  let I := CoordinateIndex l E P a b q
  let C : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    (AdicCompletion.finiteRing l E W n)) ℤ :=
    internalPerfectOrdinaryReduction l E W P n
  let r := fun i : ℤ ↦ Module.finrank (A l E) (P.X i)
  let e := quotientIso l E W P hfree n
  have hC : ∀ i, i ∉ Finset.Icc a b → IsZero (C.X i) := by
    let := ha
    let := hb
    have hCa : C.IsStrictlyGE a := by
      dsimp only [C, internalPerfectOrdinaryReduction, internalPerfectIntegralComplex]
      infer_instance
    have hCb : C.IsStrictlyLE b := by
      dsimp only [C, internalPerfectOrdinaryReduction, internalPerfectIntegralComplex]
      infer_instance
    intro i hi
    by_cases hia : i < a
    · exact (C.isStrictlyGE_iff a).mp hCa i hia
    · exact (C.isStrictlyLE_iff b).mp hCb i (by
        simp only [Finset.mem_Icc] at hi
        omega)
  let ce := freeCochainEquiv (Mod.regular (AdicCompletion.finiteRing l E W n))
    C r e a b q hC
  let qc : M ≃ (I → B) :=
    Equiv.ofBijective _ (quotientCoordinates_bijective l E P hfree a b q ha hb n)
  let flipEquiv : LocallyConstant T (I → B) ≃ (I → LocallyConstant T B) :=
    ⟨LocallyConstant.flip, LocallyConstant.unflip,
      LocallyConstant.unflip_flip, LocallyConstant.flip_unflip⟩
  let lc := (LocallyConstant.congrRight (X := T) qc).trans flipEquiv
  let ee := lc.trans ((Equiv.piCongrRight fun _ : I ↦
    (coefficientEndEquiv l E W n).toEquiv).trans ce.symm)
  have hv (z : LocallyConstant T M) :
      ce (evaluate l E W P hfree n q z) = fun k : I ↦
        coefficientEndEquiv l E W n
          (z.map (quotientEntry l E P hfree n q k.1.val (k.1.val + q) rfl
            k.2.1 k.2.2)) := by
    funext k
    apply End.ext
    change biproduct.components
      ((e k.1.val).inv ≫
        ((e k.1.val).hom ≫ biproduct.matrix (fun s t ↦
          (coefficientEndEquiv l E W n
            (z.map (quotientEntry l E P hfree n q k.1.val (k.1.val + q) rfl s t))).asHom) ≫
          (e (k.1.val + q)).inv) ≫ (e (k.1.val + q)).hom) k.2.1 k.2.2 = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id, biproduct.matrix_components]
  have hh : (fun z : LocallyConstant T M ↦ evaluate l E W P hfree n q z) = ee := by
    funext z
    apply ce.injective
    rw [hv]
    change _ = ce (ce.symm _)
    rw [Equiv.apply_symm_apply]
    rfl
  change Function.Bijective (fun z : ULift.{u + 1} (LocallyConstant T M) ↦
    evaluate l E W P hfree n q z.down)
  change Function.Bijective ((fun z : LocallyConstant T M ↦
    evaluate l E W P hfree n q z) ∘ Equiv.ulift)
  rw [hh]
  exact ee.bijective.comp Equiv.ulift.bijective

end AlgebraicGeometry.ProEtale.InternalPerfectMatrix
