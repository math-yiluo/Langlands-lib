/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Galois extensions receiving separable extensions, and normal extensions

* `exists_finiteDimensional_isGalois_algHom_of_isSeparable`: finitely many finite separable
  extensions `Lᵢ / k` embed into one finite Galois extension of `k`
  (Stacks, Lemmas 09DT and 0EXM).
* `Normal.isPurelyInseparable_fixedField_and_isGalois`: if `E / F` is normal and
  `E_insep = E ^ Aut(E/F)`, then `E_insep / F` is purely inseparable and `E / E_insep` is Galois
  (Stacks, Lemma 030M (2)).

## References

- Stacks Project, Lemma 09.15.1, <https://stacks.math.columbia.edu/tag/030M>
-/

@[expose] public section

open IntermediateField Polynomial

universe u v

/-- **Finitely many finite separable extensions embed into one finite Galois extension.**
If `L₁, …, Lₙ` are finite separable field extensions of `k`, there is a finite Galois extension
`M / k` together with `k`-algebra maps `Lᵢ →ₐ[k] M`. We take for `M` the normal closure, inside
a separable closure of `k`, of the compositum of the images of the `Lᵢ`.

(blueprint: `lem-weil-pbc-finite-galois-receiving-separable-extensions`) -/
theorem exists_finiteDimensional_isGalois_algHom_of_isSeparable {k : Type u} [Field k] {n : ℕ}
    (L : Fin n → Type v) [∀ i, Field (L i)] [∀ i, Algebra k (L i)]
    [∀ i, FiniteDimensional k (L i)] [∀ i, Algebra.IsSeparable k (L i)] :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra k M), FiniteDimensional k M ∧ IsGalois k M ∧
      Nonempty (∀ i, L i →ₐ[k] M) := by
  let Ω := SeparableClosure k
  let τ : ∀ i, L i →ₐ[k] Ω := fun i => IsSepClosed.lift
  let E : IntermediateField k Ω := ⨆ i, (τ i).fieldRange
  have : ∀ i, FiniteDimensional k (τ i).fieldRange := fun i =>
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (τ i)).toLinearEquiv
  have : FiniteDimensional k E := finiteDimensional_iSup_of_finite
  refine ⟨normalClosure k E Ω, inferInstance, inferInstance, inferInstance,
    IsGalois.normalClosure k E Ω, ⟨fun i => ?_⟩⟩
  exact (τ i).codRestrict (normalClosure k E Ω).toSubalgebra fun x =>
    le_normalClosure E (le_iSup (fun i => (τ i).fieldRange) i ⟨x, rfl⟩)

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- If `E / F` is normal, the fixed field of `Aut(E/F)` is purely inseparable over `F`. -/
theorem Normal.isPurelyInseparable_fixedField [Normal F E] :
    IsPurelyInseparable F (fixedField (⊤ : Subgroup Gal(E/F))) := by
  set K := fixedField (⊤ : Subgroup Gal(E/F))
  have hN : Normal F E := ‹_›
  refine ⟨⟨fun y => (hN.isIntegral (y : E)).tower_bot_of_field⟩, fun x hx => ?_⟩
  have hmin : minpoly F (x : E) = minpoly F x :=
    minpoly.algebraMap_eq (algebraMap K E).injective x
  have hxE : IsSeparable F (x : E) := by
    unfold IsSeparable; rw [hmin]; exact hx
  rw [← minpoly.natDegree_eq_one_iff]
  have hcard := card_rootSet_eq_natDegree (K := E) hxE (Normal.splits' (x : E))
  have hsub : ∀ y ∈ (minpoly F (x : E)).rootSet E, y = x := by
    intro y hy
    rw [mem_rootSet] at hy
    have hy' : minpoly F (x : E) = minpoly F y :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (hN.isIntegral _)) hy.2
        (minpoly.monic (hN.isIntegral _))
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) E).mp hy'.symm
    rw [← hσ]
    exact (mem_fixedField_iff _ _).mp x.2 σ trivial
  have hle : Fintype.card ((minpoly F (x : E)).rootSet E) ≤ 1 :=
    Fintype.card_le_one_iff.mpr fun a b => Subtype.ext ((hsub a a.2).trans (hsub b b.2).symm)
  have hpos := minpoly.natDegree_pos (hN.isIntegral (x : E))
  rw [← hmin]; omega

/-- If `E / F` is normal, then `E` is Galois over the fixed field of `Aut(E/F)`. For `x ∈ E`, the
polynomial `∏ (X - y)` over the distinct roots `y ∈ E` of the minimal polynomial of `x` over `F`
is separable and has coefficients fixed by `Aut(E/F)`. -/
theorem Normal.isGalois_fixedField [Normal F E] :
    IsGalois (fixedField (⊤ : Subgroup Gal(E/F))) E := by
  classical
  set K := fixedField (⊤ : Subgroup Gal(E/F))
  have hN : Normal K E := Normal.tower_top_of_normal F K E
  refine isGalois_iff.mpr ⟨⟨fun x => ?_⟩, hN⟩
  have hint : IsIntegral F x := Normal.isIntegral ‹Normal F E› x
  set s := ((minpoly F x).aroots E).toFinset with hs
  set p : E[X] := ∏ y ∈ s, (X - C y) with hp
  have hsep : p.Separable := separable_prod_X_sub_C_iff'.mpr fun _ _ _ _ h => h
  have hmem : ∀ y, y ∈ s ↔ aeval y (minpoly F x) = 0 := fun y => by
    simp [hs, mem_roots', minpoly.ne_zero hint]
  have hfix : ∀ σ : Gal(E/F), p.map (σ : E →+* E) = p := by
    intro σ
    rw [hp, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    refine Finset.prod_nbij' (fun y => σ y) (fun y => σ.symm y) ?_ ?_ ?_ ?_ ?_
    · intro y hy; rw [hmem] at hy ⊢
      simpa [hy] using (Polynomial.aeval_algHom_apply σ.toAlgHom y (minpoly F x))
    · intro y hy; rw [hmem] at hy ⊢
      simpa [hy] using (Polynomial.aeval_algHom_apply σ.symm.toAlgHom y (minpoly F x))
    · intro y _; simp
    · intro y _; simp
    · intro y _; rfl
  have hlift : p ∈ Polynomial.lifts (algebraMap K E) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨p.coeff n, (mem_fixedField_iff _ _).mpr fun σ _ => ?_⟩, rfl⟩
    have := congrArg (fun q => q.coeff n) (hfix σ)
    simpa [coeff_map] using this
  obtain ⟨q, hq⟩ := (mem_lifts p).mp hlift
  have hqsep : q.Separable := (separable_map (algebraMap K E)).mp (hq ▸ hsep)
  have hroot : aeval x q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hq, hp, eval_prod]
    exact Finset.prod_eq_zero ((hmem x).mpr (minpoly.aeval F x)) (by simp)
  exact hqsep.of_dvd (minpoly.dvd K x hroot)

/-- **A normal extension is Galois over a purely inseparable subextension.** Let `E / F` be a
normal (algebraic) extension and `E_insep = {x ∈ E | σ x = x for all σ ∈ Aut(E/F)}`, the
intermediate field `fixedField ⊤` (so a subfield of `E` containing `F`). Then `E_insep / F` is
purely inseparable and `E / E_insep` is Galois, i.e. separable and normal.

(blueprint: `lem-weil-pbc-normal-extension-purely-inseparable-then-galois`) -/
theorem Normal.isPurelyInseparable_fixedField_and_isGalois [Normal F E] :
    IsPurelyInseparable F (fixedField (⊤ : Subgroup Gal(E/F))) ∧
      IsGalois (fixedField (⊤ : Subgroup Gal(E/F))) E :=
  ⟨Normal.isPurelyInseparable_fixedField, Normal.isGalois_fixedField⟩
