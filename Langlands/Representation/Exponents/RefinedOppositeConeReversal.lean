import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.Exponents.Chambers

/-! # Actual opposite-to-upper reversal for refined Jacquet exponents -/

noncomputable section

namespace Langlands.Exponents.RefinedOppositeConeReversal

open GeneralLinear Geometric ProductLeviDualOpposite
open scoped BigOperators

universe u uF uV

theorem positiveRootCone_neg_of_reverse {r : ℕ} {x : Fin r → ℝ}
    (hx : IsPositiveRootCone (fun i => x i.rev)) :
    IsPositiveRootCone (fun i => -x i) := by
  have hsum : ∑ i, x i = 0 := by
    rw [← Equiv.sum_comp Fin.revPerm x]
    exact hx.1
  refine (isPositiveRootCone_iff_pairing _).mpr ⟨by simpa using hsum, ?_⟩
  intro h hm hn
  have hm' : Monotone (fun i : Fin r => -h i.rev) := by
    intro i j hij
    exact neg_le_neg (hm (Fin.rev_le_rev.mpr hij))
  have hn' : ∃ i j : Fin r, -h i.rev ≠ -h j.rev := by
    obtain ⟨i, j, hij⟩ := hn
    exact ⟨i.rev, j.rev, by simpa using hij⟩
  have hp := ((isPositiveRootCone_iff_pairing _).mp hx).2 _ hm' hn'
  have he : (∑ i : Fin r, x i.rev * ((-h i.rev : ℤ) : ℝ)) =
      ∑ i : Fin r, (-x i) * (h i : ℝ) := by
    calc
      _ = ∑ i : Fin r, (-x i.rev) * (h i.rev : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Int.cast_neg, mul_neg, neg_mul]
      _ = _ := by
        simpa only [Fin.revPerm_apply] using
          (Equiv.sum_comp Fin.revPerm (fun i : Fin r => (-x i) * (h i : ℝ)))
  rwa [he] at hp

section Reversal

variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)
  (R : Type u) [CommRing R]

theorem blockwiseCone_neg_of_reverse {x : Fin (C.flatten D).length → ℝ}
    (hx : ∀ j : Fin C.length,
      IsPositiveRootCone (fun k : Fin (reverseRefinement C D j).length =>
        (x ∘ reverseLabel C D)
          (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, k⟩))) :
    ∀ j : Fin C.length,
      IsPositiveRootCone (fun k : Fin (D j).length =>
        -x (C.flattenBlockEquiv D ⟨j, k⟩)) := by
  intro j
  apply positiveRootCone_neg_of_reverse
  have hj := hx j
  change IsPositiveRootCone (fun k : Fin (D j).length =>
    x (reverseLabel C D
      (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, k⟩))) at hj
  have hf : (fun k : Fin (D j).length =>
      x (reverseLabel C D
        (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, k⟩))) =
      (fun k : Fin (D j).length => x (C.flattenBlockEquiv D ⟨j, k.rev⟩)) := by
    funext k
    exact congrArg x (reverseLabel_apply C D j k)
  rwa [hf] at hj

theorem conj_mem_refinedOppositeUnipotent_iff (g : C.Levi R) :
    reverseWeyl C D R * g * (reverseWeyl C D R)⁻¹ ∈ refinedOppositeUnipotent R C D ↔
      g ∈ refinedUnipotent R C (reverseRefinement C D) := by
  rw [mem_refinedOppositeUnipotent, mem_refinedUnipotent]
  refine forall_congr' fun j => ?_
  exact (D j).reverseMatrix_conj_mem_oppositeUnipotentSubgroup_iff R (g j)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (C.Levi R) V)

/-- Inverse block reversal on the original opposite quotient. -/
def toUpper :
    RefinedOppositeJacquetModule C D ρ →ₗ[ℂ]
      RefinedJacquetModule C (reverseRefinement C D) ρ :=
  Jacquet.conjTranslate ρ (reverseWeyl C D R)⁻¹ fun u hu => by
    rw [← conj_mem_refinedOppositeUnipotent_iff]
    have h : reverseWeyl C D R *
        ((reverseWeyl C D R)⁻¹ * u * (reverseWeyl C D R)⁻¹⁻¹) *
        (reverseWeyl C D R)⁻¹ = u := by group
    rw [h]
    exact hu

/-- Block reversal gives a left inverse on the reversed upper quotient. -/
def fromUpper :
    RefinedJacquetModule C (reverseRefinement C D) ρ →ₗ[ℂ]
      RefinedOppositeJacquetModule C D ρ :=
  Jacquet.conjTranslate ρ (reverseWeyl C D R) fun u hu =>
    (conj_mem_refinedOppositeUnipotent_iff C D R u).mpr hu

theorem toUpper_mk (v : V) :
    toUpper C D R ρ (refinedOppositeJacquetMk C D ρ v) =
      refinedJacquetMk C (reverseRefinement C D) ρ
        (ρ (reverseWeyl C D R)⁻¹ v) := rfl

theorem fromUpper_toUpper (x : RefinedOppositeJacquetModule C D ρ) :
    fromUpper C D R ρ (toUpper C D R ρ x) = x :=
  Jacquet.conjTranslate_conjTranslate_inv ρ _ _ _ x

end Reversal

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

theorem isRealPartOf_relabel
    {χ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ}
    {x : Fin (C.flatten D).length → ℝ} (hx : T.IsRealPartOf χ x) :
    T.IsRealPartOf (χ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm))
      (x ∘ reverseLabel C D) := by
  intro a
  change ‖(χ (a ∘ (reverseLabel C D).symm) : ℂ)‖ = _
  rw [hx]
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (Equiv.prod_comp (reverseLabel C D) (fun i =>
      T.normalizedAbs ((a ∘ (reverseLabel C D).symm) i : F.Carrier) ^ x i)).symm

theorem isOpen_ker_relabel
    {χ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ} :
    letI := T.topology
    IsOpen (χ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
      IsOpen ((χ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)).ker :
        Set (Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ)) := by
  let := T.topology
  intro hχ
  have hcont : Continuous (MaximalConeAssembly.precomp (M := F.Carrierˣ)
      (reverseLabel C D).symm) := by
    change Continuous fun c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ =>
      fun k => c ((reverseLabel C D).symm k)
    exact continuous_pi fun k => continuous_apply _
  exact hχ.preimage hcont

theorem refinedLeviInverseHalfModulus_reverse
    (c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ) :
    (T.refinedLeviInverseHalfModulus C (reverseRefinement C D)
        (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier c)) : ℂ) =
      (T.refinedLeviHalfModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier
          (c ∘ (reverseLabel C D).symm))) : ℂ) := by
  rw [T.refinedLeviInverseHalfModulus_apply, T.refinedLeviHalfModulus_apply,
    refinedLeviModulus_reverse, Units.val_inv_eq_inv_val, NNReal.sqrt_inv,
    NNReal.coe_inv, Complex.ofReal_inv, inv_inv]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (C.Levi F.Carrier) V)

theorem toUpper_normalizedRefinedOppositeJacquet
    (c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ)
    (x : RefinedOppositeJacquetModule C D ρ) :
    toUpper C D F.Carrier ρ (T.normalizedRefinedOppositeJacquet C D ρ
        (flattenedLeviEquiv F.Carrier C D
          ((C.flatten D).blockScalarLevi F.Carrier
            (c ∘ (reverseLabel C D).symm))) x) =
      T.normalizedRefinedJacquet C (reverseRefinement C D) ρ
        (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier c))
        (toUpper C D F.Carrier ρ x) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (refinedOppositeUnipotent F.Carrier C D) x
  have hw : ∀ (g h : C.Levi F.Carrier) (u : V), ρ g (ρ h u) = ρ (g * h) u :=
    fun g h u => by rw [map_mul, Module.End.mul_apply]
  rw [T.normalizedRefinedOppositeJacquet_mk, map_smul, toUpper_mk, toUpper_mk,
    T.normalizedRefinedJacquet_mk, refinedLeviInverseHalfModulus_reverse,
    ← reverseWeyl_conj_blockScalar, hw, hw]
  congr 3
  group

theorem isGeneralizedEigencharacter_toUpper
    {χ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ}
    (hχ : IsGeneralizedEigencharacter ((T.normalizedRefinedOppositeJacquet C D ρ).comp
      ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
        ((C.flatten D).blockScalarLevi F.Carrier))) χ) :
    IsGeneralizedEigencharacter
      ((T.normalizedRefinedJacquet C (reverseRefinement C D) ρ).comp
        ((flattenedLeviEquiv F.Carrier C (reverseRefinement C D)).toMonoidHom.comp
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier)))
      (χ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)) := by
  obtain ⟨k, y, hy0, hy⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  refine (isGeneralizedEigencharacter_iff _ _).mpr
    ⟨k, toUpper C D F.Carrier ρ y, ?_, ?_⟩
  · intro h0
    apply hy0
    rw [← fromUpper_toUpper C D F.Carrier ρ y, h0, map_zero]
  · intro c
    have hy' : (((T.normalizedRefinedOppositeJacquet C D ρ
        (flattenedLeviEquiv F.Carrier C D
          ((C.flatten D).blockScalarLevi F.Carrier
            (c ∘ (reverseLabel C D).symm)))) -
        (χ (c ∘ (reverseLabel C D).symm) : ℂ) • 1) ^ k) y = 0 := hy _
    have key := map_pow_sub_smul (toUpper C D F.Carrier ρ)
      (fun x => toUpper_normalizedRefinedOppositeJacquet T C D ρ c x)
      (χ (c ∘ (reverseLabel C D).symm) : ℂ) k y
    rw [hy', map_zero] at key
    exact key.symm

end Padic

end Langlands.Exponents.RefinedOppositeConeReversal
