import Langlands.CommutativeAlgebra.Popescu.RegularSequenceFlatStatement
import Langlands.Algebra.IdealLocalFlatnessCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Stacks 07DY: a regular system of parameters mapping to a regular sequence gives flatness

The proof inducts on the length of the sequence. For `x = a :: xs`, pass to
`R ⧸ (a)` and `S ⧸ (a)S`; the induction hypothesis gives flatness there, and the
ideal local flatness criterion (Stacks 00ML, `Langlands.Algebra.idealLocalFlatnessCriterion`)
for the ideal `(a)` lifts it to flatness of `S` over `R`.
-/

universe u

open scoped TensorProduct
open TensorProduct IsLocalRing RingTheory.Sequence Pointwise

namespace Langlands.CommutativeAlgebra.Popescu

namespace RegularSequenceFlat

section Tensor

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- If `algebraMap R S a` is a nonzerodivisor on `S`, then the tensor inclusion
`(a) ⊗[R] S → R ⊗[R] S` is injective. Every element of `(a) ⊗[R] S` has the form
`a ⊗ s`, and its image corresponds to `a • s` under `R ⊗[R] S ≃ S`. -/
theorem span_singleton_rTensor_injective (a : R)
    (ha : IsSMulRegular S (algebraMap R S a)) :
    Function.Injective ((Ideal.span {a} : Ideal R).subtype.rTensor S) := by
  let g : (Ideal.span {a} : Ideal R) := ⟨a, Ideal.mem_span_singleton_self a⟩
  have hsurj : ∀ z : (Ideal.span {a} : Ideal R) ⊗[R] S, ∃ s : S, z = g ⊗ₜ[R] s := by
    intro z
    induction z with
    | tmul i s =>
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp i.2
      refine ⟨r • s, ?_⟩
      have hi : i = r • g := Subtype.ext (by simp [g, hr, smul_eq_mul])
      rw [hi, smul_tmul]
    | add z w hz hw =>
      obtain ⟨s, rfl⟩ := hz
      obtain ⟨t, rfl⟩ := hw
      exact ⟨s + t, (tmul_add _ _ _).symm⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨s, rfl⟩ := hsurj z
  have h1 : a • s = 0 := by
    have := congrArg (TensorProduct.lid R S) hz
    simpa [g] using this
  have h2 : s = 0 := by
    apply ha
    change algebraMap R S a • s = algebraMap R S a • 0
    rw [algebraMap_smul, smul_zero]
    exact h1
  rw [h2, tmul_zero]

end Tensor

section Quotient

variable {A : Type u} [CommRing A]

/-- Weak regularity on `QuotSMulTop s A` (an `A`-module) agrees with weak regularity
on the quotient ring `A ⧸ J` of the image sequence, when `J = (s)`. -/
theorem isWeaklyRegular_quotSMulTop_iff (s : A) (J : Ideal A) (hJ : J = Ideal.span {s})
    (rs : List A) :
    IsWeaklyRegular (QuotSMulTop s A) rs ↔
      IsWeaklyRegular (A ⧸ J) (rs.map (Ideal.Quotient.mk J)) := by
  have h : (s • (⊤ : Submodule A A)) = (J : Submodule A A) := by
    rw [hJ, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop s A ≃+ A ⧸ J := (Submodule.quotEquivOfEq _ _ h).toAddEquiv
  refine e.isWeaklyRegular_congr ?_
  refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ q => ?_)
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  rfl

end Quotient

section Local

variable {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R]
  [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- The base case: if the maximal ideal of `R` is zero, then `S` is flat over `R`. -/
theorem flat_of_maximalIdeal_eq_bot (h : maximalIdeal R = ⊥) : Module.Flat R S := by
  have hall : ∀ z : (maximalIdeal R) ⊗[R] S, z = 0 := by
    intro z
    induction z with
    | tmul i s =>
      have hi : i = 0 := by
        apply Subtype.ext
        have hmem : (i : R) ∈ (⊥ : Ideal R) := h ▸ i.2
        exact (Submodule.mem_bot R).mp hmem
      rw [hi, zero_tmul]
    | add z w hz hw => rw [hz, hw, add_zero]
  have hinj : Function.Injective ((maximalIdeal R).subtype.rTensor S) := by
    rw [injective_iff_map_eq_zero]
    intro z _
    exact hall z
  have hflat : Module.Flat (R ⧸ maximalIdeal R) ((R ⧸ maximalIdeal R) ⊗[R] S) := by
    let := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  exact Langlands.Algebra.idealLocalFlatnessCriterion R S S (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top inferInstance hinj hflat

/-- The induction step: if `a ∈ 𝔪_R` maps to a nonzerodivisor of `S` and
`S ⧸ (a)S` is flat over `R ⧸ (a)`, then `S` is flat over `R`. -/
theorem flat_of_flat_quotient (a : R) (ha : a ∈ maximalIdeal R)
    (hSa : IsSMulRegular S (algebraMap R S a))
    (hflat : Module.Flat (R ⧸ Ideal.span {a})
      (S ⧸ (Ideal.span {a}).map (algebraMap R S))) :
    Module.Flat R S := by
  have hI : (Ideal.span {a} : Ideal R) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr ha)
  have hflat' : Module.Flat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] S) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (Ideal.span {a})).symm.toLinearEquiv
  exact Langlands.Algebra.idealLocalFlatnessCriterion R S S (Ideal.span {a}) hI inferInstance
    (span_singleton_rTensor_injective a hSa) hflat'

end Local

/-- Stacks 07DY, by induction on the length of the sequence, for all rings at once. -/
theorem flat_of_length (n : ℕ) :
    ∀ (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R]
      [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
      (x : List R), x.length = n →
      Ideal.ofList x = maximalIdeal R →
      IsWeaklyRegular R x →
      IsWeaklyRegular S (x.map (algebraMap R S)) → Module.Flat R S := by
  induction n with
  | zero =>
    intro R S _ _ _ _ _ _ _ _ x hlen hx _ _
    cases x with
    | nil => exact flat_of_maximalIdeal_eq_bot (hx.symm.trans Ideal.ofList_nil)
    | cons a xs => simp at hlen
  | succ n ih =>
    intro R S _ _ _ _ _ _ _ _ x hlen hx hR hS
    cases x with
    | nil => simp at hlen
    | cons a xs =>
      have hlen' : xs.length = n := by simpa using hlen
      have ha : a ∈ maximalIdeal R := by
        rw [← hx]
        exact Ideal.subset_span (by simp)
      have hI : (Ideal.span {a} : Ideal R) ≠ ⊤ :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr ha)
      have hJ : (Ideal.span {a}).map (algebraMap R S) ≠ ⊤ :=
        ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
          ((Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr ha)).trans
            (map_maximalIdeal_le (algebraMap R S)))
      have : Nontrivial (R ⧸ Ideal.span {a}) := Ideal.Quotient.nontrivial_iff.mpr hI
      have : Nontrivial (S ⧸ (Ideal.span {a}).map (algebraMap R S)) :=
        Ideal.Quotient.nontrivial_iff.mpr hJ
      have : IsLocalRing (R ⧸ Ideal.span {a}) :=
        .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have : IsLocalRing (S ⧸ (Ideal.span {a}).map (algebraMap R S)) :=
        .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      have : IsLocalHom (algebraMap (R ⧸ Ideal.span {a})
          (S ⧸ (Ideal.span {a}).map (algebraMap R S))) := by
        refine ⟨fun r hr => ?_⟩
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        have : IsLocalHom (Ideal.Quotient.mk ((Ideal.span {a}).map (algebraMap R S))) :=
          IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
        change IsUnit (Ideal.Quotient.mk _ (algebraMap R S r)) at hr
        exact (isUnit_of_map_unit (algebraMap R S) r
          (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hr)).map _
      rw [List.map_cons] at hS
      obtain ⟨-, hRxs⟩ := (isWeaklyRegular_cons_iff R a xs).mp hR
      obtain ⟨hSa, hSxs⟩ := (isWeaklyRegular_cons_iff S _ _).mp hS
      refine flat_of_flat_quotient a ha hSa ?_
      refine ih (R ⧸ Ideal.span {a}) (S ⧸ (Ideal.span {a}).map (algebraMap R S))
        (xs.map (Ideal.Quotient.mk _)) (by simpa using hlen') ?_ ?_ ?_
      · rw [← Ideal.map_ofList,
          ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective,
          ← hx, Ideal.ofList_cons, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
      · exact (isWeaklyRegular_quotSMulTop_iff a _ rfl xs).mp hRxs
      · have hJspan : (Ideal.span {a}).map (algebraMap R S) =
            Ideal.span {algebraMap R S a} := by
          rw [Ideal.map_span, Set.image_singleton]
        have h := (isWeaklyRegular_quotSMulTop_iff (algebraMap R S a) _ hJspan
          (xs.map (algebraMap R S))).mp hSxs
        have heq : (xs.map (Ideal.Quotient.mk (Ideal.span {a}))).map
              (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ (Ideal.span {a}).map (algebraMap R S))) =
            (xs.map (algebraMap R S)).map
              (Ideal.Quotient.mk ((Ideal.span {a}).map (algebraMap R S))) := by
          simp only [List.map_map]
          rfl
        rw [heq]
        exact h

end RegularSequenceFlat

/-- Stacks Lemma 10.128.2 (Tag 07DY): if `R → S` is a local homomorphism of Noetherian
local rings, `x` is a weakly regular sequence of `R` generating its maximal ideal, and
the image of `x` is weakly regular on `S`, then `S` is flat over `R`. -/
theorem regularSequenceFlat : RegularSequenceFlatStatement.{u} := by
  intro R S _ _ _ _ _ _ _ _ x hx hR hS
  exact RegularSequenceFlat.flat_of_length x.length R S x rfl hx hR hS

end Langlands.CommutativeAlgebra.Popescu
