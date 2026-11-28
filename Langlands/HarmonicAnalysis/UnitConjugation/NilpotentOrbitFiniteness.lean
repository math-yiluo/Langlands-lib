import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentEndomorphismConjugacy
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-! # Finiteness of nilpotent conjugacy classes in a semisimple ring -/

namespace Langlands.HarmonicAnalysis.UnitConjugation

open LinearMap Module MulOpposite

universe u v

/-- A finite collection of nilpotents represents all the nilpotent orbits under
conjugation by units. -/
def HasFiniteNilpotentConjugacyRepresentatives (R : Type v) [Ring R] : Prop :=
  ∃ s : Finset R, (∀ N ∈ s, IsNilpotent N) ∧
    ∀ X : R, IsNilpotent X → ∃ N ∈ s, ∃ u : Rˣ, (u : R) * N * ↑(u⁻¹) = X

private theorem end_hasFiniteNilpotentConjugacyRepresentatives
    (D : Type u) [DivisionRing D] (V : Type v) [AddCommGroup V] [Module D V]
    [FiniteDimensional D V] : HasFiniteNilpotentConjugacyRepresentatives (End D V) := by
  classical
  let d := finrank D V
  have pow_dim_eq_zero (f : End D V) (hf : IsNilpotent f) : f ^ d = 0 := by
    obtain ⟨n, hn⟩ := hf
    ext x
    change x ∈ ker (f ^ d)
    exact Module.End.ker_pow_le_ker_pow_finrank f n (by simp [hn])
  let ranks (f : {f : End D V // IsNilpotent f}) : Fin (d + 1) → Fin (d + 1) :=
    fun m => ⟨finrank D (range (f.val ^ m.val)), Nat.lt_succ_of_le (Submodule.finrank_le _)⟩
  choose rep hrep using (fun r : Set.range ranks => r.property)
  refine ⟨Finset.univ.image (fun r => (rep r).val), ?_, ?_⟩
  · intro N hN
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hN
    exact (rep r).property
  · intro X hX
    let x : {f : End D V // IsNilpotent f} := ⟨X, hX⟩
    let r : Set.range ranks := ⟨ranks x, x, rfl⟩
    refine ⟨(rep r).val, Finset.mem_image_of_mem _ (Finset.mem_univ r), ?_⟩
    obtain ⟨e, he⟩ := exists_intertwiningEquiv_of_nilpotent_rank_powers (rep r).val X
      (rep r).property hX (fun m => by
        by_cases hm : m ≤ d
        · let j : Fin (d + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
          exact congrArg (fun a => (a j).val) (hrep r)
        · have hdm : d ≤ m := le_of_lt (lt_of_not_ge hm)
          rw [pow_eq_zero_of_le hdm (pow_dim_eq_zero _ (rep r).property),
            pow_eq_zero_of_le hdm (pow_dim_eq_zero _ hX)])
    refine ⟨GeneralLinearGroup.ofLinearEquiv e, ?_⟩
    ext y
    change e ((rep r).val (e.symm y)) = X y
    rw [he, e.apply_symm_apply]

private theorem hasFiniteNilpotentConjugacyRepresentatives_of_ringEquiv
    {R : Type u} {S : Type v} [Ring R] [Ring S] (e : R ≃+* S)
    (h : HasFiniteNilpotentConjugacyRepresentatives R) :
    HasFiniteNilpotentConjugacyRepresentatives S := by
  classical
  obtain ⟨s, hs, hrep⟩ := h
  refine ⟨s.image e, ?_, ?_⟩
  · intro N hN
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hN
    exact (hs M hM).map e
  · intro X hX
    obtain ⟨N, hN, u, hu⟩ := hrep (e.symm X) (hX.map e.symm)
    refine ⟨e N, Finset.mem_image_of_mem _ hN, Units.map e.toMonoidHom u, ?_⟩
    change e (u : R) * e N * e (↑(u⁻¹) : R) = X
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hu

private theorem hasFiniteNilpotentConjugacyRepresentatives_op
    {R : Type v} [Ring R] (h : HasFiniteNilpotentConjugacyRepresentatives R) :
    HasFiniteNilpotentConjugacyRepresentatives Rᵐᵒᵖ := by
  classical
  obtain ⟨s, hs, hrep⟩ := h
  refine ⟨s.image op, ?_, ?_⟩
  · intro N hN
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hN
    exact (hs M hM).op
  · intro X hX
    obtain ⟨N, hN, u, hu⟩ := hrep X.unop hX.unop
    refine ⟨op N, Finset.mem_image_of_mem _ hN, Units.opEquiv.symm (op u⁻¹), ?_⟩
    apply MulOpposite.unop_injective
    change (u : R) * (N * ↑(u⁻¹)) = X.unop
    rw [← mul_assoc, hu]

private theorem hasFiniteNilpotentConjugacyRepresentatives_pi
    {ι : Type u} [Fintype ι] {R : ι → Type v} [∀ i, Ring (R i)]
    (h : ∀ i, HasFiniteNilpotentConjugacyRepresentatives (R i)) :
    HasFiniteNilpotentConjugacyRepresentatives (∀ i, R i) := by
  classical
  choose s hs hrep using h
  let val (N : ∀ i, s i) (i : ι) : R i := (N i).val
  refine ⟨Finset.univ.image val, ?_, ?_⟩
  · intro N hN
    obtain ⟨M, _, rfl⟩ := Finset.mem_image.mp hN
    choose n hn using (fun i => hs i (val M i) (M i).property)
    refine ⟨∑ i, n i, funext fun i => ?_⟩
    change (val M i) ^ (∑ j, n j) = 0
    exact pow_eq_zero_of_le (Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
      (Finset.mem_univ i)) (hn i)
  · intro X hX
    choose N hN u hu using (fun i => hrep i (X i) (hX.map (Pi.evalRingHom R i)))
    let M : ∀ i, s i := fun i => ⟨N i, hN i⟩
    refine ⟨val M, Finset.mem_image_of_mem _ (Finset.mem_univ M), MulEquiv.piUnits.symm u,
      funext fun i => ?_⟩
    exact hu i

/-- Every semisimple ring has finitely many nilpotent conjugacy classes. -/
def NilpotentOrbitFinitenessStatement : Prop :=
  ∀ (R : Type v) [Ring R] [IsSemisimpleRing R],
    HasFiniteNilpotentConjugacyRepresentatives R

/-- Reduce by Wedderburn–Artin to matrix rings over division rings, using ranks of
powers on each factor. -/
theorem nilpotentOrbitFiniteness : NilpotentOrbitFinitenessStatement.{v} := by
  intro R _ _
  obtain ⟨n, D, d, hD, _, ⟨e⟩⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
  let (i : Fin n) : DivisionRing (D i) := hD i
  apply hasFiniteNilpotentConjugacyRepresentatives_of_ringEquiv e.symm
  refine hasFiniteNilpotentConjugacyRepresentatives_pi fun i => ?_
  exact hasFiniteNilpotentConjugacyRepresentatives_of_ringEquiv
    (matrixRingEquivEndVecMulOpposite (ι := Fin (d i)) (A := D i)).symm
    (hasFiniteNilpotentConjugacyRepresentatives_op
      (end_hasFiniteNilpotentConjugacyRepresentatives (D i) (Fin (d i) → D i)))

end Langlands.HarmonicAnalysis.UnitConjugation
