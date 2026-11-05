import Langlands.GroupScheme.SplitExistence.CommutatorOde
import Langlands.GroupScheme.SplitExistence.Integrality

/-! # The commutator relations for root exponentials over every commutative ring

Over `ℚ[t][s]` the commutator `x_γ(s) x_δ(t) x_γ(-s) x_δ(-t)` is an ordered product of root
exponentials of roots `a • root γ + c • root δ` (`a, c ≥ 1`) with distinct roots and
nondecreasing `h`-values (`exists_list_commutator_poly`). Its entries lie in `ℤ[t][s]`, so by
integrality peeling all parameters of the product lie in `ℤ[t][s]`; by injectivity of
`ℤ[t][s] → ℚ[t][s]` the identity already holds over `ℤ[t][s]`, and evaluating `s` and `t` gives
it over every commutative ring. -/

noncomputable section

universe u

open Matrix Polynomial

namespace Langlands.GroupScheme.SplitExistence

/-- A list of pairs whose second components lie in the range of a ring homomorphism `f` is the
image under `f` of a list. -/
theorem exists_list_lift {J S T : Type*} [Ring S] [Ring T] (f : S →+* T) :
    ∀ L : List (J × T), (∀ p ∈ L, p.2 ∈ f.range) →
      ∃ L' : List (J × S), L'.map (fun p => (p.1, f p.2)) = L := by
  intro L
  induction L with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons q L ih =>
    intro hL
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp (hL q (List.mem_cons_self ..))
    obtain ⟨L', hL'⟩ := ih fun p hp => hL p (List.mem_cons_of_mem _ hp)
    exact ⟨(q.1, a) :: L', by rw [List.map_cons, hL', ha]⟩

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}

namespace LieRootData

variable (D : LieRootData P)

/-- Applying a ring homomorphism to an ordered product of root exponentials applies it to the
parameters. -/
theorem prod_map_ringHom {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T)
    (L : List (J × S)) :
    (L.map fun p => divExp (D.e p.1) p.2).prod.map φ =
      ((L.map fun p => (p.1, φ p.2)).map fun p => divExp (D.e p.1) p.2).prod := by
  change φ.mapMatrix _ = _
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  simp only [Function.comp_apply, RingHom.mapMatrix_apply, divExp_map]

/-- The commutator `x_γ(s) x_δ(t) x_γ(-s) x_δ(-t)` over `ℤ[t][s]` is an ordered product of root
exponentials of roots `a • root γ + c • root δ` (`a, c ≥ 1`) with distinct roots and
nondecreasing `h`-values. -/
theorem exists_list_commutator_int [Finite J] (h : X →+ ℤ) {γ δ : J}
    (hγ : 0 < h (P.root γ)) (hδ : 0 < h (P.root δ)) :
    ∃ L : List (J × ℤ[X][X]), (∀ p ∈ L, p.1 ∈ commRoots P γ δ) ∧
      L.Pairwise (fun p q => p.1 ≠ q.1 ∧ h (P.root p.1) ≤ h (P.root q.1)) ∧
      divExp (D.e γ) (Polynomial.X : ℤ[X][X]) * divExp (D.e δ) (C Polynomial.X : ℤ[X][X]) *
          divExp (D.e γ) (-Polynomial.X : ℤ[X][X]) * divExp (D.e δ) (-C (Polynomial.X : ℤ[X])) =
        (L.map fun p => divExp (D.e p.1) p.2).prod := by
  set ι : ℤ[X][X] →+* ℚ[X][X] := mapRingHom (mapRingHom (Int.castRingHom ℚ)) with hι
  have hιinj : Function.Injective ι := by
    rw [hι, coe_mapRingHom]
    refine Polynomial.map_injective _ ?_
    rw [coe_mapRingHom]
    exact Polynomial.map_injective _ (Int.castRingHom ℚ).injective_int
  obtain ⟨L, hL₁, hL₂, hL₃⟩ := D.exists_list_commutator_poly (A := ℚ[X]) h hγ hδ Polynomial.X
  set c := divExp (D.e γ) (Polynomial.X : ℤ[X][X]) * divExp (D.e δ) (C Polynomial.X : ℤ[X][X]) *
    divExp (D.e γ) (-Polynomial.X : ℤ[X][X]) * divExp (D.e δ) (-C (Polynomial.X : ℤ[X])) with hc
  have hcι : c.map ι = divExp (D.e γ) (Polynomial.X : ℚ[X][X]) *
      divExp (D.e δ) (C Polynomial.X : ℚ[X][X]) * divExp (D.e γ) (-Polynomial.X : ℚ[X][X]) *
      divExp (D.e δ) (-C (Polynomial.X : ℚ[X])) := by
    rw [hc, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, divExp_map, divExp_map, divExp_map,
      divExp_map]
    simp [hι]
  have hmem : ∀ p ∈ L, p.2 ∈ ι.range := by
    refine D.mem_of_prod_mem h ι.range L (fun p hp => commRoots_pos h hγ hδ (hL₁ p hp)) hL₂ ?_
    intro a b
    rw [← hL₃, ← hcι]
    exact ⟨c a b, rfl⟩
  obtain ⟨L', rfl⟩ := exists_list_lift ι L hmem
  refine ⟨L', fun p hp => hL₁ _ (List.mem_map_of_mem hp), ?_, ?_⟩
  · rw [List.pairwise_map] at hL₂
    exact hL₂
  · refine Matrix.map_injective hιinj ?_
    exact (hcι.trans hL₃).trans (D.prod_map_ringHom ι L').symm

/-- **Commutator relations.** Let `h : X →+ ℤ` be positive on the roots `j` and `j'`. Over every
commutative ring `R`, the commutator `x_j(s) x_j'(t) x_j(-s) x_j'(-t)` is an ordered product of
root exponentials of roots of the form `a • root j + c • root j'` with `a, c ≥ 1`. -/
theorem commutator [Finite J] (h : X →+ ℤ) {j j' : J} (hj : 0 < h (P.root j))
    (hj' : 0 < h (P.root j')) (R : Type*) [CommRing R] (s t : R) :
    ∃ L : List (J × R),
      (∀ x ∈ L, ∃ a c : ℕ, 1 ≤ a ∧ 1 ≤ c ∧ P.root x.1 = a • P.root j + c • P.root j') ∧
      divExp (D.e j) s * divExp (D.e j') t * divExp (D.e j) (-s) * divExp (D.e j') (-t) =
        (L.map fun x => divExp (D.e x.1) x.2).prod := by
  obtain ⟨L, hL₁, -, hL₃⟩ := D.exists_list_commutator_int h hj hj'
  set φ : ℤ[X][X] →+* R := eval₂RingHom (eval₂RingHom (Int.castRingHom R) t) s with hφ
  refine ⟨L.map fun p => (p.1, φ p.2), ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hL₁ p hp
  · rw [← D.prod_map_ringHom φ, ← hL₃, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, divExp_map,
      divExp_map, divExp_map, divExp_map]
    simp [hφ]

end LieRootData

end Langlands.GroupScheme.SplitExistence
