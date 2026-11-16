import Langlands.GroupScheme.SplitExistence.Retraction
import Langlands.GroupScheme.SplitExistence.Primitive
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Integral polynomial retractions for ordered root products -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

/-- Primitivity of a finite integral matrix supplies an integral linear functional
which sends the matrix to one. -/
theorem exists_matrix_bezout {ι : Type*} [Fintype ι] (B : Matrix ι ι ℤ)
    (hB : ∀ p : ℕ, p.Prime → B.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ∃ a : ι × ι → ℤ, ∑ pq, a pq * B pq.1 pq.2 = 1 := by
  classical
  let g : ℤ := Finset.univ.gcd (fun pq : ι × ι => B pq.1 pq.2)
  have hg : g.natAbs = 1 := by
    by_contra h
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h
    apply hB p hp
    rw [map_zmod_eq_zero_iff]
    intro c d
    exact (Int.natCast_dvd.mpr hpg).trans (Finset.gcd_dvd (Finset.mem_univ (c, d)))
  obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul Finset.univ (fun pq : ι × ι => B pq.1 pq.2)
  have ha' : ∑ pq, B pq.1 pq.2 * a pq = g := by simpa [g] using ha.symm
  rcases Int.natAbs_eq_iff.mp hg with hg | hg
  · refine ⟨a, ?_⟩
    simpa [mul_comm] using ha'.trans hg
  · refine ⟨fun pq => -a pq, ?_⟩
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [show (∑ pq, a pq * B pq.1 pq.2) = g by simpa only [mul_comm] using ha', hg]
    norm_num

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

/-- Fixed integral coefficients supported on the nonzero entries of `e j 1`,
whose pairing with `e j 1` is one. -/
def integralRootCoeffs (j : J) (pq : Fin D.n × Fin D.n) : ℤ :=
  if D.e j 1 pq.1 pq.2 = 0 then 0
  else (exists_matrix_bezout (D.e j 1) (D.e_one_map_ne_zero j)).choose pq

theorem integralRootCoeffs_zero (j : J) (pq : Fin D.n × Fin D.n)
    (h : D.e j 1 pq.1 pq.2 = 0) : D.integralRootCoeffs j pq = 0 := by
  simp [integralRootCoeffs, h]

theorem integralRootCoeffs_pair (j : J) :
    ∑ pq, D.integralRootCoeffs j pq * D.e j 1 pq.1 pq.2 = 1 := by
  classical
  convert (exists_matrix_bezout (D.e j 1) (D.e_one_map_ne_zero j)).choose_spec using 1
  apply Finset.sum_congr rfl
  intro pq _
  by_cases h : D.e j 1 pq.1 pq.2 = 0 <;> simp [integralRootCoeffs, h]

section Ring

variable {R : Type*} [CommRing R]

/-- An integral linear functional reading the coefficient of one root. -/
def integralRootCoord (j : J) (M : Matrix (Fin D.n) (Fin D.n) R) : R :=
  ∑ pq : Fin D.n × Fin D.n, (D.integralRootCoeffs j pq : R) * M pq.1 pq.2

theorem integralRootCoord_map {R' : Type*} [CommRing R'] (f : R →+* R')
    (j : J) (M : Matrix (Fin D.n) (Fin D.n) R) :
    D.integralRootCoord j (M.map f) = f (D.integralRootCoord j M) := by
  simp [integralRootCoord, map_sum, map_mul]

/-- At entries supporting `e j 1`, the coefficient functional recovers the
scalar multiplying that root operator. -/
theorem integralRootCoord_eq (j : J) (M : Matrix (Fin D.n) (Fin D.n) R) (s : R)
    (hM : ∀ p q, D.e j 1 p q ≠ 0 → M p q = s * (D.e j 1 p q : R)) :
    D.integralRootCoord j M = s := by
  have hp : (∑ pq, (D.integralRootCoeffs j pq : R) * (D.e j 1 pq.1 pq.2 : R)) = 1 := by
    simpa using congrArg (Int.castRingHom R) (D.integralRootCoeffs_pair j)
  calc
    D.integralRootCoord j M =
        ∑ pq, s * ((D.integralRootCoeffs j pq : R) * (D.e j 1 pq.1 pq.2 : R)) := by
      apply Finset.sum_congr rfl
      intro pq _
      by_cases h : D.e j 1 pq.1 pq.2 = 0
      · simp [D.integralRootCoeffs_zero j pq h, h]
      · rw [hM _ _ h]
        ring
    _ = s * ∑ pq, (D.integralRootCoeffs j pq : R) * (D.e j 1 pq.1 pq.2 : R) :=
      (Finset.mul_sum ..).symm
    _ = s := by rw [hp, mul_one]

theorem integralRootCoord_opm_cons {γ : J} {l : List J}
    (hγ : 0 < D.ℓ (P.root γ)) (hlpos : ∀ δ ∈ l, 0 < D.ℓ (P.root δ))
    (hl : ∀ δ ∈ l, D.ℓ (P.root γ) ≤ D.ℓ (P.root δ)) (hγl : γ ∉ l) (c : J → R) :
    D.integralRootCoord γ (D.opm (γ :: l) c) = c γ := by
  apply D.integralRootCoord_eq
  intro p q hpq
  rw [opm_cons]
  apply D.xm_mul_opm_apply hγ hlpos hl hγl
  simpa only [one_smul] using D.e_weight γ 1 p q hpq

variable [DecidableEq J]

/-- Recover coefficients by repeatedly applying the integral linear functional
and removing the recovered root factor. -/
def integralRetrAux : List J → Matrix (Fin D.n) (Fin D.n) R → (J → R) → (J → R)
  | [], _, acc => acc
  | γ :: l, M, acc =>
    integralRetrAux l (D.xm γ (-(D.integralRootCoord γ M)) * M)
      (Function.update acc γ (D.integralRootCoord γ M))

theorem integralRetrAux_opm :
    ∀ (l : List J), l.Nodup → l.Pairwise (fun a c => D.ℓ (P.root a) ≤ D.ℓ (P.root c)) →
    (∀ δ ∈ l, 0 < D.ℓ (P.root δ)) → ∀ (c acc : J → R),
      D.integralRetrAux l (D.opm l c) acc = fun j => if j ∈ l then c j else acc j
  | [], _, _, _, c, acc => by funext j; simp [integralRetrAux]
  | γ :: l, hnd, hsort, hpos, c, acc => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hsort
    have hγ := hpos γ (List.mem_cons_self ..)
    have hlpos : ∀ δ ∈ l, 0 < D.ℓ (P.root δ) := fun δ hδ => hpos δ (List.mem_cons_of_mem _ hδ)
    rw [integralRetrAux, D.integralRootCoord_opm_cons hγ hlpos hsort.1 hnd.1,
      opm_cons, ← mul_assoc, D.xm_mul, neg_add_cancel, D.xm_zero, one_mul,
      integralRetrAux_opm l hnd.2 hsort.2 hlpos c]
    funext j
    by_cases hj : j ∈ l
    · simp [hj]
    · by_cases hjγ : j = γ
      · subst hjγ; simp [hj]
      · simp [hj, hjγ]

theorem integralRetrAux_map {R' : Type*} [CommRing R'] (f : R →+* R') :
    ∀ (l : List J) (M : Matrix (Fin D.n) (Fin D.n) R) (acc : J → R),
      D.integralRetrAux l (M.map f) (f ∘ acc) = f ∘ D.integralRetrAux l M acc
  | [], _, _ => rfl
  | γ :: l, M, acc => by
    have hmap : (D.xm γ (-(D.integralRootCoord γ M)) * M).map f =
        D.xm γ (-(D.integralRootCoord γ (M.map f))) * M.map f := by
      rw [Matrix.map_mul, xm, xm, divExp_map]
      congr 2
      rw [map_neg, D.integralRootCoord_map]
    simp only [integralRetrAux]
    rw [← integralRetrAux_map f l, hmap, Function.comp_update, D.integralRootCoord_map]

section PosList

variable [Fintype J]

/-- An integral polynomial retraction for the ordered positive-root product. -/
def integralRetr (M : Matrix (Fin D.n) (Fin D.n) R) : J → R :=
  D.integralRetrAux D.posList M 0

theorem integralRetr_opm (c : J → R) :
    D.integralRetr (D.opm D.posList c) = fun j => if j ∈ D.posList then c j else 0 :=
  D.integralRetrAux_opm _ D.posList_nodup D.posList_sorted
    (fun _ hδ => D.ℓ_root_pos (D.mem_posList.1 hδ)) c 0

theorem integralRetr_one : D.integralRetr (1 : Matrix (Fin D.n) (Fin D.n) R) = 0 := by
  rw [← D.opm_zero D.posList, integralRetr_opm]
  funext j
  simp

theorem integralRetr_map {R' : Type*} [CommRing R'] (f : R →+* R')
    (M : Matrix (Fin D.n) (Fin D.n) R) :
    D.integralRetr (M.map f) = f ∘ D.integralRetr M := by
  rw [integralRetr, integralRetr, ← integralRetrAux_map]
  congr 1
  funext j
  simp

end PosList
end Ring
end ChevalleyData
end Langlands.GroupScheme.SplitExistence
