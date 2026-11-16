import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.LinearAlgebra.CartanDNumbering

/-! # The full absolute Galois star action on a numbered type-D diagram -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

private theorem numberedStar_preserves_D {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    ∀ i j, CartanMatrix.D n (d.numberedStar e σ i) (d.numberedStar e σ j) =
      CartanMatrix.D n i j := by
  intro i j
  calc
    CartanMatrix.D n (d.numberedStar e σ i) (d.numberedStar e σ j) =
        d.cartan (d.star σ (e.symm i)) (d.star σ (e.symm j)) := (hD _ _).symm
    _ = d.cartan (e.symm i) (e.symm j) := d.cartan_star σ _ _
    _ = CartanMatrix.D n i j := by simpa using hD (e.symm i) (e.symm j)

/-- Every full Galois element fixes the fork center, including in rank four. -/
theorem star_fixes_center_of_D {n : ℕ} (hn : 4 ≤ n) (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex)
    (ha : (e a).val + 3 = n) : d.star σ a = a := by
  apply e.injective
  have h := Langlands.CartanDNumbering.fixes_center hn (d.numberedStar e σ)
    (d.numberedStar_preserves_D e hD σ)
  have hea : e a = ⟨n - 3, by omega⟩ := by
    apply Fin.ext
    change (e a).val = n - 3
    omega
  rw [← hea] at h
  simpa using h

/-- In ranks at least five the full star action fixes every nonfork vertex. -/
theorem star_fixes_nonfork_of_D {n : ℕ} (hn : 5 ≤ n) (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex)
    (ha : (e a).val + 2 < n) : d.star σ a = a := by
  apply e.injective
  have h := Langlands.CartanDNumbering.fixes_nonfork hn (d.numberedStar e σ)
    (d.numberedStar_preserves_D e hD σ) (e a) ha
  simpa using h

/-- With fixed nonfork vertices, each full Galois element acts globally by
identity or by the transposition of the two fork tips. -/
theorem star_cases_of_D_of_fixes_nonfork {n : ℕ} (hn : 4 ≤ n)
    (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hfix : ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star σ a = a)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (∀ a, e (d.star σ a) = e a) ∨
      (∀ a, e (d.star σ a) = Langlands.CartanDNumbering.forkSwap n (by omega) (e a)) := by
  have hfix' : ∀ i : Fin n, i.val + 2 < n → d.numberedStar e σ i = i := by
    intro i hi
    simpa using congrArg e (hfix σ (e.symm i) (by simpa using hi))
  rcases Langlands.CartanDNumbering.eq_id_or_swap_of_fixes_nonfork hn
      (d.numberedStar e σ) (d.numberedStar_preserves_D e hD σ) hfix' with hid | hswap
  · left
    intro a
    simpa using hid (e a)
  · right
    intro a
    simpa [Langlands.CartanDNumbering.forkSwap] using hswap (e a)

/-- In ranks at least five the two global star possibilities require no
supplied fixation assumption. -/
theorem star_cases_of_D {n : ℕ} (hn : 5 ≤ n) (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (∀ a, e (d.star σ a) = e a) ∨
      (∀ a, e (d.star σ a) = Langlands.CartanDNumbering.forkSwap n (by omega) (e a)) :=
  d.star_cases_of_D_of_fixes_nonfork (by omega) e hD
    (d.star_fixes_nonfork_of_D hn e hD) σ

/-- A nontrivial full star action with fixed nonfork vertices has exactly
identity and the fork-tip transposition as its image. -/
theorem starImagePair_of_D_of_fixes_nonfork {n : ℕ} (hn : 4 ≤ n)
    (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hfix : ∀ (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star σ a = a)
    (hnot : ¬ d.StarIsTrivial) :
    d.StarImagePair e (Langlands.CartanDNumbering.forkSwap n (by omega)) := by
  classical
  have hcases := d.star_cases_of_D_of_fixes_nonfork hn e hD hfix
  have hex : ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      ∃ a : d.Vertex, d.star σ a ≠ a := by
    simpa only [StarIsTrivial, not_forall] using hnot
  obtain ⟨σ, a, ha⟩ := hex
  have hswap := (hcases σ).resolve_left (fun hid => ha (e.injective (hid a)))
  refine ⟨?_, hcases, ⟨σ, hswap⟩⟩
  intro h
  apply ha
  apply e.injective
  simpa only [h, Equiv.Perm.one_apply] using hswap a

/-- In ranks at least five a nontrivial full star action has the exact
two-permutation image, without a supplied nonfork-fixation assumption. -/
theorem starImagePair_of_D {n : ℕ} (hn : 5 ≤ n) (e : d.Vertex ≃ Fin n)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) :
    d.StarImagePair e (Langlands.CartanDNumbering.forkSwap n (by omega)) :=
  d.starImagePair_of_D_of_fixes_nonfork (by omega) e hD
    (d.star_fixes_nonfork_of_D hn e hD) hnot

end Langlands.GroupScheme.TitsIndexData
