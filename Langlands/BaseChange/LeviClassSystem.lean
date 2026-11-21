import Langlands.BaseChange.RegularLeviNormRepresentative
import Langlands.BaseChange.RegularSemisimpleOrbit
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Levi class systems in a regular semisimple conjugacy class -/

noncomputable section

open Polynomial

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands

universe u

variable {K : Type u} [Field K] {n : ℕ} (B : BlockShape n)

/-- `m` is a system of representatives, without repetition, of the `M(K)`-conjugacy classes
of the elements of the standard block Levi `M = B.Levi K` whose block diagonal embedding is
`GL_n(K)`-conjugate to `γ`. -/
def IsLeviClassSystem (γ : GeneralLinear n K) {k : ℕ} (m : Fin k → B.Levi K) : Prop :=
  (∀ j, ∃ x : GeneralLinear n K, x⁻¹ * γ * x = B.leviEmbedding K (m j)) ∧
  (∀ j j', (∃ y : B.Levi K, y⁻¹ * m j * y = m j') → j = j') ∧
  ∀ m' : B.Levi K, (∃ x : GeneralLinear n K, x⁻¹ * γ * x = B.leviEmbedding K m') →
    ∃ j, ∃ y : B.Levi K, y⁻¹ * m j * y = m'

omit [Field K] in
/-- Conjugation does not change the characteristic polynomial. -/
theorem charpoly_conj {K : Type u} [CommRing K] {r : ℕ} (x g : GeneralLinear r K) :
    ((x⁻¹ * g * x : GeneralLinear r K) : Matrix (Fin r) (Fin r) K).charpoly =
      (g : Matrix (Fin r) (Fin r) K).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, Units.mul_inv_cancel_left]

/-- Conjugation preserves regular semisimplicity. -/
theorem isRegularSemisimple_conj {r : ℕ} {g : GeneralLinear r K} (hg : IsRegularSemisimple g)
    (x : GeneralLinear r K) : IsRegularSemisimple (x⁻¹ * g * x) := by
  unfold IsRegularSemisimple
  rw [charpoly_conj]
  exact hg

/-- A block of a block diagonal element with separable characteristic polynomial has a
separable characteristic polynomial dividing it. -/
theorem charpoly_dvd_of_leviEmbedding (m : B.Levi K) (i : Fin B.length) :
    (m i : Matrix (Fin (B.size i)) (Fin (B.size i)) K).charpoly ∣
      (B.leviEmbedding K m : Matrix (Fin n) (Fin n) K).charpoly := by
  rw [charpoly_leviEmbedding]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- The blocks of a regular semisimple block diagonal element are regular semisimple. -/
theorem isRegularSemisimple_block {m : B.Levi K}
    (hm : IsRegularSemisimple (B.leviEmbedding K m)) (i : Fin B.length) :
    IsRegularSemisimple (m i) :=
  Polynomial.Separable.of_dvd hm (charpoly_dvd_of_leviEmbedding B m i)

private theorem charpoly_levi_conj (m y : B.Levi K) (i : Fin B.length) :
    ((y⁻¹ * m * y) i : Matrix (Fin (B.size i)) (Fin (B.size i)) K).charpoly =
      (m i : Matrix (Fin (B.size i)) (Fin (B.size i)) K).charpoly :=
  charpoly_conj (y i) (m i)

/-- Block diagonal elements in a regular semisimple class with the same block characteristic
polynomials are conjugate in the Levi. -/
private theorem exists_levi_conj_of_charpoly_eq {γ : GeneralLinear n K}
    (hγ : IsRegularSemisimple γ) {m m' : B.Levi K}
    (hm : ∃ x : GeneralLinear n K, x⁻¹ * γ * x = B.leviEmbedding K m)
    (hc : ∀ i, (m' i : Matrix (Fin (B.size i)) (Fin (B.size i)) K).charpoly =
      (m i : Matrix (Fin (B.size i)) (Fin (B.size i)) K).charpoly) :
    ∃ y : B.Levi K, y⁻¹ * m * y = m' := by
  obtain ⟨x, hx⟩ := hm
  have hreg : IsRegularSemisimple (B.leviEmbedding K m) := hx ▸ isRegularSemisimple_conj hγ x
  have hconj : ∀ i, ∃ g : GeneralLinear (B.size i) K,
      (g : Matrix (Fin (B.size i)) (Fin (B.size i)) K) * (m i : Matrix _ _ K) *
        ((g⁻¹ : GeneralLinear (B.size i) K) : Matrix _ _ K) = (m' i : Matrix _ _ K) :=
    fun i => exists_matrix_conj_of_charpoly_eq_of_separable _ _
      (isRegularSemisimple_block B hreg i) (hc i)
  choose g hg using hconj
  refine ⟨g⁻¹, ?_⟩
  funext i
  apply Units.ext
  simp only [Pi.mul_apply, Pi.inv_apply, inv_inv, Units.val_mul]
  exact hg i

/-- Every regular semisimple element has a finite Levi class system. -/
theorem exists_isLeviClassSystem {γ : GeneralLinear n K} (hγ : IsRegularSemisimple γ) :
    ∃ (k : ℕ) (m : Fin k → B.Levi K), IsLeviClassSystem B γ m := by
  classical
  let χ : K[X] := (γ : Matrix (Fin n) (Fin n) K).charpoly
  have hχ : χ ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  let S : Set (B.Levi K) :=
    {m | ∃ x : GeneralLinear n K, x⁻¹ * γ * x = B.leviEmbedding K m}
  let c : B.Levi K → (Fin B.length → K[X]) :=
    fun m i => (m i : Matrix (Fin (B.size i)) (Fin (B.size i)) K).charpoly
  have hcS : ∀ m ∈ S, ∀ i, c m i ∈ {g : K[X] | g.Monic ∧ g ∣ χ} := by
    rintro m ⟨x, hx⟩ i
    refine ⟨Matrix.charpoly_monic _, ?_⟩
    have h := charpoly_dvd_of_leviEmbedding B m i
    rwa [← hx, charpoly_conj] at h
  have hD : ({g : K[X] | g.Monic ∧ g ∣ χ} : Set K[X]).Finite := by
    have : Finite {g : K[X] // g.Monic ∧ g ∣ χ} :=
      @Finite.of_fintype _ (Polynomial.fintypeSubtypeMonicDvd χ hχ)
    exact this
  let T : Set (Fin B.length → K[X]) := c '' S
  have hT : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin B.length => {g : K[X] | g.Monic ∧ g ∣ χ})
      (fun _ => hD)).subset ?_
    rintro _ ⟨m, hm, rfl⟩ i -
    exact hcS m hm i
  let s := hT.toFinset
  let e := s.equivFin
  have hpre : ∀ j : Fin s.card, ∃ m, m ∈ S ∧ c m = (e.symm j : Fin B.length → K[X]) := by
    intro j
    have h := (e.symm j).2
    rw [Set.Finite.mem_toFinset] at h
    obtain ⟨m, hm, hcm⟩ := h
    exact ⟨m, hm, hcm⟩
  choose m hmS hmc using hpre
  refine ⟨s.card, m, hmS, ?_, ?_⟩
  · rintro j j' ⟨y, hy⟩
    have hcc : c (m j') = c (m j) := by
      funext i
      rw [← hy]
      exact charpoly_levi_conj B (m j) y i
    rw [hmc, hmc] at hcc
    exact (e.symm.injective (Subtype.ext hcc)).symm
  · intro m' hm'
    have hmem : c m' ∈ s := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨m', hm', rfl⟩
    refine ⟨e ⟨c m', hmem⟩, ?_⟩
    have hc : c (m (e ⟨c m', hmem⟩)) = c m' := by
      rw [hmc, Equiv.symm_apply_apply]
    exact exists_levi_conj_of_charpoly_eq B hγ (hmS _) (fun i => congrFun hc.symm i)

end Langlands.BaseChange
