import Langlands.Shimura.Unitary.HarrisLevelFreePositive
import Langlands.Shimura.Unitary.TorsionFreeLevels

/-!
# Harris's (4.5) for sufficiently small levels of a definite group

Harris (1999, p.310) assumes that `K^{ℓ,p}` is "sufficiently small so that (4.5)" holds. This
module shows that such levels exist inside every compact open level. Fix a place `v` over a prime
`q ≥ 3` different from `ℓ` and `p`. Shrinking a compact open `L₀ ≤ σ(A_f^{ℓp})` to the elements
whose component at `v` lies in the principal congruence level modulo `q` gives a compact open
level `smallAwayLevel` that is torsion-free at `v`. For a positive involution, Harris's (4.5)
then holds for all compact `K_ℓ` and `C_p` (`HarrisDividingLevelFree.of_smallAwayLevel`), and
such levels exist below every compact open `L₀` (`exists_harrisDividingLevelFree`).
-/

noncomputable section

open Langlands.Global Langlands.Shimura.SmallLevels
open scoped NumberField

set_option autoImplicit false

universe v

namespace Langlands.Shimura.DefiniteForms

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]

/-- The component at a place not dividing `n` is continuous on `σ(A_f^n)`. -/
theorem continuous_primeToLocalMap (n : ℕ) (v : PrimeToFinitePlace n) :
    Continuous (primeToLocalMap σ n v) :=
  σ.continuous_pointsMap _ (RestrictedProduct.continuous_eval v)

/-- The away level `L₀` shrunk at a place `v ∤ n`: the elements of `L₀` whose component at `v`
lies in the principal congruence level modulo `q`. -/
def smallAwayLevel (n : ℕ) (v : PrimeToFinitePlace n) (q : ℕ)
    (L₀ : Subgroup (σ.PrimeToPoints n)) : Subgroup (σ.PrimeToPoints n) :=
  L₀ ⊓ (SmallLevels.congruenceLevel σ v.1 q).comap (primeToLocalMap σ n v)

variable {σ}

theorem smallAwayLevel_le {n : ℕ} {v : PrimeToFinitePlace n} {q : ℕ}
    {L₀ : Subgroup (σ.PrimeToPoints n)} : smallAwayLevel σ n v q L₀ ≤ L₀ :=
  inf_le_left

/-- The shrunk level is open when `L₀` is. -/
theorem isOpen_smallAwayLevel {n : ℕ} (v : PrimeToFinitePlace n) {q : ℕ} (hq : q ≠ 0)
    {L₀ : Subgroup (σ.PrimeToPoints n)} (hL₀ : IsOpen (L₀ : Set (σ.PrimeToPoints n))) :
    IsOpen (smallAwayLevel σ n v q L₀ : Set (σ.PrimeToPoints n)) :=
  hL₀.inter ((SmallLevels.isOpen_congruenceLevel σ v.1 hq).preimage
    (continuous_primeToLocalMap σ n v))

/-- The shrunk level is compact when `L₀` is: it is the intersection of `L₀` with an open, hence
closed, subgroup. -/
theorem isCompact_smallAwayLevel {n : ℕ} (v : PrimeToFinitePlace n) {q : ℕ} (hq : q ≠ 0)
    {L₀ : Subgroup (σ.PrimeToPoints n)} (hL₀ : IsCompact (L₀ : Set (σ.PrimeToPoints n))) :
    IsCompact (smallAwayLevel σ n v q L₀ : Set (σ.PrimeToPoints n)) := by
  have hW : IsOpen (((SmallLevels.congruenceLevel σ v.1 q).comap (primeToLocalMap σ n v) :
      Subgroup (σ.PrimeToPoints n)) : Set (σ.PrimeToPoints n)) :=
    (SmallLevels.isOpen_congruenceLevel σ v.1 hq).preimage (continuous_primeToLocalMap σ n v)
  exact hL₀.inter_right (Subgroup.isClosed_of_isOpen _ hW)

/-- For a prime `q ≥ 3` contained in `v`, the level `e⁻¹ (1 × L)` with `L` the shrunk level is
torsion-free at `v`. -/
theorem levelTorsionFreeAt_smallAwayLevel [Nontrivial A] {n : ℕ} (hn : n ≠ 0)
    (v : PrimeToFinitePlace n) {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q)
    (hv : (q : 𝓞 ℚ) ∈ v.1.asIdeal) (L₀ : Subgroup (σ.PrimeToPoints n)) :
    LevelTorsionFreeAt σ v.1 (splitLevel σ n hn ⊥ (smallAwayLevel σ n v q L₀)) :=
  levelTorsionFreeAt_splitLevel v (SmallLevels.congruenceLevel_torsionFree σ hq hq3 hv)
    fun _ hx => hx.2

section Pair

variable {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
  {vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal}}
  {vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}}

include hℓ hp in
/-- A place over a prime `q` different from `ℓ` and `p`, as a place not dividing `ℓ p`. -/
def awayPlace {q : ℕ} (hq : q.Prime) (hqℓ : q ≠ ℓ) (hqp : q ≠ p) (v : FinitePlace ℚ)
    (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) : PrimeToFinitePlace (ℓ * p) :=
  ⟨v, fun h => ((natCast_mul_mem_asIdeal_iff v).1 h).elim
    (fun h' => not_natCast_mem_and_natCast_mem hq hℓ hqℓ v ⟨hv, h'⟩)
    (fun h' => not_natCast_mem_and_natCast_mem hq hp hqp v ⟨hv, h'⟩)⟩

include hℓ hp hℓp in
/-- Harris's (4.5) for a sufficiently small level of a definite group (1999, p.310): for distinct
primes `ℓ` and `p`, a place `v` over a prime `q ≥ 3` different from `ℓ` and `p`, a positive
involution, compact `K_ℓ` and `C_p`, and a compact `L₀`, the shrunk level `K^{ℓ,p}` satisfies
(4.5). -/
theorem HarrisDividingLevelFree.of_smallAwayLevel [Nontrivial A] (hn : ℓ * p ≠ 0)
    (hpos : (σ.baseChange ℝ).IsPositive) {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (hqℓ : q ≠ ℓ)
    (hqp : q ≠ p) (v : FinitePlace ℚ) (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    {Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1))}
    {Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))}
    (hKℓ : IsCompact (Kℓ : Set (σ.Points (FiniteCompletion ℚ vℓ.1))))
    (hCp : IsCompact (Cp : Set (σ.Points (FiniteCompletion ℚ vp.1))))
    {L₀ : Subgroup (σ.PrimeToPoints (ℓ * p))}
    (hL₀ : IsCompact (L₀ : Set (σ.PrimeToPoints (ℓ * p)))) :
    HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp
      (smallAwayLevel σ (ℓ * p) (awayPlace hℓ hp hq hqℓ hqp v hv) q L₀) :=
  HarrisDividingLevelFree.of_isPositive hℓ hp hℓp hn hpos hKℓ hCp
    (isCompact_smallAwayLevel _ hq.ne_zero hL₀) v
    (fun h => not_natCast_mem_and_natCast_mem hq hℓ hqℓ v ⟨hv, h⟩)
    (fun h => not_natCast_mem_and_natCast_mem hq hp hqp v ⟨hv, h⟩)
    (levelTorsionFreeAt_smallAwayLevel hn (awayPlace hℓ hp hq hqℓ hqp v hv) hq hq3 hv L₀)

include hℓ hp hℓp in
/-- **Sufficiently small levels exist.** For a positive involution of a nonzero algebra and
distinct primes `ℓ`, `p`, every compact open `L₀ ≤ σ(A_f^{ℓp})` contains a compact open `L` such
that Harris's (4.5) holds for `L` and all compact `K_ℓ` and `C_p`. -/
theorem exists_harrisDividingLevelFree [Nontrivial A] (hn : ℓ * p ≠ 0)
    (hpos : (σ.baseChange ℝ).IsPositive) {L₀ : Subgroup (σ.PrimeToPoints (ℓ * p))}
    (hL₀o : IsOpen (L₀ : Set (σ.PrimeToPoints (ℓ * p))))
    (hL₀c : IsCompact (L₀ : Set (σ.PrimeToPoints (ℓ * p)))) :
    ∃ L ≤ L₀, IsOpen (L : Set (σ.PrimeToPoints (ℓ * p))) ∧
      IsCompact (L : Set (σ.PrimeToPoints (ℓ * p))) ∧
      ∀ (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
        (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))),
        IsCompact (Kℓ : Set (σ.Points (FiniteCompletion ℚ vℓ.1))) →
        IsCompact (Cp : Set (σ.Points (FiniteCompletion ℚ vp.1))) →
        HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L := by
  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (ℓ + p + 3)
  have hq3 : 3 ≤ q := by omega
  have hqℓ : q ≠ ℓ := by omega
  have hqp : q ≠ p := by omega
  obtain ⟨v, hv, -⟩ := existsUnique_finitePlace_natCast_mem q hq
  refine ⟨smallAwayLevel σ (ℓ * p) (awayPlace hℓ hp hq hqℓ hqp v hv) q L₀, smallAwayLevel_le,
    isOpen_smallAwayLevel _ hq.ne_zero hL₀o, isCompact_smallAwayLevel _ hq.ne_zero hL₀c,
    fun Kℓ Cp hKℓ hCp => ?_⟩
  exact HarrisDividingLevelFree.of_smallAwayLevel hℓ hp hℓp hn hpos hq hq3 hqℓ hqp v hv hKℓ hCp hL₀c

end Pair

end Langlands.Shimura.DefiniteForms
