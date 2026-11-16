import Langlands.Representation.Archimedean.RealBlockFunctional
import Langlands.Representation.Archimedean.RealTemperedIrreducibleStatement
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# Tied irreducibility from the tempered irreducibility statement

`RealTemperedStandardIrreducibleStatement` (irreducibility of real standard modules whose blocks
all have the same real exponent) implies `RealBlockFunctional.TiedIrreducible` (irreducibility of
the principal series of signed-power characters with signs `(−1)^{q_l}` and tied exponents): the
characters are those of a list of character blocks, whose standard module is the principal series.
-/

noncomputable section

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTiedIrreducible

open PartialJacquet GramFormula RealJacquetFrobenius RealStrictCharacterLanglandsQuotient
  Langlands.LocalFactor.Archimedean

/-- The principal series depends only on the characters at the positions `l < N`. -/
theorem principalSeries_congr {N : ℕ} {χ χ' : ℕ → ℝˣ → ℂ}
    (h : ∀ l : ℕ, l < N → ∀ x : ℝˣ, χ l x = χ' l x) :
    principalSeries ℝ N χ = principalSeries ℝ N χ' := by
  have hc : principalSeriesCharacter ℝ N χ = principalSeriesCharacter ℝ N χ' := by
    funext a
    unfold principalSeriesCharacter
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [h i i.isLt]
  ext f
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hc]

/-- Irreducibility of the `K`-finite `(𝔤, K)`-module of a space of functions only depends on the
space. -/
theorem isIrreducible_kFinite_of_eq {N : ℕ} {V V' : Submodule ℂ (Langlands.GeneralLinear N ℝ → ℂ)}
    (h : V = V')
    (hV : ∀ f ∈ V, ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ f)
    (hVK : ∀ k ∈ unitaryCompact ℝ N, ∀ f ∈ V,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k f ∈ V)
    (hVX : ∀ (X : Matrix (Fin N) (Fin N) ℝ), ∀ f ∈ V, rightDerivative (matrixModel ℝ N) X f ∈ V)
    (hV' : ∀ f ∈ V', ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ f)
    (hV'K : ∀ k ∈ unitaryCompact ℝ N, ∀ f ∈ V',
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) k f ∈ V')
    (hV'X : ∀ (X : Matrix (Fin N) (Fin N) ℝ), ∀ f ∈ V',
      rightDerivative (matrixModel ℝ N) X f ∈ V')
    (hirr : IsIrreducibleGKModule (kFiniteRep V hVK) (kFiniteLie V hV hVK hVX)) :
    IsIrreducibleGKModule (kFiniteRep V' hV'K) (kFiniteLie V' hV' hV'K hV'X) := by
  subst h
  exact hirr

/-- The parity `q mod 2` as an element of `Fin 2`. -/
def parity (q : ℕ) : Fin 2 := ⟨q % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The list of character blocks `sgn^{q_l} |·|^{f_l}`, `l < b`. -/
def charList (b : ℕ) (f : ℕ → ℂ) (q : ℕ → ℕ) : List RealBlock :=
  (List.ofFn fun i : Fin b => charData (parity (q i)) (f i)).map RealBlock.character

theorem isCharacterList_charList (b : ℕ) (f : ℕ → ℂ) (q : ℕ → ℕ) :
    IsCharacterList (charList b f q) := by
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨c, rfl⟩

theorem realRank_charList (b : ℕ) (f : ℕ → ℂ) (q : ℕ → ℕ) : realRank (charList b f q) = b := by
  rw [charList, realRank_map_character, List.length_ofFn]

theorem realPositionCharacter_charList {b : ℕ} (f : ℕ → ℂ) (q : ℕ → ℕ) {l : ℕ} (hl : l < b)
    (x : ℝˣ) :
    realPositionCharacter (charList b f q) l x = charFun (parity (q l)) (f l) x := by
  rw [charList, realPositionCharacter_map_character _ l (by simpa using hl)]
  simp only [List.getElem_ofFn]
  rfl

theorem charFun_eq {ψ : ℕ → ℝˣ → ℂ} {f : ℕ → ℂ} {q : ℕ → ℕ} (hψ : IsSignedPower ψ f)
    (hq : ∀ l : ℕ, ψ l (-1) = (-1) ^ q l) (l : ℕ) (x : ℝˣ) :
    charFun (parity (q l)) (f l) x = ψ l x := by
  rw [hψ.eq l x, charFun]
  congr 1
  have hpar : ((-1 : ℂ)) ^ (parity (q l)).val = (-1) ^ q l := by
    change (-1 : ℂ) ^ (q l % 2) = (-1) ^ q l
    conv_rhs => rw [← Nat.mod_add_div (q l) 2, pow_add, pow_mul]
    norm_num
  rcases lt_or_gt_of_ne x.ne_zero with hneg | hpos
  · have hs : signUnit x = -1 := by simp [signUnit, not_lt.mpr hneg.le]
    have hd : (x : ℝ) / |(x : ℝ)| = -1 := by rw [abs_of_neg hneg, div_neg, div_self x.ne_zero]
    rw [hs, hq, hd]
    push_cast
    exact hpar
  · have hs : signUnit x = 1 := by simp [signUnit, hpos]
    have hd : (x : ℝ) / |(x : ℝ)| = 1 := by rw [abs_of_pos hpos, div_self x.ne_zero]
    rw [hs, hψ.one, hd]
    simp

theorem realBlockExponent_charList {b : ℕ} (f : ℕ → ℂ) (q : ℕ → ℕ) :
    ∀ x ∈ charList b f q, ∃ i : Fin b, realBlockExponent x = (f i).re := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact ⟨i, rfl⟩

end RealTiedIrreducible

/-- **Statement.** `RealTemperedStandardIrreducibleStatement` implies
`RealBlockFunctional.TiedIrreducible`: for every `b`, every family `ψ` of characters with
`ψ_l(x) = ψ_l(sgn x) |x|^{f_l}`, `ψ_l(1) = 1`, `‖ψ_l(−1)‖ = 1` and `ψ_l(−1) = (−1)^{q_l}`, and
`Re f_l = Re f_0` for `l < b`, the `(𝔤𝔩_b(ℝ), O(b))`-module of `O(b)`-finite functions of the
principal series of `ψ` is irreducible. -/
def RealTiedIrreducibleStatement : Prop :=
  RealTemperedStandardIrreducibleStatement → RealBlockFunctional.TiedIrreducible

open RealTiedIrreducible RealStrictCharacterLanglandsQuotient in
theorem realTiedIrreducible : RealTiedIrreducibleStatement := by
  intro htemp b ψ f q hψ hq hre
  have hirr := htemp b (charList b f q) (realRank_charList b f q) (fun x hx y hy => by
    obtain ⟨i, hi⟩ := realBlockExponent_charList f q x hx
    obtain ⟨j, hj⟩ := realBlockExponent_charList f q y hy
    rw [hi, hj, hre i i.isLt, hre j j.isLt])
  have hV : realStandardModule b (charList b f q) = principalSeries ℝ b ψ :=
    (realStandardModule_eq (isCharacterList_charList b f q)).trans
      (principalSeries_congr fun l hl x => by
        rw [realPositionCharacter_charList f q hl, charFun_eq hψ hq])
  exact isIrreducible_kFinite_of_eq hV (fun _ hf => contMDiff_of_mem_realStandardModule hf)
    (fun k _ _ hf => rightTranslation_mem_realStandardModule_of_mem hf k)
    (fun X _ hf => rightDerivative_mem_realStandardModule_of_mem hf X) (fun _ hf => hf.1)
    (fun k _ _ hf => rightTranslation_mem_principalSeries ψ hf k)
    (fun X _ hf => rightDerivative_mem_principalSeries ψ hf X) hirr

end Langlands.Archimedean
