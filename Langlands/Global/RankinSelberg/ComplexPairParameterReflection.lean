import Langlands.Analysis.SeveralComplex.EntireSpectralReflection
import Langlands.Global.RankinSelberg.ComplexAdjacentNormalizedProducts
import Langlands.Global.RankinSelberg.ComplexCompactProfileFamily

/-! # Continuation of complex pair normalizations in the exponents -/

noncomputable section

open Metric Set
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.Analysis.SeveralComplex (HasEntireSpectralReflection entireSpectralReflection)
open ComplexCompactProfileFamily (characterList)

private theorem prod_map_flatMap {A B M : Type*} [Monoid M] (xs : List A) (f : A → List B)
    (g : B → M) : ((xs.flatMap f).map g).prod = (xs.map fun x => ((f x).map g).prod).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, ih]

private theorem pair_block_prod {n m : ℕ} {M : Type*} [CommMonoid M]
    (x : Fin n → ComplexCharacterData) (y : Fin m → ComplexCharacterData) (g : ComplexCharacterData → M) :
    ((complexPairBlocks (List.ofFn x) (List.ofFn y)).map g).prod =
      ∏ i, ∏ j, g ((x i).mul (y j)) := by
  simp only [complexPairBlocks, prod_map_flatMap, List.map_ofFn, Function.comp_apply, List.prod_ofFn]

variable {n m : ℕ}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

private theorem differentiable_finsetProd {I : Type*} (T : Finset I) (f : I → X → ℂ)
    (hf : ∀ i ∈ T, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun u => ∏ i ∈ T, f i u) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using differentiable_const (1 : ℂ)
  | insert i T hi ih =>
    simp only [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i T)).mul
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem differentiable_denominator_ofFn
    (x : X → Fin n → ComplexCharacterData) (y : X → Fin m → ComplexCharacterData)
    (l : Fin n → ℤ) (k : Fin m → ℤ)
    (hxw : ∀ u i, (x u i).weight = l i) (hyw : ∀ u j, (y u j).weight = k j)
    (hx : ∀ i, Differentiable ℂ (fun u => (x u i).exponent))
    (hy : ∀ j, Differentiable ℂ (fun u => (y u j).exponent))
    (s : X → ℂ) (hs : Differentiable ℂ s) :
    Differentiable ℂ (fun u => (complexPairLFactor (List.ofFn (x u)) (List.ofFn (y u))).denominator (s u)) := by
  simp only [complexPairLFactor, denominator_complexLFactor, pair_block_prod]
  apply differentiable_finsetProd
  intro i _
  apply differentiable_finsetProd
  intro j _
  have h (u : X) : ((x u i).mul (y u j)).lFactor.denominator (s u) =
      gammaComplex.denominator
        (s u + ((x u i).exponent + (y u j).exponent + ((l i + k j).natAbs : ℂ) / 2)) := by
    simp only [ComplexCharacterData.lFactor, complexTateL, ReciprocalEntire.denominator_shift,
      ComplexCharacterData.mul, hxw, hyw]
  simp only [h]
  exact gammaComplex.entire.comp (hs.add (((hx i).add (hy j)).add_const _))

theorem differentiable_pairDenominator (l : Fin n → ℤ) (k : Fin m → ℤ)
    (p : X → Fin n → ℂ) (q : X → Fin m → ℂ) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (s : X → ℂ) (hs : Differentiable ℂ s) :
    Differentiable ℂ (fun u => (complexPairLFactor (characterList l (p u))
      (characterList k (q u))).denominator (s u)) :=
  differentiable_denominator_ofFn (fun u i => characterOfParams (l i) (p u i))
    (fun u j => characterOfParams (k j) (q u j)) l k (fun _ _ => rfl) (fun _ _ => rfl)
    (differentiable_pi.mp hp) (differentiable_pi.mp hq) s hs

theorem differentiable_pairDualDenominator (l : Fin n → ℤ) (k : Fin m → ℤ)
    (p : X → Fin n → ℂ) (q : X → Fin m → ℂ) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (s : X → ℂ) (hs : Differentiable ℂ s) :
    Differentiable ℂ (fun u => (complexPairLFactor ((characterList l (p u)).map ComplexCharacterData.inv)
      ((characterList k (q u)).map ComplexCharacterData.inv)).denominator (s u)) := by
  simp only [characterList, List.map_ofFn]
  exact differentiable_denominator_ofFn (fun u i => (characterOfParams (l i) (p u i)).inv)
    (fun u j => (characterOfParams (k j) (q u j)).inv) (-l) (-k) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun i => (differentiable_pi.mp hp i).neg) (fun j => (differentiable_pi.mp hq j).neg) s hs

theorem differentiable_pairEpsilon (l : Fin n → ℤ) (k : Fin m → ℤ)
    (p : X → Fin n → ℂ) (q : X → Fin m → ℂ) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (a : ℂˣ) (s : X → ℂ) (hs : Differentiable ℂ s) :
    Differentiable ℂ (fun u => (complexPairEpsilon (characterList l (p u)) (characterList k (q u))
      a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) (s u) : ℂ)) := by
  let v (u : X) (i : Fin n) (j : Fin m) := (characterOfParams (l i) (p u i)).mul
    (characterOfParams (k j) (q u j))
  have h (u : X) : (complexPairEpsilon (characterList l (p u)) (characterList k (q u))
      a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) (s u) : ℂ) =
      ∏ i, ∏ j, ((v u i j).epsilon a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) (s u) : ℂ) := by
    unfold complexPairEpsilon complexEpsilon
    change Units.coeHom ℂ _ = _
    rw [map_list_prod, List.map_map]
    exact pair_block_prod _ _ _
  simp only [h]
  apply differentiable_finsetProd
  intro i _
  apply differentiable_finsetProd
  intro j _
  have ha : (‖(a : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr a.ne_zero
  have hchar (u : X) : ((v u i j).character a : ℂ) =
      ((a : ℂ) / (‖(a : ℂ)‖ : ℂ)) ^ (l i + k j) *
        (‖(a : ℂ)‖ : ℂ) ^ (2 * (p u i + q u j)) := (v u i j).character_eq a
  have hd : Differentiable ℂ (fun u => ((v u i j).character a : ℂ)) := by
    simp only [hchar]
    exact (((differentiable_pi.mp hp i).add (differentiable_pi.mp hq j)).const_mul 2).const_cpow
      (.inl ha) |>.const_mul _
  simp only [ComplexCharacterData.coe_epsilon]
  change Differentiable ℂ (fun u => (‖(a : ℂ)‖₊ : ℂ) * ((v u i j).character a : ℂ) *
    (‖(a : ℂ)‖ : ℂ) ^ (2 * (s u - 1)) * Complex.I ^ (l i + k j).natAbs)
  exact ((hd.const_mul _).mul (((hs.sub_const 1).const_mul 2).const_cpow (.inl ha))).mul_const _

theorem complexCentralSign_ne_zero (ds : List ComplexCharacterData) : complexCentralSign ds ≠ 0 := by
  intro h
  have hsq := ComplexJacquet.complexCentralSign_sq ds
  rw [h] at hsq
  simp at hsq

theorem complexCentralSign_characterList (l : Fin n → ℤ) (p : Fin n → ℂ) :
    complexCentralSign (characterList l p) = ∏ i, (-1 : ℂ) ^ l i := by
  simp only [complexCentralSign, characterList, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [(characterOfParams _ _).character_eq]
  simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one,
    div_one, characterOfParams_weight, Complex.one_cpow, mul_one]

/-- For fixed weights, entire pair normalizations propagate from a small parameter disk
along a holomorphic family of exponents. The input integrals are jointly holomorphic on
the parameter disk of radius three times a uniform spectral right half-plane. -/
def ComplexPairParameterReflectionStatement : Prop :=
  ∀ (n m : ℕ) (l : Fin n → ℤ) (k : Fin m → ℤ) (p : ℂ → Fin n → ℂ) (q : ℂ → Fin m → ℂ)
    (a : ℂˣ) (c : ℂ), c ≠ 0 → Differentiable ℂ p → Differentiable ℂ q →
    ∀ (Z Zd : ℂ × ℂ → ℂ) (σ : ℝ),
      DifferentiableOn ℂ Z (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
      DifferentiableOn ℂ Zd (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
        HasComplexPairNormalization (characterList l (p z)) (characterList k (q z)) a c
          (fun s => Z (z, s)) (fun s => Zd (z, s))) →
      HasComplexPairNormalization (characterList l (p 1)) (characterList k (q 1)) a c
        (fun s => Z (1, s)) (fun s => Zd (1, s))

theorem complexPairParameterReflection : ComplexPairParameterReflectionStatement := by
  intro n m l k p q a c hc hp hq Z Zd σ hZ hZd hInit
  let ds (z : ℂ) := characterList l (p z)
  let es (z : ℂ) := characterList k (q z)
  let F (u : ℂ × ℂ) := (complexPairLFactor (ds u.1) (es u.1)).denominator u.2 * Z u
  let G (u : ℂ × ℂ) :=
    (complexPairLFactor ((ds u.1).map ComplexCharacterData.inv)
      ((es u.1).map ComplexCharacterData.inv)).denominator u.2 * Zd u
  let E (u : ℂ × ℂ) :=
    c * (complexPairEpsilon (ds u.1) (es u.1) a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) u.2 : ℂ)
  have hp' := hp.comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have hq' := hq.comp (differentiable_fst (𝕜 := ℂ) (E := ℂ) (F := ℂ))
  have hF : DifferentiableOn ℂ F (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) :=
    (differentiable_pairDenominator l k _ _ hp' hq' _ differentiable_snd).differentiableOn.mul hZ
  have hG : DifferentiableOn ℂ G (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) :=
    (differentiable_pairDualDenominator l k _ _ hp' hq' _ differentiable_snd).differentiableOn.mul hZd
  have hE : Differentiable ℂ E :=
    (differentiable_pairEpsilon l k _ _ hp' hq' a _ differentiable_snd).const_mul c
  have hE₀ (u : ℂ × ℂ) : E u ≠ 0 := mul_ne_zero hc (Units.ne_zero _)
  change HasEntireSpectralReflection (fun s => F (1, s)) (fun s => G (1, s)) (fun s => E (1, s))
  exact entireSpectralReflection F G E σ hF hG hE hE₀ hInit

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
