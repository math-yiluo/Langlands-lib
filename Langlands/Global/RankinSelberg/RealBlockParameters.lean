import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Real block lists with fixed discrete data and varying exponents -/

noncomputable section

open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealBlockParameters

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent)
open Langlands.Archimedean.RealJacquetFrobenius (charData)

/-- The discrete datum of a real block: a parity for a character, a weight for a real
induction of a complex character. -/
abbrev Shape := Fin 2 ⊕ ℤ

/-- The real block with the given discrete datum and complex exponent. -/
def blockOfParams : Shape → ℂ → RealBlock
  | .inl e, t => .character (charData e t)
  | .inr l, t => .induced (characterOfParams l t)

/-- A real block list with fixed discrete data and varying exponents. -/
def blockList {n : ℕ} (sh : Fin n → Shape) (p : Fin n → ℂ) : List RealBlock :=
  List.ofFn fun i => blockOfParams (sh i) (p i)

/-- The discrete data of the blocks of a tensor product of two blocks. -/
def tensorShape : Shape → Shape → List Shape
  | .inl e, .inl e' => [.inl (e + e')]
  | .inl _, .inr l => [.inr l]
  | .inr l, .inl _ => [.inr l]
  | .inr l, .inr l' => [.inr (l + l'), .inr (l + -l')]

/-- The discrete datum of the dual block. -/
def dualShape : Shape → Shape
  | .inl e => .inl e
  | .inr l => .inr (-l)

theorem realCharacterData_ext {c d : RealCharacterData} (hp : c.parity = d.parity)
    (he : c.exponent = d.exponent) : c = d := by
  have hch : c.character = d.character := by
    ext x
    rw [c.character_eq, d.character_eq, hp, he]
  cases c
  cases d
  cases hch
  simp only at hp he
  subst hp he
  rfl

theorem complexCharacterData_ext {c d : ComplexCharacterData} (hw : c.weight = d.weight)
    (he : c.exponent = d.exponent) : c = d := by
  have hch : c.character = d.character := by
    ext z
    rw [c.character_eq, d.character_eq, hw, he]
  cases c
  cases d
  cases hch
  simp only at hw he
  subst hw he
  rfl

@[simp]
theorem charData_parity (e : Fin 2) (t : ℂ) : (charData e t).parity = e := rfl

@[simp]
theorem charData_exponent (e : Fin 2) (t : ℂ) : (charData e t).exponent = t := rfl

/-- Tensor products of parametrized blocks are parametrized blocks at the summed exponent. -/
theorem tensor_blockOfParams (a a' : Shape) (t t' : ℂ) :
    (blockOfParams a t).tensor (blockOfParams a' t') =
      (tensorShape a a').map fun b => blockOfParams b (t + t') := by
  cases a with
  | inl e =>
    cases a' with
    | inl e' =>
      simp only [blockOfParams, tensorShape, RealBlock.tensor, List.map_cons, List.map_nil,
        List.cons.injEq, RealBlock.character.injEq, and_true]
      exact realCharacterData_ext rfl rfl
    | inr l =>
      simp only [blockOfParams, tensorShape, RealBlock.tensor, List.map_cons, List.map_nil,
        List.cons.injEq, RealBlock.induced.injEq, and_true]
      exact complexCharacterData_ext rfl (add_comm _ _)
  | inr l =>
    cases a' with
    | inl e =>
      simp only [blockOfParams, tensorShape, RealBlock.tensor, List.map_cons, List.map_nil,
        List.cons.injEq, RealBlock.induced.injEq, and_true]
      exact complexCharacterData_ext rfl rfl
    | inr l' =>
      simp only [blockOfParams, tensorShape, RealBlock.tensor, List.map_cons, List.map_nil,
        List.cons.injEq, RealBlock.induced.injEq, and_true]
      exact ⟨complexCharacterData_ext rfl rfl, complexCharacterData_ext rfl rfl⟩

/-- The dual of a parametrized block is the parametrized block of the dual datum at the
negated exponent. -/
theorem dualBlock_blockOfParams (a : Shape) (t : ℂ) :
    RealLocalJacquet.dualBlock (blockOfParams a t) = blockOfParams (dualShape a) (-t) := by
  cases a with
  | inl e =>
    simp only [blockOfParams, dualShape, RealLocalJacquet.dualBlock, RealBlock.character.injEq]
    exact realCharacterData_ext rfl rfl
  | inr l =>
    simp only [blockOfParams, dualShape, RealLocalJacquet.dualBlock, RealBlock.induced.injEq]
    exact complexCharacterData_ext rfl rfl

theorem map_dualBlock_blockList {n : ℕ} (sh : Fin n → Shape) (p : Fin n → ℂ) :
    (blockList sh p).map RealLocalJacquet.dualBlock =
      blockList (fun i => dualShape (sh i)) (fun i => -p i) := by
  simp only [blockList, List.map_ofFn]
  congr 1
  funext i
  exact dualBlock_blockOfParams (sh i) (p i)

/-- The reciprocal `L`-factor of a parametrized block is a translate of the one at exponent
zero. -/
theorem lFactor_blockOfParams (a : Shape) (t s : ℂ) :
    (blockOfParams a t).lFactor.denominator s =
      (blockOfParams a 0).lFactor.denominator (s + t) := by
  cases a with
  | inl e =>
    simp only [blockOfParams, RealBlock.lFactor_character, ReciprocalEntire.denominator_shift,
      charData_exponent, charData_parity, zero_add]
    ring_nf
  | inr l =>
    simp only [blockOfParams, RealBlock.lFactor_induced, ReciprocalEntire.denominator_shift,
      characterOfParams_exponent, characterOfParams_weight, zero_add]
    ring_nf

/-- The epsilon factor of a parametrized block is a translate of the one at exponent zero. -/
theorem epsilon_blockOfParams (a : Shape) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (t s : ℂ) :
    ((blockOfParams a t).epsilon b c hc s : ℂ) =
      ((blockOfParams a 0).epsilon b c hc (s + t) : ℂ) := by
  have hb : ((|(b : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr b.ne_zero
  cases a with
  | inl e =>
    change ((charData e t).epsilon b c hc s : ℂ) = ((charData e 0).epsilon b c hc (s + t) : ℂ)
    rw [RealCharacterData.coe_epsilon, RealCharacterData.coe_epsilon,
      (charData e t).character_eq, (charData e 0).character_eq]
    simp only [charData_parity, charData_exponent, Complex.cpow_zero, mul_one]
    rw [show s + t - 1 = t + (s - 1) by ring, Complex.cpow_add _ _ hb]
    ring
  | inr l =>
    change ((characterOfParams l t).realInducedEpsilon b c hc s : ℂ) =
      ((characterOfParams l 0).realInducedEpsilon b c hc (s + t) : ℂ)
    have hn : ((‖((realToComplex b : ℂˣ) : ℂ)‖ : ℝ) : ℂ) = ((|(b : ℝ)| : ℝ) : ℂ) := by
      simp [realToComplex, Complex.norm_real]
    rw [ComplexCharacterData.coe_realInducedEpsilon, ComplexCharacterData.coe_realInducedEpsilon,
      (characterOfParams l t).character_eq, (characterOfParams l 0).character_eq, hn]
    simp only [characterOfParams_weight, characterOfParams_exponent, mul_zero, Complex.cpow_zero,
      mul_one]
    rw [show 2 * (s + t - 1) = 2 * t + 2 * (s - 1) by ring, Complex.cpow_add _ _ hb]
    ring

private theorem prod_map_flatMap {A B M : Type*} [Monoid M] (xs : List A) (f : A → List B)
    (g : B → M) : ((xs.flatMap f).map g).prod = (xs.map fun x => ((f x).map g).prod).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, ih]

/-- The pair reciprocal `L`-factor of two parametrized lists, as a finite product of
translates of the block factors at exponent zero. -/
theorem pairDenominator_blockList {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape)
    (p : Fin n → ℂ) (q : Fin m → ℂ) (s : ℂ) :
    (realPairLFactor (blockList sh p) (blockList sh' q)).denominator s =
      ∏ i, ∏ j, ((tensorShape (sh i) (sh' j)).map fun b =>
        (blockOfParams b 0).lFactor.denominator (s + (p i + q j))).prod := by
  rw [realPairLFactor, denominator_realLFactor, realPairBlocks, prod_map_flatMap]
  simp only [blockList, List.map_ofFn, List.prod_ofFn, Function.comp_apply, prod_map_flatMap,
    tensor_blockOfParams, List.map_map]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  refine List.map_congr_left fun b _ => ?_
  exact lFactor_blockOfParams b _ s

/-- The pair epsilon factor of two parametrized lists, as a finite product of translates of
the block epsilon factors at exponent zero. -/
theorem pairEpsilon_blockList {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape)
    (p : Fin n → ℂ) (q : Fin m → ℂ) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (s : ℂ) :
    (realPairEpsilon (blockList sh p) (blockList sh' q) b c hc s : ℂ) =
      ∏ i, ∏ j, ((tensorShape (sh i) (sh' j)).map fun x =>
        ((blockOfParams x 0).epsilon b c hc (s + (p i + q j)) : ℂ)).prod := by
  have h : (realPairEpsilon (blockList sh p) (blockList sh' q) b c hc s : ℂ) =
      ((realPairBlocks (blockList sh p) (blockList sh' q)).map fun x =>
        (x.epsilon b c hc s : ℂ)).prod := by
    unfold realPairEpsilon realEpsilon
    change Units.coeHom ℂ _ = _
    rw [map_list_prod, List.map_map]
    rfl
  rw [h, realPairBlocks, prod_map_flatMap]
  simp only [blockList, List.map_ofFn, List.prod_ofFn, Function.comp_apply, prod_map_flatMap,
    tensor_blockOfParams, List.map_map]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact epsilon_blockOfParams x b c hc _ s

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

private theorem differentiable_listProd {I : Type*} (l : List I) (f : I → X → ℂ)
    (hf : ∀ i ∈ l, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun u => (l.map fun i => f i u).prod) := by
  induction l with
  | nil => simpa only [List.map_nil, List.prod_nil] using differentiable_const (1 : ℂ)
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf i List.mem_cons_self).mul (ih fun j hj => hf j (List.mem_cons_of_mem i hj))

/-- The pair reciprocal `L`-factor is jointly holomorphic in holomorphic exponents and a
holomorphic spectral variable. -/
theorem differentiable_pairDenominator {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape)
    (p : X → Fin n → ℂ) (q : X → Fin m → ℂ) (hp : Differentiable ℂ p)
    (hq : Differentiable ℂ q) (s : X → ℂ) (hs : Differentiable ℂ s) :
    Differentiable ℂ (fun u =>
      (realPairLFactor (blockList sh (p u)) (blockList sh' (q u))).denominator (s u)) := by
  simp only [pairDenominator_blockList]
  refine differentiable_finsetProd _ _ fun i _ => differentiable_finsetProd _ _ fun j _ => ?_
  refine differentiable_listProd _ _ fun b _ => ?_
  exact (blockOfParams b 0).lFactor.entire.comp
    (hs.add ((differentiable_pi.mp hp i).add (differentiable_pi.mp hq j)))

/-- The pair epsilon factor is jointly holomorphic in holomorphic exponents and a holomorphic
spectral variable. -/
theorem differentiable_pairEpsilon {n m : ℕ} (sh : Fin n → Shape) (sh' : Fin m → Shape)
    (p : X → Fin n → ℂ) (q : X → Fin m → ℂ) (hp : Differentiable ℂ p)
    (hq : Differentiable ℂ q) (b : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (s : X → ℂ)
    (hs : Differentiable ℂ s) :
    Differentiable ℂ (fun u =>
      (realPairEpsilon (blockList sh (p u)) (blockList sh' (q u)) b c hc (s u) : ℂ)) := by
  simp only [pairEpsilon_blockList]
  refine differentiable_finsetProd _ _ fun i _ => differentiable_finsetProd _ _ fun j _ => ?_
  refine differentiable_listProd _ _ fun x _ => ?_
  exact ((blockOfParams x 0).differentiable_epsilon b c hc).comp
    (hs.add ((differentiable_pi.mp hp i).add (differentiable_pi.mp hq j)))

end Langlands.Global.RankinSelbergGlobal.RealBlockParameters
