import Langlands.LocalFactor.ArchimedeanScaling
import Langlands.Weil.Representation.SumsTensor
import Langlands.Weil.Representation.OperationClosureProof

/-!
# Arithmetic factors of finite archimedean Weil presentations

Finite lists of the published character and real-induction blocks, their actual
continuous sum models, and the L- and epsilon-factor products of the blocks.
A supplied continuous representation receives factors only through supplied
presentation data with an actual invertible linear intertwiner. No presentation
is chosen, and no independence of the presentation is asserted.
-/

noncomputable section

universe uG uV uW

namespace Langlands.LocalFactor.Archimedean

open Langlands.Weil.Archimedean

section Model

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The zero-dimensional representation on `Fin 0 → ℂ`: the empty sum. -/
def zeroRepresentation (G : Type uG) [Group G] [TopologicalSpace G] :
    FiniteRepresentation.ContinuousObjects.{uG, 0} G :=
  ⟨FiniteRepresentation.of (Representation.trivial ℂ G (Fin 0 → ℂ)), by
    let _ : TopologicalSpace (Module.End ℂ (Fin 0 → ℂ)) := moduleTopology ℂ _
    change Continuous (Representation.trivial ℂ G (Fin 0 → ℂ))
    exact continuous_const⟩

@[simp]
theorem zeroRepresentation_rank : (zeroRepresentation G).val.rank = 0 := by
  simp only [zeroRepresentation, FiniteRepresentation.rank]
  exact Module.finrank_fin_fun ℂ

/-- The published binary direct sum of two continuous representations, with
continuity of the product action. -/
def continuousSum (A : FiniteRepresentation.ContinuousObjects.{uG, uV} G)
    (B : FiniteRepresentation.ContinuousObjects.{uG, uW} G) :
    FiniteRepresentation.ContinuousObjects.{uG, max uV uW} G :=
  ⟨FiniteRepresentation.sum A.val B.val,
    Weil.OperationClosure.continuous_prod A.val.representation B.val.representation
      A.property B.property⟩

@[simp]
theorem continuousSum_val (A : FiniteRepresentation.ContinuousObjects.{uG, uV} G)
    (B : FiniteRepresentation.ContinuousObjects.{uG, uW} G) :
    (continuousSum A B).val = FiniteRepresentation.sum A.val B.val := rfl

@[simp]
theorem continuousSum_rank (A : FiniteRepresentation.ContinuousObjects.{uG, uV} G)
    (B : FiniteRepresentation.ContinuousObjects.{uG, uW} G) :
    (continuousSum A B).val.rank = A.val.rank + B.val.rank := by
  simp only [continuousSum_val, FiniteRepresentation.sum, FiniteRepresentation.rank]
  exact Module.finrank_prod

end Model

/-! ## Complex presentations -/

/-- The shifted complex Gamma block of a complex character datum. -/
def ComplexCharacterData.gammaBlock (d : ComplexCharacterData) : GammaBlock :=
  .complex (d.exponent + (d.weight.natAbs : ℂ) / 2)

theorem ComplexCharacterData.gammaBlock_factor (d : ComplexCharacterData) :
    d.gammaBlock.factor = d.lFactor := rfl

/-- The actual sum model of a finite list of complex character blocks. -/
def complexModel :
    List ComplexCharacterData → FiniteRepresentation.ContinuousObjects.{0, 0} ComplexWeil
  | [] => zeroRepresentation ComplexWeil
  | d :: ds => continuousSum d.representation (complexModel ds)

@[simp]
theorem complexModel_nil : complexModel [] = zeroRepresentation ComplexWeil := rfl

theorem complexModel_cons (d : ComplexCharacterData) (ds : List ComplexCharacterData) :
    complexModel (d :: ds) = continuousSum d.representation (complexModel ds) := rfl

/-- The model is the published binary sum folded from the zero representation. -/
theorem complexModel_val (ds : List ComplexCharacterData) :
    (complexModel ds).val =
      ds.foldr (fun d A => FiniteRepresentation.sum (complexCharacter d.character).val A)
        (FiniteRepresentation.of (Representation.trivial ℂ ComplexWeil (Fin 0 → ℂ))) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.foldr_cons, ← ih]
    rfl

/-- Each complex character block has rank one. -/
@[simp]
theorem complexModel_rank (ds : List ComplexCharacterData) :
    (complexModel ds).val.rank = ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [complexModel_cons, continuousSum_rank, ih, d.representation_rank, List.length_cons,
      add_comm]

/-- The L-factor of a complex presentation: the product of the block factors. -/
def complexLFactor (ds : List ComplexCharacterData) : ReciprocalEntire :=
  ReciprocalEntire.product (ds.map ComplexCharacterData.lFactor)

/-- Standard trace-character epsilon of a complex presentation. -/
def complexStandardEpsilon (ds : List ComplexCharacterData) : ℂˣ :=
  (ds.map ComplexCharacterData.standardEpsilon).prod

/-- Epsilon of a complex presentation twisted by `‖.‖^(2*s)`, for
`complexScaledCharacter a` and `complexScaledMeasure c hc`. -/
def complexEpsilon (ds : List ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) : ℂˣ :=
  (ds.map fun d => d.epsilon a c hc s).prod

section ComplexLaws

variable (ds es : List ComplexCharacterData) (d : ComplexCharacterData)

@[simp]
theorem complexLFactor_nil : complexLFactor [] = ReciprocalEntire.one := rfl

theorem complexLFactor_cons : complexLFactor (d :: ds) = d.lFactor.mul (complexLFactor ds) :=
  rfl

@[simp]
theorem complexLFactor_singleton : complexLFactor [d] = d.lFactor := by
  apply ReciprocalEntire.ext
  funext z
  simp [complexLFactor, ReciprocalEntire.product, ReciprocalEntire.one]

theorem denominator_complexLFactor (z : ℂ) :
    (complexLFactor ds).denominator z = (ds.map fun d => d.lFactor.denominator z).prod := by
  rw [complexLFactor, ReciprocalEntire.denominator_product, List.map_map]
  rfl

theorem complexLFactor_append :
    complexLFactor (ds ++ es) = (complexLFactor ds).mul (complexLFactor es) := by
  apply ReciprocalEntire.ext
  funext z
  simp [denominator_complexLFactor, List.prod_append]

theorem complexLFactor_perm {ds es : List ComplexCharacterData} (h : ds.Perm es) :
    complexLFactor ds = complexLFactor es :=
  ReciprocalEntire.product_perm (h.map _)

/-- The factor is the published finite Gamma product of the shifted blocks. -/
theorem complexLFactor_eq_gammaProduct :
    complexLFactor ds = gammaProduct (ds.map ComplexCharacterData.gammaBlock) := by
  rw [gammaProduct, List.map_map]
  rfl

/-- The factor in the raw Gamma-shift form of
`ComplexFactorPresentationIndependenceStatement`. -/
theorem complexLFactor_eq_shiftProduct :
    complexLFactor ds = ReciprocalEntire.product (ds.map fun d =>
      gammaComplex.shift (d.exponent + (d.weight.natAbs : ℂ) / 2)) :=
  rfl

theorem complexLFactor_isPole (s : ℂ) :
    (complexLFactor ds).IsPole s ↔
      ∃ d ∈ ds, ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ) := by
  rw [complexLFactor, ReciprocalEntire.isPole_product]
  constructor
  · rintro ⟨F, hF, hp⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hF
    exact ⟨d, hd, (d.lFactor_isPole s).mp hp⟩
  · rintro ⟨d, hd, hp⟩
    exact ⟨d.lFactor, List.mem_map_of_mem hd, (d.lFactor_isPole s).mpr hp⟩

/-- The regular domain is the complement of the union of the block pole sets. -/
theorem complexLFactor_regular_iff (s : ℂ) :
    (complexLFactor ds).denominator s ≠ 0 ↔
      ∀ d ∈ ds, ∀ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) ≠ -(n : ℂ) := by
  have h := (complexLFactor_isPole ds s).not
  simp only [not_exists, not_and] at h
  exact h

variable {ds} in
/-- A regular point of the presentation factor is regular for each block. -/
def complexBlockRegularPoint (s : (complexLFactor ds).RegularPoint) {d : ComplexCharacterData}
    (hd : d ∈ ds) : d.lFactor.RegularPoint :=
  ⟨s.val, fun h => s.property
    ((ReciprocalEntire.isPole_product _ _).mpr ⟨d.lFactor, List.mem_map_of_mem hd, h⟩)⟩

/-- Evaluation at a regular point is the product of the block evaluations. -/
theorem coe_eval_complexLFactor (s : (complexLFactor ds).RegularPoint) :
    ((complexLFactor ds).eval s : ℂ) =
      (ds.attach.map fun d => (d.val.lFactor.eval
        (complexBlockRegularPoint s d.property) : ℂ)).prod := by
  have h : (ds.attach.map fun d => (d.val.lFactor.eval
      (complexBlockRegularPoint s d.property) : ℂ)) =
      ds.map fun d => (d.lFactor.denominator s.val)⁻¹ :=
    List.attach_map_val (f := fun d : ComplexCharacterData => (d.lFactor.denominator s.val)⁻¹)
  rw [h, ReciprocalEntire.coe_eval, denominator_complexLFactor, List.prod_inv, List.map_map]
  rfl

@[simp]
theorem complexStandardEpsilon_nil : complexStandardEpsilon [] = 1 := rfl

@[simp]
theorem complexStandardEpsilon_cons :
    complexStandardEpsilon (d :: ds) = d.standardEpsilon * complexStandardEpsilon ds := rfl

theorem coe_complexStandardEpsilon :
    (complexStandardEpsilon ds : ℂ) = (ds.map fun d => Complex.I ^ d.weight.natAbs).prod := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [ih]

variable (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ)

@[simp]
theorem complexEpsilon_nil : complexEpsilon [] a c hc s = 1 := rfl

@[simp]
theorem complexEpsilon_cons :
    complexEpsilon (d :: ds) a c hc s = d.epsilon a c hc s * complexEpsilon ds a c hc s := rfl

@[simp]
theorem complexEpsilon_singleton : complexEpsilon [d] a c hc s = d.epsilon a c hc s := by
  simp [complexEpsilon]

theorem complexEpsilon_append :
    complexEpsilon (ds ++ es) a c hc s = complexEpsilon ds a c hc s * complexEpsilon es a c hc s := by
  simp [complexEpsilon, List.prod_append]

theorem complexEpsilon_perm {ds es : List ComplexCharacterData} (h : ds.Perm es) :
    complexEpsilon ds a c hc s = complexEpsilon es a c hc s :=
  (h.map _).prod_eq

/-- Closed formula: rank-`n` Haar scale, determinant, absolute value and standard phase. -/
theorem coe_complexEpsilon :
    (complexEpsilon ds a c hc s : ℂ) =
      (c : ℂ) ^ ds.length * (ds.map fun d => (d.character a : ℂ)).prod *
        (‖(a : ℂ)‖ : ℂ) ^ (2 * (ds.length : ℂ) * (s - 1)) *
        (ds.map fun d => Complex.I ^ d.weight.natAbs).prod := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have ha : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr a.ne_zero
    have hexp : 2 * ((d :: ds).length : ℂ) * (s - 1) =
        2 * (s - 1) + 2 * (ds.length : ℂ) * (s - 1) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    rw [complexEpsilon_cons, Units.val_mul, ih, ComplexCharacterData.coe_epsilon, hexp,
      Complex.cpow_add _ _ ha]
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    ring

theorem complexEpsilon_ne_zero : (complexEpsilon ds a c hc s : ℂ) ≠ 0 :=
  (complexEpsilon ds a c hc s).ne_zero

theorem differentiable_complexEpsilon :
    Differentiable ℂ (fun s => (complexEpsilon ds a c hc s : ℂ)) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [complexEpsilon_cons, Units.val_mul]
    exact (d.differentiable_epsilon a c hc).mul ih

@[simp]
theorem complexEpsilon_standard : complexEpsilon ds 1 1 zero_lt_one s = complexStandardEpsilon ds := by
  simp [complexEpsilon, complexStandardEpsilon]

/-- Positive Haar scaling multiplies by the scale to the actual model rank. -/
theorem complexEpsilon_measure_scale (b : NNReal) (hb : 0 < b) :
    (complexEpsilon ds a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) ^ (complexModel ds).val.rank * (complexEpsilon ds a c hc s : ℂ) := by
  rw [complexModel_rank, coe_complexEpsilon, coe_complexEpsilon, NNReal.coe_mul,
    Complex.ofReal_mul, mul_pow]
  ring

end ComplexLaws

/-! ## Real presentations -/

/-- A block of a real presentation: a real character, or the actual real
induction of a complex character (weight zero allowed, not asserted irreducible). -/
inductive RealBlock where
  | character (d : RealCharacterData)
  | induced (d : ComplexCharacterData)

namespace RealBlock

/-- Real blocks are the disjoint union of real and complex character data. -/
def equivSum : RealBlock ≃ RealCharacterData ⊕ ComplexCharacterData where
  toFun
    | character d => .inl d
    | induced d => .inr d
  invFun
    | .inl d => character d
    | .inr d => induced d
  left_inv x := by cases x <;> rfl
  right_inv y := by cases y <;> rfl

/-- The actual continuous representation of the block. -/
def representation : RealBlock → FiniteRepresentation.ContinuousObjects.{0, 0} RealWeil
  | character d => d.representation
  | induced d => d.realInducedRepresentation

/-- Block rank: one for a character, two for a real induction. -/
def rank : RealBlock → ℕ
  | character _ => 1
  | induced _ => 2

theorem representation_character (d : RealCharacterData) :
    (character d).representation = realCharacter d.character := rfl

theorem representation_induced (d : ComplexCharacterData) :
    (induced d).representation = realInducedCharacter d.character := rfl

@[simp]
theorem representation_rank (x : RealBlock) : x.representation.val.rank = x.rank := by
  cases x <;> simp [representation, rank]

/-- The block L-factor. -/
def lFactor : RealBlock → ReciprocalEntire
  | character d => d.lFactor
  | induced d => d.realInducedLFactor

/-- The shifted Gamma block. -/
def gammaBlock : RealBlock → GammaBlock
  | character d => .real (d.exponent + (d.parity.val : ℂ))
  | induced d => .complex (d.exponent + (d.weight.natAbs : ℂ) / 2)

theorem gammaBlock_factor (x : RealBlock) : x.gammaBlock.factor = x.lFactor := by
  cases x <;> rfl

theorem lFactor_character (d : RealCharacterData) :
    (character d).lFactor = gammaReal.shift (d.exponent + (d.parity.val : ℂ)) := rfl

theorem lFactor_induced (d : ComplexCharacterData) :
    (induced d).lFactor = gammaComplex.shift (d.exponent + (d.weight.natAbs : ℂ) / 2) := rfl

/-- Standard plus-character epsilon, including the induction phase `i`. -/
def standardEpsilon : RealBlock → ℂˣ
  | character d => d.standardEpsilon
  | induced d => d.realInducedStandardEpsilon

/-- Determinant multiplier at a real unit: the character value, or sign times
the restricted inducing character. -/
def determinant : RealBlock → ℝˣ → ℂˣ
  | character d, a => d.character a
  | induced d, a => d.realInducedDeterminant a

/-- Block epsilon for `realScaledCharacter a` and `realScaledMeasure c hc`. -/
def epsilon : RealBlock → ℝˣ → (c : NNReal) → 0 < c → ℂ → ℂˣ
  | character d, a, c, hc, s => d.epsilon a c hc s
  | induced d, a, c, hc, s => d.realInducedEpsilon a c hc s

variable (x : RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ)

theorem lFactor_isPole_character (d : RealCharacterData) :
    (character d).lFactor.IsPole s ↔
      ∃ n : ℕ, s + (d.exponent + (d.parity.val : ℂ)) = -(2 * (n : ℂ)) :=
  d.lFactor_isPole s

theorem lFactor_isPole_induced (d : ComplexCharacterData) :
    (induced d).lFactor.IsPole s ↔
      ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ) :=
  d.realInducedLFactor_isPole s

theorem coe_standardEpsilon_character (d : RealCharacterData) :
    ((character d).standardEpsilon : ℂ) = Complex.I ^ d.parity.val := rfl

theorem coe_standardEpsilon_induced (d : ComplexCharacterData) :
    ((induced d).standardEpsilon : ℂ) = Complex.I ^ (d.weight.natAbs + 1) := rfl

theorem coe_determinant_character (d : RealCharacterData) :
    ((character d).determinant a : ℂ) = (d.character a : ℂ) := rfl

theorem coe_determinant_induced (d : ComplexCharacterData) :
    ((induced d).determinant a : ℂ) =
      (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) * (d.character (realToComplex a) : ℂ) := rfl

/-- Block closed formula with the rank as Haar and absolute-value exponent. -/
theorem coe_epsilon :
    (x.epsilon a c hc s : ℂ) = (c : ℂ) ^ x.rank * (x.determinant a : ℂ) *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ ((x.rank : ℂ) * (s - 1)) * (x.standardEpsilon : ℂ) := by
  cases x with
  | character d => simp [epsilon, rank, determinant, standardEpsilon]
  | induced d => simp [epsilon, rank, determinant, standardEpsilon]

theorem differentiable_epsilon :
    Differentiable ℂ (fun s => (x.epsilon a c hc s : ℂ)) := by
  cases x with
  | character d => exact d.differentiable_epsilon a c hc
  | induced d => exact d.differentiable_realInducedEpsilon a c hc

@[simp]
theorem epsilon_standard : x.epsilon 1 1 zero_lt_one s = x.standardEpsilon := by
  cases x with
  | character d => exact d.epsilon_standard s
  | induced d => exact d.realInducedEpsilon_standard s

theorem epsilon_measure_scale (b : NNReal) (hb : 0 < b) :
    (x.epsilon a (b * c) (mul_pos hb hc) s : ℂ) = (b : ℂ) ^ x.rank * (x.epsilon a c hc s : ℂ) := by
  cases x with
  | character d => simpa [epsilon, rank] using d.epsilon_measure_scale a c b hc hb s
  | induced d => exact d.realInducedEpsilon_measure_scale a c b hc hb s

end RealBlock

/-- The actual sum model of a finite list of real blocks. -/
def realModel : List RealBlock → FiniteRepresentation.ContinuousObjects.{0, 0} RealWeil
  | [] => zeroRepresentation RealWeil
  | x :: xs => continuousSum x.representation (realModel xs)

/-- Total rank of a real presentation: the sum of the block ranks. -/
def realRank (xs : List RealBlock) : ℕ := (xs.map RealBlock.rank).sum

@[simp]
theorem realModel_nil : realModel [] = zeroRepresentation RealWeil := rfl

theorem realModel_cons (x : RealBlock) (xs : List RealBlock) :
    realModel (x :: xs) = continuousSum x.representation (realModel xs) := rfl

/-- The model is the published binary sum folded from the zero representation. -/
theorem realModel_val (xs : List RealBlock) :
    (realModel xs).val =
      xs.foldr (fun x A => FiniteRepresentation.sum x.representation.val A)
        (FiniteRepresentation.of (Representation.trivial ℂ RealWeil (Fin 0 → ℂ))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldr_cons, ← ih]
    rfl

@[simp]
theorem realRank_nil : realRank [] = 0 := rfl

@[simp]
theorem realRank_cons (x : RealBlock) (xs : List RealBlock) :
    realRank (x :: xs) = x.rank + realRank xs := by
  simp [realRank]

@[simp]
theorem realModel_rank (xs : List RealBlock) : (realModel xs).val.rank = realRank xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [realModel_cons, continuousSum_rank, ih, x.representation_rank, realRank_cons]

/-- The L-factor of a real presentation: the product of the block factors. -/
def realLFactor (xs : List RealBlock) : ReciprocalEntire :=
  ReciprocalEntire.product (xs.map RealBlock.lFactor)

/-- Standard plus-character epsilon of a real presentation. -/
def realStandardEpsilon (xs : List RealBlock) : ℂˣ :=
  (xs.map RealBlock.standardEpsilon).prod

/-- Epsilon of a real presentation twisted by `|.|^s`, for
`realScaledCharacter a` and `realScaledMeasure c hc`. -/
def realEpsilon (xs : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) : ℂˣ :=
  (xs.map fun x => x.epsilon a c hc s).prod

section RealLaws

variable (xs ys : List RealBlock) (x : RealBlock)

@[simp]
theorem realLFactor_nil : realLFactor [] = ReciprocalEntire.one := rfl

theorem realLFactor_cons : realLFactor (x :: xs) = x.lFactor.mul (realLFactor xs) := rfl

@[simp]
theorem realLFactor_singleton : realLFactor [x] = x.lFactor := by
  apply ReciprocalEntire.ext
  funext z
  simp [realLFactor, ReciprocalEntire.product, ReciprocalEntire.one]

theorem denominator_realLFactor (z : ℂ) :
    (realLFactor xs).denominator z = (xs.map fun x => x.lFactor.denominator z).prod := by
  rw [realLFactor, ReciprocalEntire.denominator_product, List.map_map]
  rfl

theorem realLFactor_append :
    realLFactor (xs ++ ys) = (realLFactor xs).mul (realLFactor ys) := by
  apply ReciprocalEntire.ext
  funext z
  simp [denominator_realLFactor, List.prod_append]

theorem realLFactor_perm {xs ys : List RealBlock} (h : xs.Perm ys) :
    realLFactor xs = realLFactor ys :=
  ReciprocalEntire.product_perm (h.map _)

/-- The factor is the published finite Gamma product of the shifted blocks. -/
theorem realLFactor_eq_gammaProduct :
    realLFactor xs = gammaProduct (xs.map RealBlock.gammaBlock) := by
  rw [gammaProduct, List.map_map, realLFactor]
  congr 1
  apply List.map_congr_left
  intro x _
  exact (RealBlock.gammaBlock_factor x).symm

theorem realLFactor_isPole (s : ℂ) :
    (realLFactor xs).IsPole s ↔
      (∃ d : RealCharacterData, RealBlock.character d ∈ xs ∧
        ∃ n : ℕ, s + (d.exponent + (d.parity.val : ℂ)) = -(2 * (n : ℂ))) ∨
      (∃ d : ComplexCharacterData, RealBlock.induced d ∈ xs ∧
        ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ)) := by
  rw [realLFactor, ReciprocalEntire.isPole_product]
  constructor
  · rintro ⟨F, hF, hp⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hF
    cases x with
    | character d => exact .inl ⟨d, hx, (RealBlock.lFactor_isPole_character s d).mp hp⟩
    | induced d => exact .inr ⟨d, hx, (RealBlock.lFactor_isPole_induced s d).mp hp⟩
  · rintro (⟨d, hd, hp⟩ | ⟨d, hd, hp⟩)
    · exact ⟨_, List.mem_map_of_mem hd, (RealBlock.lFactor_isPole_character s d).mpr hp⟩
    · exact ⟨_, List.mem_map_of_mem hd, (RealBlock.lFactor_isPole_induced s d).mpr hp⟩

/-- The regular domain is the complement of the union of the block pole sets. -/
theorem realLFactor_regular_iff (s : ℂ) :
    (realLFactor xs).denominator s ≠ 0 ↔
      (∀ d : RealCharacterData, RealBlock.character d ∈ xs →
        ∀ n : ℕ, s + (d.exponent + (d.parity.val : ℂ)) ≠ -(2 * (n : ℂ))) ∧
      (∀ d : ComplexCharacterData, RealBlock.induced d ∈ xs →
        ∀ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) ≠ -(n : ℂ)) := by
  have h := (realLFactor_isPole xs s).not
  simp only [not_or, not_exists, not_and] at h
  exact h

variable {xs} in
/-- A regular point of the presentation factor is regular for each block. -/
def realBlockRegularPoint (s : (realLFactor xs).RegularPoint) {x : RealBlock}
    (hx : x ∈ xs) : x.lFactor.RegularPoint :=
  ⟨s.val, fun h => s.property
    ((ReciprocalEntire.isPole_product _ _).mpr ⟨x.lFactor, List.mem_map_of_mem hx, h⟩)⟩

/-- Evaluation at a regular point is the product of the block evaluations. -/
theorem coe_eval_realLFactor (s : (realLFactor xs).RegularPoint) :
    ((realLFactor xs).eval s : ℂ) =
      (xs.attach.map fun x => (x.val.lFactor.eval
        (realBlockRegularPoint s x.property) : ℂ)).prod := by
  have h : (xs.attach.map fun x => (x.val.lFactor.eval
      (realBlockRegularPoint s x.property) : ℂ)) =
      xs.map fun x => (x.lFactor.denominator s.val)⁻¹ :=
    List.attach_map_val (f := fun x : RealBlock => (x.lFactor.denominator s.val)⁻¹)
  rw [h, ReciprocalEntire.coe_eval, denominator_realLFactor, List.prod_inv, List.map_map]
  rfl

@[simp]
theorem realStandardEpsilon_nil : realStandardEpsilon [] = 1 := rfl

@[simp]
theorem realStandardEpsilon_cons :
    realStandardEpsilon (x :: xs) = x.standardEpsilon * realStandardEpsilon xs := rfl

variable (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ)

@[simp]
theorem realEpsilon_nil : realEpsilon [] a c hc s = 1 := rfl

@[simp]
theorem realEpsilon_cons :
    realEpsilon (x :: xs) a c hc s = x.epsilon a c hc s * realEpsilon xs a c hc s := rfl

@[simp]
theorem realEpsilon_singleton : realEpsilon [x] a c hc s = x.epsilon a c hc s := by
  simp [realEpsilon]

theorem realEpsilon_append :
    realEpsilon (xs ++ ys) a c hc s = realEpsilon xs a c hc s * realEpsilon ys a c hc s := by
  simp [realEpsilon, List.prod_append]

theorem realEpsilon_perm {xs ys : List RealBlock} (h : xs.Perm ys) :
    realEpsilon xs a c hc s = realEpsilon ys a c hc s :=
  (h.map _).prod_eq

/-- Closed formula: rank-`n` Haar scale, block determinants, absolute value and
standard phases, where `n` is the sum of the block ranks. -/
theorem coe_realEpsilon :
    (realEpsilon xs a c hc s : ℂ) =
      (c : ℂ) ^ realRank xs * (xs.map fun x => (x.determinant a : ℂ)).prod *
        ((|(a : ℝ)| : ℝ) : ℂ) ^ ((realRank xs : ℂ) * (s - 1)) *
        (xs.map fun x => (x.standardEpsilon : ℂ)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ha : ((|(a : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr a.ne_zero
    rw [realEpsilon_cons, Units.val_mul, ih, RealBlock.coe_epsilon, realRank_cons,
      Nat.cast_add, add_mul, Complex.cpow_add _ _ ha, pow_add]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem realEpsilon_ne_zero : (realEpsilon xs a c hc s : ℂ) ≠ 0 :=
  (realEpsilon xs a c hc s).ne_zero

theorem differentiable_realEpsilon :
    Differentiable ℂ (fun s => (realEpsilon xs a c hc s : ℂ)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [realEpsilon_cons, Units.val_mul]
    exact (x.differentiable_epsilon a c hc).mul ih

@[simp]
theorem realEpsilon_standard : realEpsilon xs 1 1 zero_lt_one s = realStandardEpsilon xs := by
  simp [realEpsilon, realStandardEpsilon]

/-- Positive Haar scaling multiplies by the scale to the actual model rank. -/
theorem realEpsilon_measure_scale (b : NNReal) (hb : 0 < b) :
    (realEpsilon xs a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) ^ (realModel xs).val.rank * (realEpsilon xs a c hc s : ℂ) := by
  rw [realModel_rank, coe_realEpsilon, coe_realEpsilon, NNReal.coe_mul,
    Complex.ofReal_mul, mul_pow]
  ring

end RealLaws

/-! ## Attachments to supplied representations -/

/-- A complex presentation of a supplied continuous representation: a block list
and an actual invertible linear intertwiner from its sum model. -/
structure ComplexPresentation (V : FiniteRepresentation.ContinuousObjects.{0, uV} ComplexWeil) where
  blocks : List ComplexCharacterData
  intertwiner : FiniteRepresentation.Equiv (complexModel blocks).val V.val

/-- A real presentation of a supplied continuous representation: a block list
and an actual invertible linear intertwiner from its sum model. -/
structure RealPresentation (V : FiniteRepresentation.ContinuousObjects.{0, uV} RealWeil) where
  blocks : List RealBlock
  intertwiner : FiniteRepresentation.Equiv (realModel blocks).val V.val

namespace ComplexPresentation

variable {V : FiniteRepresentation.ContinuousObjects.{0, uV} ComplexWeil}
  (P : ComplexPresentation V)

/-- The sum model presents itself, by the identity intertwiner. -/
def ofModel (ds : List ComplexCharacterData) : ComplexPresentation (complexModel ds) :=
  ⟨ds, Representation.Equiv.refl _⟩

/-- Transport a presentation along an actual equivalence of targets. -/
def transport {W : FiniteRepresentation.ContinuousObjects.{0, uW} ComplexWeil}
    (e : FiniteRepresentation.Equiv V.val W.val) : ComplexPresentation W :=
  ⟨P.blocks, P.intertwiner.trans e⟩

/-- The L-factor attached through this presentation. -/
def lFactor : ReciprocalEntire := complexLFactor P.blocks

/-- The standard epsilon attached through this presentation. -/
def standardEpsilon : ℂˣ := complexStandardEpsilon P.blocks

/-- The epsilon attached through this presentation, for
`complexScaledCharacter a` and `complexScaledMeasure c hc`. -/
def epsilon (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) : ℂˣ :=
  complexEpsilon P.blocks a c hc s

@[simp]
theorem transport_blocks {W : FiniteRepresentation.ContinuousObjects.{0, uW} ComplexWeil}
    (e : FiniteRepresentation.Equiv V.val W.val) : (P.transport e).blocks = P.blocks := rfl

/-- The target rank is the number of blocks. -/
theorem rank_eq : V.val.rank = P.blocks.length :=
  (FiniteRepresentation.rank_eq_of_equiv P.intertwiner).symm.trans (complexModel_rank _)

theorem lFactor_isPole (s : ℂ) :
    P.lFactor.IsPole s ↔
      ∃ d ∈ P.blocks, ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ) :=
  complexLFactor_isPole _ s

variable (a : ℂˣ) (c : NNReal) (hc : 0 < c) (s : ℂ)

theorem epsilon_ne_zero : (P.epsilon a c hc s : ℂ) ≠ 0 := (P.epsilon a c hc s).ne_zero

theorem differentiable_epsilon : Differentiable ℂ (fun s => (P.epsilon a c hc s : ℂ)) :=
  differentiable_complexEpsilon _ a c hc

@[simp]
theorem epsilon_standard : P.epsilon 1 1 zero_lt_one s = P.standardEpsilon :=
  complexEpsilon_standard _ s

/-- Positive Haar scaling multiplies by the scale to the rank of the target. -/
theorem epsilon_measure_scale (b : NNReal) (hb : 0 < b) :
    (P.epsilon a (b * c) (mul_pos hb hc) s : ℂ) = (b : ℂ) ^ V.val.rank * (P.epsilon a c hc s : ℂ) := by
  rw [P.rank_eq, ← complexModel_rank]
  exact complexEpsilon_measure_scale _ a c hc s b hb

end ComplexPresentation

namespace RealPresentation

variable {V : FiniteRepresentation.ContinuousObjects.{0, uV} RealWeil} (P : RealPresentation V)

/-- The sum model presents itself, by the identity intertwiner. -/
def ofModel (xs : List RealBlock) : RealPresentation (realModel xs) :=
  ⟨xs, Representation.Equiv.refl _⟩

/-- Transport a presentation along an actual equivalence of targets. -/
def transport {W : FiniteRepresentation.ContinuousObjects.{0, uW} RealWeil}
    (e : FiniteRepresentation.Equiv V.val W.val) : RealPresentation W :=
  ⟨P.blocks, P.intertwiner.trans e⟩

/-- The L-factor attached through this presentation. -/
def lFactor : ReciprocalEntire := realLFactor P.blocks

/-- The standard epsilon attached through this presentation. -/
def standardEpsilon : ℂˣ := realStandardEpsilon P.blocks

/-- The epsilon attached through this presentation, for
`realScaledCharacter a` and `realScaledMeasure c hc`. -/
def epsilon (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ) : ℂˣ :=
  realEpsilon P.blocks a c hc s

@[simp]
theorem transport_blocks {W : FiniteRepresentation.ContinuousObjects.{0, uW} RealWeil}
    (e : FiniteRepresentation.Equiv V.val W.val) : (P.transport e).blocks = P.blocks := rfl

/-- The target rank is the sum of the block ranks. -/
theorem rank_eq : V.val.rank = realRank P.blocks :=
  (FiniteRepresentation.rank_eq_of_equiv P.intertwiner).symm.trans (realModel_rank _)

theorem lFactor_isPole (s : ℂ) :
    P.lFactor.IsPole s ↔
      (∃ d : RealCharacterData, RealBlock.character d ∈ P.blocks ∧
        ∃ n : ℕ, s + (d.exponent + (d.parity.val : ℂ)) = -(2 * (n : ℂ))) ∨
      (∃ d : ComplexCharacterData, RealBlock.induced d ∈ P.blocks ∧
        ∃ n : ℕ, s + (d.exponent + (d.weight.natAbs : ℂ) / 2) = -(n : ℂ)) :=
  realLFactor_isPole _ s

variable (a : ℝˣ) (c : NNReal) (hc : 0 < c) (s : ℂ)

theorem epsilon_ne_zero : (P.epsilon a c hc s : ℂ) ≠ 0 := (P.epsilon a c hc s).ne_zero

theorem differentiable_epsilon : Differentiable ℂ (fun s => (P.epsilon a c hc s : ℂ)) :=
  differentiable_realEpsilon _ a c hc

@[simp]
theorem epsilon_standard : P.epsilon 1 1 zero_lt_one s = P.standardEpsilon :=
  realEpsilon_standard _ s

/-- Positive Haar scaling multiplies by the scale to the rank of the target. -/
theorem epsilon_measure_scale (b : NNReal) (hb : 0 < b) :
    (P.epsilon a (b * c) (mul_pos hb hc) s : ℂ) = (b : ℂ) ^ V.val.rank * (P.epsilon a c hc s : ℂ) := by
  rw [P.rank_eq, ← realModel_rank]
  exact realEpsilon_measure_scale _ a c hc s b hb

end RealPresentation

end Langlands.LocalFactor.Archimedean
