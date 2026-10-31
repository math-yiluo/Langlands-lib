import Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.CuspidalSupport.BlockPermutationTensor
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.Filtration.JordanHolderProof
import Langlands.Representation.Shahidi.IntertwiningInduced

/-!
# Adjacent two-supercuspidal products: the algebraic part of Ze80 1.11(b)

For supercuspidal `ρ, ρ'` of `GL_k` with `ρ' ≅ νρ` or `ρ ≅ νρ'`, the normalized
`(k, k)` Jacquet module of `ρ × ρ'` has length two, every nonzero proper
invariant subspace is unique and irreducible with irreducible quotient, and the
Jacquet modules of the subspace and the quotient are `ρ ⊗ ρ'` and `ρ' ⊗ ρ`.
The associated Jacquet filtration, the nonassociated subquotient theorem and
reducibility of `ρ × ρ'` are explicit hypotheses.
-/

noncomputable section

namespace Langlands.Classification.TwoSupercuspidalAdjacent

open GeneralLinear Geometric CuspidalSupport

universe uF uV uA uG uW

section Shapes

variable {k : ℕ} (hk : 0 < k)

@[simp] theorem size_twoBlocks (i : Fin 2) : (Shahidi.twoBlocks k k hk hk).size i = k := by
  fin_cases i <;> rfl

/-- The only standard shape associated to `(k, k)` is `(k, k)` itself. -/
theorem eq_of_levisAssociated {F : Type*} [Field F] {C : BlockShape (k + k)}
    (h : LevisAssociated (F := F) (Shahidi.twoBlocks k k hk hk) C) :
    C = Shahidi.twoBlocks k k hk hk := by
  obtain ⟨⟨w, hw⟩⟩ := h
  have hl := TotalConjugatingCount.length_eq hw
  refine TotalConjugatingCount.shape_ext hl.symm (fun j => ?_)
  obtain ⟨i, rfl⟩ := TotalConjugatingCount.blockMap_surjective hw j
  rw [TotalConjugatingCount.size_blockMap hw]
  exact (size_twoBlocks hk i).trans (size_twoBlocks hk _).symm

end Shapes

section Pieces

variable {k : ℕ} (hk : 0 < k) {K : Type uF} [Field K]

/-- The coordinates of block `j` are exactly those whose block index is `j`. -/
theorem range_index {n : ℕ} (B : BlockShape n) (j : Fin B.length) :
    Set.range (B.index j) = {x | blockIndex B x = j} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact blockIndex_index B j a
  · intro hx
    obtain ⟨i, a, rfl⟩ := TotalConjugatingCount.index_surjective B x
    change blockIndex B (B.index i a) = j at hx
    rw [blockIndex_index] at hx
    subst hx
    exact ⟨a, rfl⟩

theorem fin_two_eq_of_ne {a b c : Fin 2} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  revert a b c; decide

variable (w : MinimalConjugatingPermutations (F := K)
  (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk))

theorem blockMap_one_ne :
    blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 1 ≠
      blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 :=
  (TotalConjugatingCount.blockMap_injective w.property).ne (show (1 : Fin 2) ≠ 0 by decide)

/-- A minimal conjugating permutation of `(k, k)` whose block map sends the
first block to the second sends the first block onto the second in order. -/
theorem apply_castAdd_of_blockMap
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 1)
    (x : Fin k) : w.val.val (Fin.castAdd k x) = Fin.natAdd k x := by
  have hm : StrictMono
      (fun a : Fin k => w.val.val ((Shahidi.twoBlocks k k hk hk).index 0 a)) :=
    w.val.property.1 0
  have hn : StrictMono (fun a : Fin k => (Shahidi.twoBlocks k k hk hk).index 1 a) := by
    intro a b hab
    change (Shahidi.twoBlocks k k hk hk).index 1 a < (Shahidi.twoBlocks k k hk hk).index 1 b
    rw [Shahidi.twoBlocks_index_second hk hk a, Shahidi.twoBlocks_index_second hk hk b]
    simpa using hab
  have hr : Set.range (fun a : Fin k => w.val.val ((Shahidi.twoBlocks k k hk hk).index 0 a)) =
      Set.range (fun a : Fin k => (Shahidi.twoBlocks k k hk hk).index 1 a) := by
    have h1 := TotalConjugatingCount.range_block w.property 0
    rw [h] at h1
    exact h1.trans (range_index _ 1).symm
  have := congrFun ((StrictMono.range_inj_of_wellFoundedLT hm hn).mp hr) x
  change w.val.val ((Shahidi.twoBlocks k k hk hk).index 0 x) =
    (Shahidi.twoBlocks k k hk hk).index 1 x at this
  rwa [Shahidi.twoBlocks_index_first hk hk x, Shahidi.twoBlocks_index_second hk hk x] at this

theorem blockMap_one_of_blockMap_zero
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 1) :
    blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 1 = 0 := by
  have h1 := blockMap_one_ne hk w
  rw [h] at h1
  exact fin_two_eq_of_ne (a := 1) (Ne.symm h1) (show (1 : Fin 2) ≠ 0 by decide)

/-- The symmetric statement for the second block. -/
theorem apply_natAdd_of_blockMap
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 1)
    (x : Fin k) : w.val.val (Fin.natAdd k x) = Fin.castAdd k x := by
  have hm : StrictMono
      (fun a : Fin k => w.val.val ((Shahidi.twoBlocks k k hk hk).index 1 a)) :=
    w.val.property.1 1
  have hn : StrictMono (fun a : Fin k => (Shahidi.twoBlocks k k hk hk).index 0 a) := by
    intro a b hab
    change (Shahidi.twoBlocks k k hk hk).index 0 a < (Shahidi.twoBlocks k k hk hk).index 0 b
    rw [Shahidi.twoBlocks_index_first hk hk a, Shahidi.twoBlocks_index_first hk hk b]
    exact hab
  have hr : Set.range (fun a : Fin k => w.val.val ((Shahidi.twoBlocks k k hk hk).index 1 a)) =
      Set.range (fun a : Fin k => (Shahidi.twoBlocks k k hk hk).index 0 a) := by
    have h1 := TotalConjugatingCount.range_block w.property 1
    rw [blockMap_one_of_blockMap_zero hk w h] at h1
    exact h1.trans (range_index _ 0).symm
  have := congrFun ((StrictMono.range_inj_of_wellFoundedLT hm hn).mp hr) x
  change w.val.val ((Shahidi.twoBlocks k k hk hk).index 1 x) =
    (Shahidi.twoBlocks k k hk hk).index 0 x at this
  rwa [Shahidi.twoBlocks_index_first hk hk x, Shahidi.twoBlocks_index_second hk hk x] at this

/-- Entries of a Levi element pulled back along a conjugating permutation. -/
theorem leviConjugation_symm_entry (m : (Shahidi.twoBlocks k k hk hk).Levi K) (i j : Fin (k + k)) :
    (Shahidi.twoBlocks k k hk hk).leviEmbedding K
        ((leviConjugation _ _ w.val.val w.property).symm m) i j =
      (Shahidi.twoBlocks k k hk hk).leviEmbedding K m (w.val.val i) (w.val.val j) := by
  rw [leviConjugation_symm_embedding, mul_permutation_entry, permutation_inv,
    permutation_mul_entry, inv_inv]

/-- A block-swapping conjugation exchanges the two Levi factors. -/
theorem leviConjugation_symm_zero
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 1)
    (m : (Shahidi.twoBlocks k k hk hk).Levi K) :
    (leviConjugation _ _ w.val.val w.property).symm m 0 = m 1 := by
  apply Units.ext
  ext a b
  have ha : ∀ x : Fin k, w.val.val ((Shahidi.twoBlocks k k hk hk).index 0 x) =
      (Shahidi.twoBlocks k k hk hk).index 1 x := fun x => by
    have := apply_castAdd_of_blockMap hk w h x
    rwa [← Shahidi.twoBlocks_index_first hk hk x, ← Shahidi.twoBlocks_index_second hk hk x] at this
  have e := leviConjugation_symm_entry hk w m ((Shahidi.twoBlocks k k hk hk).index 0 a)
    ((Shahidi.twoBlocks k k hk hk).index 0 b)
  rw [(Shahidi.twoBlocks k k hk hk).leviEmbedding_apply_same K _ 0 a b, ha a, ha b,
    (Shahidi.twoBlocks k k hk hk).leviEmbedding_apply_same K m 1 a b] at e
  exact e

/-- A block-swapping conjugation exchanges the two Levi factors. -/
theorem leviConjugation_symm_one
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 1)
    (m : (Shahidi.twoBlocks k k hk hk).Levi K) :
    (leviConjugation _ _ w.val.val w.property).symm m 1 = m 0 := by
  apply Units.ext
  ext a b
  have ha : ∀ x : Fin k, w.val.val ((Shahidi.twoBlocks k k hk hk).index 1 x) =
      (Shahidi.twoBlocks k k hk hk).index 0 x := fun x => by
    have := apply_natAdd_of_blockMap hk w h x
    rwa [← Shahidi.twoBlocks_index_first hk hk x, ← Shahidi.twoBlocks_index_second hk hk x] at this
  have e := leviConjugation_symm_entry hk w m ((Shahidi.twoBlocks k k hk hk).index 1 a)
    ((Shahidi.twoBlocks k k hk hk).index 1 b)
  rw [(Shahidi.twoBlocks k k hk hk).leviEmbedding_apply_same K _ 1 a b, ha a, ha b,
    (Shahidi.twoBlocks k k hk hk).leviEmbedding_apply_same K m 0 a b] at e
  exact e

/-- A minimal conjugating permutation fixing the first block lies in the
block Weyl group. -/
theorem mem_blockWeyl_of_blockMap
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 0) :
    w.val.val ∈ blockWeyl (Shahidi.twoBlocks k k hk hk) := by
  have h1 : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk)
      w.val.val 1 = 1 := by
    have h' := blockMap_one_ne hk w
    rw [h] at h'
    exact fin_two_eq_of_ne (a := 0) (Ne.symm h') (show (0 : Fin 2) ≠ 1 by decide)
  intro a
  rw [TotalConjugatingCount.blockIndex_apply w.property]
  rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide)
    (blockIndex (Shahidi.twoBlocks k k hk hk) a) with hi | hi
  · rw [hi]; exact h
  · rw [hi]; exact h1

/-- Minimal conjugating permutations of `(k, k)` are determined by the image
of the first block. -/
theorem eq_of_blockMap_zero_eq
    {w₁ w₂ : MinimalConjugatingPermutations (F := K)
      (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk)}
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w₁.val.val 0 =
      blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w₂.val.val 0) :
    w₁ = w₂ := by
  have h1 : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w₁.val.val 1 =
      blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w₂.val.val 1 := by
    refine fin_two_eq_of_ne (blockMap_one_ne hk w₁).symm ?_
    rw [h]
    exact (blockMap_one_ne hk w₂).symm
  have hx := TotalConjugatingCount.eq_of_blockValue_eq (F := K) (Shahidi.twoBlocks k k hk hk)
    ⟨_, w₁⟩ ⟨_, w₂⟩ (fun i => by
      rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) i with hi | hi
      · rw [hi]; exact congrArg Fin.val h
      · rw [hi]; exact congrArg Fin.val h1)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hx).2

end Pieces

section Equivs

variable {k : ℕ} (hk : 0 < k) {K : Type uF} [Field K] [TopologicalSpace K]
  (w : MinimalConjugatingPermutations (F := K)
    (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk))
  (A₀ A₁ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k K))

/-- Transport along a block-swapping minimal permutation exchanges the two
tensor factors. -/
def swapEquiv
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 1) :
    (transport _ _ w.val.val w.property (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk A₀ A₁)).representation).Equiv
      (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk A₁ A₀)).representation :=
  Representation.Equiv.mk
    (Shahidi.pairSwap
      (V := fun i => (Classification.twoBlockFactors hk hk A₀ A₁ i : Type uV))
      (W := fun i => (Classification.twoBlockFactors hk hk A₁ A₀ i : Type uV))
      (LinearEquiv.refl ℂ A₀) (LinearEquiv.refl ℂ A₁))
    (fun m => LinearMap.ext fun x =>
      Shahidi.pairSwap_external
        (fun i => (Classification.twoBlockFactors hk hk A₀ A₁ i).obj.ρ)
        (fun i => (Classification.twoBlockFactors hk hk A₁ A₀ i).obj.ρ)
        (LinearEquiv.refl ℂ A₀) (LinearEquiv.refl ℂ A₁)
        ((leviConjugation _ _ w.val.val w.property).symm m) m
        (fun y => congrArg (fun g => A₀.obj.ρ g y) (leviConjugation_symm_zero hk w h m))
        (fun y => congrArg (fun g => A₁.obj.ρ g y) (leviConjugation_symm_one hk w h m)) x)

/-- Transport along a minimal permutation fixing the first block is
equivalent to the original representation. -/
def fixEquiv
    (h : blockMap (Shahidi.twoBlocks k k hk hk) (Shahidi.twoBlocks k k hk hk) w.val.val 0 = 0)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ ((Shahidi.twoBlocks k k hk hk).Levi K) V) :
    (transport _ _ w.val.val w.property ρ).Equiv ρ :=
  transportWeylEquiv w.val.val (mem_blockWeyl_of_blockMap hk w h) w.property ρ

end Equivs

section Separation

variable {k : ℕ} (hk : 0 < k) {K : Type uF} [Field K] [TopologicalSpace K]

/-- The Levi element with `g` in the first block and `1` in the second. -/
def firstBlock (g : GeneralLinear k K) : (Shahidi.twoBlocks k k hk hk).Levi K :=
  Fin.cases g (Fin.cases 1 finZeroElim)

/-- An element acting by a scalar on the first factor, placed in the first
block, acts by the same scalar on the external tensor product. -/
theorem external_firstBlock (A₀ A₁ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k K))
    (g : GeneralLinear k K) (c : ℂ) (hg : ∀ v, A₀.representation g v = c • v)
    (x : FiniteTensor.externalSmoothObject (Classification.twoBlockFactors hk hk A₀ A₁)) :
    (FiniteTensor.externalSmoothObject
      (Classification.twoBlockFactors hk hk A₀ A₁)).representation (firstBlock hk g) x =
      c • x := by
  revert x
  change ∀ x : PiTensorProduct ℂ
      (fun i => (Classification.twoBlockFactors hk hk A₀ A₁ i : Type uV)),
    FiniteTensor.external (fun i => (Classification.twoBlockFactors hk hk A₀ A₁ i).obj.ρ)
      (firstBlock hk g) x = c • x
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, FiniteTensor.external_tprod, smul_comm]
    congr 1
    have hv : (fun i => (Classification.twoBlockFactors hk hk A₀ A₁ i).obj.ρ
        (firstBlock hk g i) (v i)) = Function.update v 0 (c • v 0) := by
      funext i
      rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) i with hi | hi
      · subst hi
        rw [Function.update_self]
        exact hg (v 0)
      · subst hi
        rw [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
        change A₁.obj.ρ 1 (v 1) = v 1
        rw [map_one]
        rfl
    rw [hv, MultilinearMap.map_update_smul, Function.update_eq_self]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-- A central element acting by `c` on `A₀` and by `c'` on `A₁ ≅ χ A₀`, with
`χ z ≠ 1`, separates `A₀ ⊗ A₁` from `A₁ ⊗ A₀`. -/
theorem not_equiv_swap {A₀ A₁ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k K)}
    (z : GeneralLinear k K) (c c' : ℂˣ) (χ : GeneralLinear k K →* ℂˣ) (hχ : χ z ≠ 1)
    (hc : ∀ v, A₀.representation z v = (c : ℂ) • v)
    (hc' : ∀ v, A₁.representation z v = (c' : ℂ) • v)
    (f : A₁.representation.Equiv (twist χ A₀.representation)) (v : A₁) (hv : v ≠ 0)
    (x : FiniteTensor.externalSmoothObject (Classification.twoBlockFactors hk hk A₀ A₁))
    (hx : x ≠ 0)
    (e : (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk A₀ A₁)).representation.Equiv
      (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk A₁ A₀)).representation) : False := by
  have h1 : (c' : ℂ) = χ z * c := by
    have hf := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap z v
    change f (A₁.representation z v) = (χ z : ℂ) • A₀.representation z (f v) at hf
    rw [hc', hc, map_smul, smul_smul] at hf
    have hfv : f v ≠ 0 := fun h => hv (f.injective (by simpa using h))
    exact smul_left_injective ℂ hfv hf
  have h2 : (c : ℂ) = c' := by
    have he := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
      (firstBlock hk z) x
    change e ((FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk A₀ A₁)).representation (firstBlock hk z) x) =
      (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk A₁ A₀)).representation (firstBlock hk z) (e x)
      at he
    rw [external_firstBlock hk A₀ A₁ z c hc, external_firstBlock hk A₁ A₀ z c' hc',
      map_smul] at he
    have hex : e x ≠ 0 := fun h => hx (e.injective (by simpa using h))
    exact smul_left_injective ℂ hex he
  apply hχ
  apply Units.ext
  have h3 : (χ z : ℂ) * c = 1 * c := by rw [← h1, ← h2, one_mul]
  simpa using mul_right_cancel₀ c.ne_zero h3

end Separation

section Adjacent

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {k : ℕ} (hk : 0 < k)

/-- The supercuspidal factors `(ρ, ρ')` of the two blocks. -/
def twoBlockCuspidal
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    ∀ i : Fin (Shahidi.twoBlocks k k hk hk).length,
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (Shahidi.twoBlocks k k hk hk).size i) :=
  Fin.cases ρ (Fin.cases ρ' finZeroElim)

theorem twoBlockCuspidal_obj
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    (fun i => (twoBlockCuspidal F T hk ρ ρ' i).obj) =
      Classification.twoBlockFactors hk hk ρ.obj ρ'.obj := by
  let := T.topology
  funext i
  rcases (show ∀ i : Fin 2, i = 0 ∨ i = 1 by decide) i with hi | hi <;> subst hi <;> rfl

/-- The external tensor product `ρ ⊗ ρ'` is irreducible and cuspidal. -/
theorem tensor_irreducible_cuspidal
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)).IsIrreducible ∧
      IsLeviCuspidal (Shahidi.twoBlocks k k hk hk)
        (FiniteTensor.externalSmoothObject
          (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)).representation := by
  let := T.topology
  rw [← twoBlockCuspidal_obj F T hk ρ ρ']
  exact glCuspidalTensor.{uV, uF} p F T (k + k) (by omega) _ (twoBlockCuspidal F T hk ρ ρ')

/-- If `ρ' ≅ νρ`, then `ρ ⊗ ρ'` and `ρ' ⊗ ρ` are not equivalent. -/
theorem isEmpty_equiv_swap_of_twist
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (h : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass) :
    letI := T.topology
    IsEmpty ((FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)).representation.Equiv
      (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk ρ'.obj ρ.obj)).representation) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup k
  refine ⟨fun e => ?_⟩
  let χ := T.determinantPowerCharacter k 1
  let ρt := SupercuspidalRep.twist χ (T.isOpen_ker_determinantPowerCharacter k 1)
    (T.ker_determinant_le_ker_determinantPowerCharacter k 1) ρ
  change ρ'.isoClass = ρt.isoClass at h
  obtain ⟨f⟩ := (SupercuspidalRep.isoClass_eq_iff ρ' ρt).mp h
  let f' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier) (n := k)).ι.mapIso f)
  obtain ⟨ω, ⟨-, hω⟩, -⟩ := admissibleSchur_centralCharacter ρ.obj.representation
    ρ.property.2.1 ρ.property.1
  obtain ⟨ω', ⟨-, hω'⟩, -⟩ := admissibleSchur_centralCharacter ρ'.obj.representation
    ρ'.property.2.1 ρ'.property.1
  let z := scalarToCenter (n := k) (LocalFactor.PadicAbelian.uniformizerUnit T)
  obtain ⟨v, hv⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible _ ρ'.property.1
  obtain ⟨x, hx⟩ := LeviAdmissibility.exists_ne_zero_of_isIrreducible _ (tensor_irreducible_cuspidal F T hk ρ ρ').1
  refine not_equiv_swap hk (z : GeneralLinear k F.Carrier) (ω z) (ω' z) χ ?_ (hω z) (hω' z)
    f' v hv x hx e
  intro h1
  have hz := congrArg (fun a : ℂˣ => (a : ℂ)) h1
  change (T.determinantPowerCharacter k 1
    (scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℂ) = 1 at hz
  rw [IntegralTwistFreeness.scalar_uniformizer_value] at hz
  have hq : 1 < (T.residueCardinality : ℝ) := by
    exact_mod_cast T.residueCardinality_gt_one
  have hexp : -(k : ℝ) * 1 = 0 :=
    (Real.rpow_right_inj (lt_trans zero_lt_one hq) (ne_of_gt hq)).mp
      (by simpa using Complex.ofReal_injective hz)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  exact hk0 (by linarith)

/-- In the adjacent case, `ρ ⊗ ρ'` and `ρ' ⊗ ρ` are not equivalent. -/
theorem isEmpty_equiv_swap
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (h : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
        ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass) :
    letI := T.topology
    IsEmpty ((FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)).representation.Equiv
      (FiniteTensor.externalSmoothObject
        (Classification.twoBlockFactors hk hk ρ'.obj ρ.obj)).representation) := by
  let := T.topology
  rcases h with h | h
  · exact isEmpty_equiv_swap_of_twist F T hk ρ ρ' h
  · exact ⟨fun e => (isEmpty_equiv_swap_of_twist F T hk ρ' ρ h).false e.symm⟩

end Adjacent

section Quotients

open LengthCriterionProof (quotientRep lower)

variable {G : Type*} [Monoid G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The successive quotient of the whole representation by zero is the
representation itself. -/
def quotientRepBotTopEquiv (ρ : Representation ℂ G V) :
    (quotientRep (⊥ : Subrepresentation ρ) ⊤).Equiv ρ :=
  Representation.Equiv.mk
    ((Submodule.quotEquivOfEqBot (lower (⊥ : Subrepresentation ρ) ⊤) (by
        refine eq_bot_iff.2 fun x hx => (Submodule.mem_bot ℂ).2 (Subtype.ext ?_)
        change (x : V) ∈ (⊥ : Submodule ℂ V) at hx
        exact (Submodule.mem_bot ℂ).1 hx)).trans
      { toFun := fun x => (x : V)
        invFun := fun v => ⟨v, trivial⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun g => LinearMap.ext fun y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl)

/-- The representation on an invariant subspace `S` is its successive
quotient over zero. -/
theorem nonempty_equiv_quotientRep_bot (ρ : Representation ℂ G V) (S : Subrepresentation ρ) :
    Nonempty (S.toRepresentation.Equiv (quotientRep (⊥ : Subrepresentation ρ) S)) := by
  let f : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  obtain ⟨e⟩ := LengthTwo.nonempty_gradedEquiv f (S := ⊥) (T := ⊤) (S' := ⊥) (T' := S)
    (fun v _ => v.2)
    (fun w hw => ⟨⟨w, hw⟩, trivial, rfl⟩)
    (fun v _ => by
      change (v : V) = 0 ↔ v = 0
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩)
  exact ⟨(quotientRepBotTopEquiv _).symm.trans e⟩

/-- The quotient by an invariant subspace `S` is the successive quotient of
the whole representation by `S`. -/
theorem nonempty_equiv_quotientRep_top (ρ : Representation ℂ G V) (S : Subrepresentation ρ) :
    Nonempty ((ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)).Equiv
      (quotientRep S ⊤)) := by
  let f : ρ.IntertwiningMap
      (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  obtain ⟨e⟩ := LengthTwo.nonempty_gradedEquiv f (S := S) (T := ⊤) (S' := ⊥) (T' := ⊤)
    (fun _ _ => trivial)
    (fun w _ => by
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule w
      exact ⟨v, trivial, rfl⟩)
    (fun v _ => by
      change S.toSubmodule.mkQ v = 0 ↔ v ∈ S.toSubmodule
      exact Submodule.Quotient.mk_eq_zero _)
  exact ⟨(quotientRepBotTopEquiv _).symm.trans e.symm⟩

/-- For a short exact sequence `0 → ρ → σ → τ → 0`, the two-step filtration
of `σ` by the image of `ρ` has graded pieces equivalent to `ρ` and `τ`. -/
theorem twoStep_pieces_of_exact {U W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G U} {σ : Representation ℂ G V}
    {τ : Representation ℂ G W} (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap) :
    Nonempty (((LengthTwo.twoStep i.range).gradedRepresentation 0).ρ.Equiv ρ) ∧
      Nonempty (((LengthTwo.twoStep i.range).gradedRepresentation 1).ρ.Equiv τ) := by
  constructor
  · obtain ⟨e₁⟩ := LengthTwo.nonempty_gradedEquiv i (S := ⊥) (T := ⊤) (S' := ⊥) (T' := i.range)
      (fun v _ => ⟨v, rfl⟩)
      (fun w hw => by
        obtain ⟨v, hv⟩ := hw
        exact ⟨v, trivial, hv⟩)
      (fun v _ => by
        change i v = 0 ↔ v = 0
        exact map_eq_zero_iff i hi)
    exact ⟨e₁.symm.trans (quotientRepBotTopEquiv ρ)⟩
  · obtain ⟨e₂⟩ := LengthTwo.nonempty_gradedEquiv q (S := i.range) (T := ⊤) (S' := ⊥) (T' := ⊤)
      (fun _ _ => trivial)
      (fun w _ => by
        obtain ⟨v, hv⟩ := hq w
        exact ⟨v, trivial, hv⟩)
      (fun v _ => by
        change q v = 0 ↔ v ∈ LinearMap.range i.toLinearMap
        rw [hex, LinearMap.mem_ker]
        rfl)
    exact ⟨e₂.trans (quotientRepBotTopEquiv τ)⟩

/-- Two composition series of length two. If the first factor of `t` is
equivalent to `X`, every factor of `s` is equivalent to `X` or to `Y`, and the
factors of `s` are not both equivalent to `X`, then the second factor of `t` is
equivalent to `Y`. -/
theorem second_factor_of_series {A : Rep.{uA} ℂ G}
    {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    (s t : ObjectRepFiltration A 2) (hs : s.HasSimpleFactors) (ht : t.HasSimpleFactors)
    {X : Representation ℂ G U} {Y : Representation ℂ G W}
    (hsXY : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv X) ∨
      Nonempty ((s.gradedRepresentation i).ρ.Equiv Y))
    (hs01 : ¬ (Nonempty ((s.gradedRepresentation 0).ρ.Equiv X) ∧
      Nonempty ((s.gradedRepresentation 1).ρ.Equiv X)))
    (ht0 : Nonempty ((t.gradedRepresentation 0).ρ.Equiv X)) :
    Nonempty ((t.gradedRepresentation 1).ρ.Equiv Y) := by
  have hJH := jordanHolderSeriesComparison ℂ G A 2 2 s t hs ht
  obtain ⟨e', he'⟩ := hJH
  obtain ⟨ψ⟩ := ht0
  have hm0 := he' (e'.symm 0)
  rw [Equiv.apply_symm_apply] at hm0
  have hm1 := he' (e'.symm 1)
  rw [Equiv.apply_symm_apply] at hm1
  obtain ⟨φ₀⟩ := hm0
  obtain ⟨φ₁⟩ := hm1
  have hX0 : Nonempty ((s.gradedRepresentation (e'.symm 0)).ρ.Equiv X) := ⟨φ₀.trans ψ⟩
  have hne : e'.symm 1 ≠ e'.symm 0 := fun h => absurd (e'.symm.injective h) (by decide)
  rcases hsXY (e'.symm 1) with hX1 | hY1
  · exfalso
    have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
    rcases key _ _ hne with ⟨h1, h0⟩ | ⟨h1, h0⟩
    · rw [h1] at hX1
      rw [h0] at hX0
      exact hs01 ⟨hX1, hX0⟩
    · rw [h1] at hX1
      rw [h0] at hX0
      exact hs01 ⟨hX0, hX1⟩
  · obtain ⟨χ⟩ := hY1
    exact ⟨φ₁.symm.trans χ⟩

/-- A composition series `0 ⊂ S ⊂ A` with covering steps. -/
theorem hasCompositionSeriesLength_two {A : Rep.{uA} ℂ G} (S : Subrepresentation A.ρ)
    (h₁ : ⊥ ⋖ S) (h₂ : S ⋖ ⊤) : HasCompositionSeriesLength A 2 := by
  let s : ObjectRepFiltration A 2 :=
    ObjectRepFiltration.ofSubrepresentations ![⊥, S, ⊤]
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [Fin.le_def])
      rfl rfl
  refine ⟨s, (LengthCriterionProof.hasSimpleFactors_iff_covBy s).mpr fun i => ?_⟩
  fin_cases i
  · exact h₁
  · exact h₂

/-- Two distinct elements, each covering `⊥` and covered by `⊤`, are
complements of each other. -/
theorem inf_eq_bot_and_sup_eq_top {α : Type*} [Lattice α] [BoundedOrder α] {a b : α}
    (ha₀ : ⊥ ⋖ a) (ha₁ : a ⋖ ⊤) (hb₀ : ⊥ ⋖ b) (hb₁ : b ⋖ ⊤) (hab : a ≠ b) :
    a ⊓ b = ⊥ ∧ a ⊔ b = ⊤ := by
  constructor
  · rcases ha₀.eq_or_eq bot_le inf_le_left with h | h
    · exact h
    · rcases hb₀.eq_or_eq bot_le (inf_eq_left.1 h) with h' | h'
      · exact absurd h' ha₀.lt.ne'
      · exact absurd h' hab
  · rcases ha₁.eq_or_eq le_sup_left le_top with h | h
    · rcases hb₁.eq_or_eq (sup_eq_left.1 h) le_top with h' | h'
      · exact absurd h' hab
      · exact absurd h' ha₁.lt.ne
    · exact h

/-- If `S ⊓ S' = 0` and `S ⊔ S'` is everything, then `S'` is equivalent to the
quotient by `S`. -/
theorem nonempty_equiv_quotient_of_compl (ρ : Representation ℂ G V)
    {S S' : Subrepresentation ρ} (h₁ : S ⊓ S' = ⊥) (h₂ : S ⊔ S' = ⊤) :
    Nonempty (S'.toRepresentation.Equiv
      (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv))) := by
  let f : S'.toRepresentation.IntertwiningMap
      (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) :=
    { toLinearMap := S.toSubmodule.mkQ ∘ₗ S'.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  refine ⟨f.ofBijective ⟨fun x y hxy => ?_, fun y => ?_⟩⟩
  · have hq : S.toSubmodule.mkQ (x : V) = S.toSubmodule.mkQ (y : V) := hxy
    have hmem : (x : V) - y ∈ S.toSubmodule := (Submodule.Quotient.eq _).1 hq
    have hmem' : (x : V) - y ∈ S'.toSubmodule := S'.toSubmodule.sub_mem x.2 y.2
    have hinf : (x : V) - y ∈ S.toSubmodule ⊓ S'.toSubmodule := Submodule.mem_inf.2 ⟨hmem, hmem'⟩
    have hbot : (x : V) - y ∈ (S ⊓ S').toSubmodule := hinf
    rw [h₁] at hbot
    change (x : V) - y ∈ (⊥ : Submodule ℂ V) at hbot
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hbot))
  · obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule y
    have hv : v ∈ (S ⊔ S').toSubmodule := by
      rw [h₂]
      trivial
    have hv' : v ∈ S.toSubmodule ⊔ S'.toSubmodule := hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hv'
    refine ⟨⟨b, hb⟩, ?_⟩
    have ha₀ : S.toSubmodule.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero _).2 ha
    change S.toSubmodule.mkQ b = S.toSubmodule.mkQ v
    rw [← hab, map_add, ha₀, zero_add]

end Quotients

section SmoothSubquotients

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The smooth subrepresentation on `S` is the representation of `S`. -/
def subrepresentationEquiv (A : SmoothRep.{0, uG, uW} ℂ G)
    (S : Subrepresentation A.representation) :
    (SmoothRep.subrepresentation A S).representation.Equiv S.toRepresentation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => LinearMap.ext fun _ => rfl)

end SmoothSubquotients

section Structure

open LengthCriterionProof (quotientRep)
open JacquetLength

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {k : ℕ} (hk : 0 < k)

set_option hygiene false in
local notation "𝔅" => Shahidi.twoBlocks k k hk hk

theorem eq_one_of_one_add_eq_two {x : ℕ∞} (h : 1 + x = 2) : x = 1 := by
  induction x using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    have hm : 1 + m = 2 := by exact_mod_cast h
    rw [show m = 1 by omega]
    rfl

/-- There are exactly two minimal permutations conjugating the `(k, k)` Levi
onto itself. -/
theorem card_minimalConjugating :
    Nat.card (MinimalConjugatingPermutations (F := F.Carrier) 𝔅 𝔅) = 2 := by
  have := Fintype.ofFinite (BlockShape (k + k))
  obtain ⟨_, hcard⟩ := totalConjugatingCount p F (k + k) 𝔅
  rw [Nat.card_sigma, Finset.sum_eq_single 𝔅] at hcard
  · exact hcard
  · intro C _ hC
    have : IsEmpty (MinimalConjugatingPermutations (F := F.Carrier) 𝔅 C) :=
      ⟨fun w => hC (eq_of_levisAssociated hk ⟨⟨w.val.val, w.property⟩⟩)⟩
    exact Nat.card_of_isEmpty
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem levisAssociated_self : LevisAssociated (F := F.Carrier) 𝔅 𝔅 := by
  obtain ⟨⟨w⟩, -⟩ := Nat.card_pos_iff.1 (by rw [card_minimalConjugating F hk]; omega :
    0 < Nat.card (MinimalConjugatingPermutations (F := F.Carrier) 𝔅 𝔅))
  exact ⟨⟨w.val.val, w.property⟩⟩

/-- The algebraic core of Ze80 1.11(b). Let `σ` be irreducible quasicuspidal on
the `(k, k)` Levi, not equivalent to `σ'`, and let its transport along the
block-swapping minimal permutation be equivalent to `σ'`. Then the normalized
`(k, k)` Jacquet module of `π = i(σ)` has length two and `π` is nonzero. Every
invariant subspace `S` other than zero and `π` covers zero and is covered by
`π`. The Jacquet module of `S` is equivalent to `σ`, and that of `π / S` to
`σ'`. -/
theorem properStructure
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T (k + k))
    (hfilt : AssociatedJacquetFiltrationTheorem.{uF, uV} F T (k + k))
    (σ σ' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ ((𝔅).Levi F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hσq : letI := T.topology; IsLeviQuasicuspidal 𝔅 σ.representation)
    (hswap : letI := T.topology; IsEmpty (σ.representation.Equiv σ'.representation))
    (hw : letI := T.topology; ∀ w : MinimalConjugatingPermutations (F := F.Carrier) 𝔅 𝔅,
      blockMap 𝔅 𝔅 w.val.val 0 = 1 →
      Nonempty ((transport _ _ w.val.val w.property σ.representation).Equiv
        σ'.representation)) :
    letI := T.topology
    jacquetLength T {𝔅} (T.normalizedParabolicInduced 𝔅 σ.representation) = 2 ∧
    (⊥ : Subrepresentation (T.normalizedParabolicInduced 𝔅 σ.representation)) ≠ ⊤ ∧
    ∀ S : Subrepresentation (T.normalizedParabolicInduced 𝔅 σ.representation),
      S ≠ ⊥ → S ≠ ⊤ →
      (⊥ ⋖ S ∧ S ⋖ ⊤) ∧
      Nonempty ((T.normalizedJacquet 𝔅 S.toRepresentation).Equiv σ.representation) ∧
      Nonempty ((T.normalizedJacquet 𝔅
        ((T.normalizedParabolicInduced 𝔅 σ.representation).quotient S.toSubmodule
          (fun g _ hv => S.apply_mem_toSubmodule g hv))).Equiv σ'.representation) := by
  let := T.topology
  have hI1 : ∀ C, LevisAssociated (F := F.Carrier) 𝔅 C →
      C ∈ ({𝔅} : Finset (BlockShape (k + k))) :=
    fun C hC => Finset.mem_singleton.2 (eq_of_levisAssociated hk hC)
  have hπ : IsSmooth (T.normalizedParabolicInduced 𝔅 σ.representation) :=
    T.isSmooth_normalizedParabolicInduced _ σ.representation
  have hf := (hfilt 𝔅 𝔅 σ hσq (levisAssociated_self F hk)).2
  obtain ⟨r, e, s, hs⟩ := hf
  have hsimple : s.HasSimpleFactors := fun i => by
    obtain ⟨φ⟩ := hs i
    exact JacquetLength.isIrreducible_of_equiv φ.symm
      (isIrreducible_transport _ (e i).property hσ)
  have hr : r = 2 := by
    have := card_minimalConjugating F hk
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    exact this
  subst hr
  have hlen : jacquetLength T {𝔅} (T.normalizedParabolicInduced 𝔅 σ.representation) = 2 := by
    rw [jacquetLength, Finset.sum_singleton]
    have := repLength_eq_of_hasSimpleFactors s hsimple
    rw [Nat.cast_ofNat] at this
    exact this
  have hfin : jacquetLength T {𝔅} (T.normalizedParabolicInduced 𝔅 σ.representation) ≠ ⊤ := by
    rw [hlen]; simp
  have hμ := count_strictMono T {𝔅} hπ hfin
    (one_le_jacquetLength_stepQuotient T minimalNonzeroJacquet.{uF, max uF uV} hnon _ _ hI1
      σ hσq)
  have hμ0 : count T {𝔅} (⊥ : Subrepresentation
      (T.normalizedParabolicInduced 𝔅 σ.representation)) = 0 := count_bot T _
  have hμ2 : count T {𝔅} (⊤ : Subrepresentation
      (T.normalizedParabolicInduced 𝔅 σ.representation)) = 2 := by
    rw [count_top, hlen]; rfl
  have hne : (⊥ : Subrepresentation (T.normalizedParabolicInduced 𝔅 σ.representation)) ≠ ⊤ :=
    fun h => absurd (hμ0.symm.trans ((congrArg (count T {𝔅}) h).trans hμ2)) (by decide)
  refine ⟨hlen, hne, fun S hS0 hS1 => ?_⟩
  have h1 := hμ (bot_lt_iff_ne_bot.2 hS0)
  have h2 := hμ (lt_top_iff_ne_top.2 hS1)
  have hS : count T {𝔅} S = 1 := by omega
  have hcov : ⊥ ⋖ S ∧ S ⋖ ⊤ :=
    ⟨LengthTwo.covBy_of_count hμ (bot_lt_iff_ne_bot.2 hS0) (by omega),
      LengthTwo.covBy_of_count hμ (lt_top_iff_ne_top.2 hS1) (by omega)⟩
  -- the short exact sequence `S → π → π / S`
  let incl : S.toRepresentation.IntertwiningMap
      (T.normalizedParabolicInduced 𝔅 σ.representation) := subtypeMap S
  let q : (T.normalizedParabolicInduced 𝔅 σ.representation).IntertwiningMap
      ((T.normalizedParabolicInduced 𝔅 σ.representation).quotient S.toSubmodule
        (fun g _ hv => S.apply_mem_toSubmodule g hv)) :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hex : LinearMap.range incl.toLinearMap = LinearMap.ker q.toLinearMap := by
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  have hsplit := jacquetLength_eq_add_of_exact T {𝔅} incl q hπ (subtypeMap_injective S)
    (Submodule.mkQ_surjective _) hex
  have hlenS : jacquetLength T {𝔅} S.toRepresentation = 1 := by
    have hne : jacquetLength T {𝔅} S.toRepresentation ≠ ⊤ :=
      ne_top_of_le_ne_top hfin (jacquetLength_le T {𝔅} hπ S)
    rw [← ENat.natCast_toNat hne]
    change ((count T {𝔅} S : ℕ) : ℕ∞) = 1
    rw [hS]; rfl
  have hlenQ : jacquetLength T {𝔅}
      ((T.normalizedParabolicInduced 𝔅 σ.representation).quotient S.toSubmodule
        (fun g _ hv => S.apply_mem_toSubmodule g hv)) = 1 :=
    eq_one_of_one_add_eq_two ((congrArg (· + _) hlenS.symm).trans (hsplit.symm.trans hlen))
  have hirrS : (T.normalizedJacquet 𝔅 S.toRepresentation).IsIrreducible := by
    rw [← repLength_eq_one_iff]
    rw [jacquetLength, Finset.sum_singleton] at hlenS
    exact hlenS
  have hirrQ : (T.normalizedJacquet 𝔅
      ((T.normalizedParabolicInduced 𝔅 σ.representation).quotient S.toSubmodule
        (fun g _ hv => S.apply_mem_toSubmodule g hv))).IsIrreducible := by
    rw [← repLength_eq_one_iff]
    rw [jacquetLength, Finset.sum_singleton] at hlenQ
    exact hlenQ
  -- Frobenius reciprocity identifies the Jacquet module of `S`
  have hSs : IsSmooth S.toRepresentation :=
    isSmooth_of_injective (subtypeMap S) (subtypeMap_injective S) hπ
  have eS : Nonempty ((T.normalizedJacquet 𝔅 S.toRepresentation).Equiv σ.representation) := by
    let A := Parabolic.FirstAdjointness.equiv T 𝔅 hSs incl
    have hincl : incl ≠ 0 := by
      intro h
      apply hS0
      refine eq_bot_iff.2 fun v hv => ?_
      have hv0 := congrArg (fun f => f ⟨v, hv⟩) h
      exact (LengthTwo.mem_bot_iff v).2 hv0
    have hA : A ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hincl
    have := hirrS
    have : σ.representation.IsIrreducible := hσ
    exact ⟨A.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero A).resolve_right hA)⟩
  refine ⟨hcov, eS, ?_⟩
  -- the image of `r(S)` in `r(π)` is the first step of a composition series
  have hJ := T.normalizedJacquetMap_exact 𝔅 incl q hπ (subtypeMap_injective S)
    (Submodule.mkQ_surjective _) hex
  obtain ⟨hinj, hrex, hsurj⟩ := hJ
  have hP := twoStep_pieces_of_exact _ _ hinj hsurj hrex
  obtain ⟨⟨ψ0⟩, ⟨ψ1⟩⟩ := hP
  obtain ⟨eS'⟩ := eS
  have ht : (LengthTwo.twoStep (T.normalizedJacquetMap 𝔅 incl).range).HasSimpleFactors := by
    intro i
    fin_cases i
    · exact JacquetLength.isIrreducible_of_equiv (ψ0.trans eS').symm hσ
    · exact JacquetLength.isIrreducible_of_equiv ψ1.symm hirrQ
  -- the factors of the geometric filtration are `σ` and `σ'`, not both `σ`
  have hpieces : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv σ.representation) ∨
      Nonempty ((s.gradedRepresentation i).ρ.Equiv σ'.representation) := by
    intro i
    obtain ⟨χ⟩ := hs i
    rcases (show ∀ a : Fin 2, a = 0 ∨ a = 1 by decide) (blockMap 𝔅 𝔅 (e i).val.val 0) with h | h
    · exact Or.inl ⟨χ.trans (fixEquiv hk (e i) h σ.representation)⟩
    · obtain ⟨ω⟩ := hw (e i) h
      exact Or.inr ⟨χ.trans ω⟩
  have hfix : ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv σ.representation) →
      blockMap 𝔅 𝔅 (e i).val.val 0 = 0 := by
    intro i hi
    obtain ⟨φ⟩ := hi
    by_contra hne
    have h1 : blockMap 𝔅 𝔅 (e i).val.val 0 = 1 :=
      fin_two_eq_of_ne (a := 0) (Ne.symm hne) (show (0 : Fin 2) ≠ 1 by decide)
    obtain ⟨χ⟩ := hs i
    obtain ⟨ω⟩ := hw _ h1
    exact hswap.false (φ.symm.trans (χ.trans ω))
  have hnot : ¬ (Nonempty ((s.gradedRepresentation 0).ρ.Equiv σ.representation) ∧
      Nonempty ((s.gradedRepresentation 1).ρ.Equiv σ.representation)) := by
    rintro ⟨h0, h1⟩
    have h01 := e.injective (eq_of_blockMap_zero_eq hk ((hfix 0 h0).trans (hfix 1 h1).symm))
    exact absurd h01 (by decide)
  have hY := second_factor_of_series s
    (LengthTwo.twoStep (T.normalizedJacquetMap 𝔅 incl).range) hsimple ht hpieces hnot
    ⟨ψ0.trans eS'⟩
  obtain ⟨φ⟩ := hY
  exact ⟨ψ1.symm.trans φ⟩

end Structure

section Assembly

open JacquetLength

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {k : ℕ} (hk : 0 < k)

set_option hygiene false in
local notation "𝔅" => Shahidi.twoBlocks k k hk hk

/-- Ze80 1.11(b) for one adjacent pair `ρ' ≅ νρ` or `ρ ≅ νρ'`, given the
associated Jacquet filtration and the nonassociated subquotient theorem at rank
`2k`. Every nonzero proper invariant subspace of `ρ × ρ'` has Jacquet module
`ρ ⊗ ρ'` and quotient Jacquet module `ρ' ⊗ ρ`. If `ρ × ρ'` is reducible, it
has length two and exactly one such subspace, and both the subspace and the
quotient are irreducible. -/
theorem adjacentStructure
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T (k + k))
    (hfilt : AssociatedJacquetFiltrationTheorem.{uF, uV} F T (k + k))
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (h : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
        ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass) :
    letI := T.topology
    let P := (T.normalizedProductInductionFunctor 𝔅).obj
      (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)
    (¬ P.IsIrreducible →
      HasCompositionSeriesLength P.obj 2 ∧
        (∃! S : Subrepresentation P.representation, S ≠ ⊥ ∧ S ≠ ⊤) ∧
        ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
          (SmoothRep.subrepresentation P S).IsIrreducible ∧
            (SmoothRep.quotient P S).IsIrreducible) ∧
    ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      Nonempty (((T.normalizedJacquetFunctor 𝔅).obj
          (SmoothRep.subrepresentation P S)).representation.Equiv
        (FiniteTensor.externalSmoothObject
          (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)).representation) ∧
      Nonempty (((T.normalizedJacquetFunctor 𝔅).obj
          (SmoothRep.quotient P S)).representation.Equiv
        (FiniteTensor.externalSmoothObject
          (Classification.twoBlockFactors hk hk ρ'.obj ρ.obj)).representation) := by
  let := T.topology
  intro P
  have hσ := tensor_irreducible_cuspidal F T hk ρ ρ'
  have hsw := isEmpty_equiv_swap F T hk ρ ρ' h
  have hPS := properStructure F T hk hnon hfilt
    (FiniteTensor.externalSmoothObject (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj))
    (FiniteTensor.externalSmoothObject (Classification.twoBlockFactors hk hk ρ'.obj ρ.obj))
    hσ.1 hσ.2.2 hsw (fun w hw => ⟨swapEquiv hk w ρ.obj ρ'.obj hw⟩)
  obtain ⟨-, hne, hS⟩ := hPS
  have hne' : (⊥ : Subrepresentation P.representation) ≠ ⊤ := hne
  have hall : ∀ S : Subrepresentation P.representation, S ≠ ⊥ → S ≠ ⊤ →
      (⊥ ⋖ S ∧ S ⋖ ⊤) ∧
      Nonempty ((T.normalizedJacquet 𝔅 S.toRepresentation).Equiv
        (FiniteTensor.externalSmoothObject
          (Classification.twoBlockFactors hk hk ρ.obj ρ'.obj)).representation) ∧
      Nonempty ((T.normalizedJacquet 𝔅
        (P.representation.quotient S.toSubmodule
          (fun g _ hv => S.apply_mem_toSubmodule g hv))).Equiv
        (FiniteTensor.externalSmoothObject
          (Classification.twoBlockFactors hk hk ρ'.obj ρ.obj)).representation) := hS
  refine ⟨fun hred => ?_, fun S h₀ h₁ => ?_⟩
  · have hex : ∃ S : Subrepresentation P.representation, S ≠ ⊥ ∧ S ≠ ⊤ := by
      by_contra hno
      exact hred
        { toNontrivial := ⟨⟨⊥, ⊤, hne'⟩⟩
          eq_bot_or_eq_top := fun S => (em (S = ⊥)).imp id
            (fun h₀ => by_contra fun h₁ => hno ⟨S, h₀, h₁⟩) }
    obtain ⟨S, hS₀, hS₁⟩ := hex
    obtain ⟨⟨c₁, c₂⟩, -, ⟨eQ⟩⟩ := hall S hS₀ hS₁
    refine ⟨hasCompositionSeriesLength_two S c₁ c₂, ⟨S, ⟨hS₀, hS₁⟩, fun S' hT => ?_⟩,
      fun S' h₀ h₁ => ?_⟩
    · by_contra hST
      obtain ⟨⟨d₁, d₂⟩, ⟨eT⟩, -⟩ := hall S' hT.1 hT.2
      obtain ⟨hi, hs⟩ := inf_eq_bot_and_sup_eq_top c₁ c₂ d₁ d₂ (Ne.symm hST)
      obtain ⟨φ⟩ := nonempty_equiv_quotient_of_compl P.representation hi hs
      exact hsw.false (eT.symm.trans ((normalizedJacquetEquiv T 𝔅 φ).trans eQ))
    · obtain ⟨⟨d₁, d₂⟩, -, -⟩ := hall S' h₀ h₁
      constructor
      · obtain ⟨φ⟩ := nonempty_equiv_quotientRep_bot P.representation S'
        exact JacquetLength.isIrreducible_of_equiv ((subrepresentationEquiv P S').trans φ).symm
          (LengthTwo.isIrreducible_gradedRep_of_covBy d₁)
      · obtain ⟨φ⟩ := nonempty_equiv_quotientRep_top P.representation S'
        exact JacquetLength.isIrreducible_of_equiv φ.symm
          (LengthTwo.isIrreducible_gradedRep_of_covBy d₂)
  · obtain ⟨-, ⟨eS⟩, ⟨eQ⟩⟩ := hall S h₀ h₁
    exact ⟨⟨(normalizedJacquetEquiv T 𝔅 (subrepresentationEquiv P S)).trans eS⟩, ⟨eQ⟩⟩

end Assembly

section Conditional

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 1.11 from its four inputs: nonadjacent irreducibility, adjacent
reducibility, and the two Jacquet-of-induction theorems for quasicuspidal data
in every rank. The final proof module supplies these inputs. -/
theorem productStructure_of
    (ha : TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T)
    (hred : TwoSupercuspidalAdjacentProductReducible.{uF, uV} F T)
    (hnon : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hfilt : ∀ n, AssociatedJacquetFiltrationTheorem.{uF, uV} F T n) :
    TwoSupercuspidalProductStructure.{uF, uV} F T := by
  refine ⟨ha, fun k hk ρ ρ' h => ?_, fun k hk ρ ρ' h => ?_⟩
  · exact (adjacentStructure F T hk (hnon (k + k)) (hfilt (k + k)) ρ ρ' h).1
      (hred k hk ρ ρ' h)
  · exact (adjacentStructure F T hk (hnon (k + k)) (hfilt (k + k)) ρ ρ' h).2

end Conditional

end Langlands.Classification.TwoSupercuspidalAdjacent
