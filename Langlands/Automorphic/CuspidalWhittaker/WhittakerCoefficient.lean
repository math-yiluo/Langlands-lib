import Langlands.Automorphic.CuspidalWhittaker.Columns
import Langlands.Automorphic.ConstantTerm

/-!
# The global Whittaker coefficient of a cusp form

Iterating the column coefficients from column `r` down to column `1` turns a continuous
rational-left-invariant cuspidal function `φ` on `GL_{r+1}(𝔸_K)` into a function `W_φ` given by
iterated column integrals; classically this is the Whittaker coefficient
`∫_{N(K)\N(𝔸_K)} φ(u g) ψ(u)⁻¹ du`, an identification not needed here. It is linear in `φ`,
commutes with right translation, satisfies `W_φ(u g) = ψ(∑ᵢ u_{i,i+1}) W_φ(g)` for upper
unitriangular `u`, and does not vanish identically when `φ ≠ 0`. The starting level uses that
`φ` is rational-left-invariant and that its constant terms along the maximal parabolics vanish.
-/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global Langlands.GeneralLinear ContinuousRationalFunctions

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)] {r : ℕ}

/-! ### Iterating the column coefficients -/

/-- The four properties carried at level `c`. -/
structure LevelProps (c : ℕ) (F : AdelicGL K (r + 1) → ℂ) : Prop where
  continuous : Continuous F
  invariant : MirInvariant c F
  vanishing : BlockVanishing c F
  equivariant : Equivariant c F

theorem LevelProps.colCoeff {c : ℕ} (h : c < r) {F : AdelicGL K (r + 1) → ℂ}
    (hF : LevelProps (c + 1) F) : LevelProps c (colCoeff c F) :=
  ⟨continuous_colCoeff hF.continuous hF.invariant,
    mirInvariant_colCoeff h hF.continuous hF.invariant,
    blockVanishing_colCoeff h hF.continuous hF.invariant hF.vanishing,
    equivariant_colCoeff h hF.invariant hF.equivariant⟩

/-- Apply the column coefficients for the columns `k, k - 1, …, 1` in turn. -/
def descend : ℕ → (AdelicGL K (r + 1) → ℂ) → (AdelicGL K (r + 1) → ℂ)
  | 0, F => F
  | k + 1, F => descend k (colCoeff k F)

theorem levelProps_descend : ∀ k, k ≤ r → ∀ F : AdelicGL K (r + 1) → ℂ,
    LevelProps k F → LevelProps 0 (descend k F)
  | 0, _, _, hF => hF
  | k + 1, hk, F, hF => levelProps_descend k (by omega) _ (hF.colCoeff (by omega))

theorem exists_descend_ne_zero : ∀ k, k ≤ r → ∀ F : AdelicGL K (r + 1) → ℂ,
    LevelProps k F → (∃ g, F g ≠ 0) → ∃ g, descend k F g ≠ 0
  | 0, _, _, _, h => h
  | k + 1, hk, F, hF, ⟨g, hg⟩ => by
      refine exists_descend_ne_zero k (by omega) _ (hF.colCoeff (by omega)) ?_
      by_contra! hcon
      exact hg (eq_zero_of_colCoeff_eq_zero (by omega) hF.continuous hF.invariant hF.vanishing
        hcon g)

theorem descend_add : ∀ k, k ≤ r → ∀ F₁ F₂ : AdelicGL K (r + 1) → ℂ,
    LevelProps k F₁ → LevelProps k F₂ →
      ∀ g, descend k (fun x => F₁ x + F₂ x) g = descend k F₁ g + descend k F₂ g
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, hk, F₁, F₂, h₁, h₂, g => by
      simp only [descend]
      rw [show colCoeff k (fun x => F₁ x + F₂ x) = fun x => colCoeff k F₁ x + colCoeff k F₂ x from
        funext (colCoeff_add h₁.continuous h₁.invariant h₂.continuous h₂.invariant)]
      exact descend_add k (by omega) _ _ (h₁.colCoeff (by omega)) (h₂.colCoeff (by omega)) g

theorem descend_const_mul : ∀ k (a : ℂ) (F : AdelicGL K (r + 1) → ℂ) g,
    descend k (fun x => a * F x) g = a * descend k F g
  | 0, _, _, _ => rfl
  | k + 1, a, F, g => by
      simp only [descend]
      rw [show colCoeff k (fun x => a * F x) = fun x => a * colCoeff k F x from
        funext (colCoeff_const_mul k a F)]
      exact descend_const_mul k a _ g

theorem descend_mul_right : ∀ k (F : AdelicGL K (r + 1) → ℂ) (x g : AdelicGL K (r + 1)),
    descend k (fun g' => F (g' * x)) g = descend k F (g * x)
  | 0, _, _, _ => rfl
  | k + 1, F, x, g => by
      simp only [descend]
      rw [show colCoeff k (fun g' => F (g' * x)) = fun g' => colCoeff k F (g' * x) from
        funext fun g' => colCoeff_mul_right k F x g']
      exact descend_mul_right k _ x g

/-! ### The starting level -/

section Block

variable {m : ℕ} (hab : m + (r + 1 - m) = r + 1)

/-- The block numbering used by `blockUnipotent`. -/
def blockIndex : Fin m ⊕ Fin (r + 1 - m) ≃ Fin (r + 1) := finSumFinEquiv.trans (finCongr hab)

@[simp] theorem blockIndex_inl (a : Fin m) : ((blockIndex hab (Sum.inl a) : Fin (r + 1)) : ℕ) = a :=
  rfl

@[simp] theorem blockIndex_inr (b : Fin (r + 1 - m)) :
    ((blockIndex hab (Sum.inr b) : Fin (r + 1)) : ℕ) = m + b := rfl

/-- The `(a, b)`-block of matrix coordinates. -/
def blockPart {T : Type*} (X : Fin (r + 1) × Fin (r + 1) → T) :
    Matrix (Fin m) (Fin (r + 1 - m)) T :=
  Matrix.of fun a b => X (blockIndex hab (Sum.inl a), blockIndex hab (Sum.inr b))

theorem blkUnit_eq_blockUnipotent (X : Fin (r + 1) × Fin (r + 1) → Adeles K) :
    blkUnit m r X = blockUnipotent hab (blockPart hab X) := by
  apply Units.ext
  ext i j
  obtain ⟨p, rfl⟩ := (blockIndex hab).surjective i
  obtain ⟨q, rfl⟩ := (blockIndex hab).surjective j
  rw [blockUnipotent_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  change _ = Matrix.fromBlocks 1 (blockPart hab X) 0 1 ((blockIndex hab).symm (blockIndex hab p))
    ((blockIndex hab).symm (blockIndex hab q))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, blkUnit_val, Matrix.add_apply, blkMat_apply]
  simp only [Matrix.one_apply, (blockIndex hab).injective.eq_iff]
  rcases p with a | b <;> rcases q with a' | b'
  · have h1 : ¬((a : ℕ) < m ∧ m ≤ (a' : ℕ) ∧ (a' : ℕ) ≤ r) := fun h => by
      have := a'.isLt
      omega
    simp only [blockIndex_inl, h1, ite_false, add_zero, Matrix.fromBlocks_apply₁₁,
      Matrix.one_apply, Sum.inl.injEq]
  · have h1 : (a : ℕ) < m ∧ m ≤ m + (b' : ℕ) ∧ m + (b' : ℕ) ≤ r :=
      ⟨a.isLt, by omega, by have := b'.isLt; omega⟩
    simp only [blockIndex_inl, blockIndex_inr, h1, Matrix.fromBlocks_apply₁₂,
      reduceCtorEq, ite_false, zero_add]
    rfl
  · have h1 : ¬(m + (b : ℕ) < m ∧ m ≤ (a' : ℕ) ∧ (a' : ℕ) ≤ r) := fun h => by omega
    simp only [blockIndex_inl, blockIndex_inr, h1, ite_false, add_zero, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, reduceCtorEq]
  · have h1 : ¬(m + (b : ℕ) < m ∧ m ≤ m + (b' : ℕ) ∧ m + (b' : ℕ) ≤ r) := fun h => by omega
    simp only [blockIndex_inr, h1, ite_false, add_zero, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply, Sum.inr.injEq]

/-- The block projection of torus coordinates. -/
def blockPartHom : (Fin (r + 1) × Fin (r + 1) → AdeleQuotient K) →+
    Matrix (Fin m) (Fin (r + 1 - m)) (AdeleQuotient K) where
  toFun := blockPart hab
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_blockPartHom : Continuous (blockPartHom (K := K) hab) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _

theorem surjective_blockPartHom : Function.Surjective (blockPartHom (K := K) hab) := by
  intro M
  refine ⟨fun p => match (blockIndex hab).symm p.1, (blockIndex hab).symm p.2 with
    | Sum.inl a', Sum.inr b' => M a' b'
    | _, _ => 0, ?_⟩
  ext a b
  change (match (blockIndex hab).symm (blockIndex hab (Sum.inl a)),
    (blockIndex hab).symm (blockIndex hab (Sum.inr b)) with
    | Sum.inl a', Sum.inr b' => M a' b'
    | _, _ => 0) = M a b
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The torus block integral is the published constant term. -/
theorem torusIntegral_blkUnit_eq_constantTerm (f : ContinuousRationalFunctions K (r + 1))
    (g : AdelicGL K (r + 1)) :
    torusIntegral (Fin (r + 1) × Fin (r + 1)) (fun X => evaluate K (r + 1) f (blkUnit m r X * g)) =
      constantTerm K (r + 1) hab f g := by
  let : MeasurableSpace (Matrix (Fin m) (Fin (r + 1 - m)) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin m) (Fin (r + 1 - m)) (AdeleQuotient K)) := ⟨rfl⟩
  have := matrixQuotientHaar_isAddHaarMeasure K m (r + 1 - m)
  have : SecondCountableTopology (Matrix (Fin m) (Fin (r + 1 - m)) (AdeleQuotient K)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin (r + 1 - m) → AdeleQuotient K))
  have hpt : ∀ t : Fin (r + 1) × Fin (r + 1) → AdeleQuotient K,
      evaluate K (r + 1) f (blkUnit m r (torusLift t) * g) =
        constantTermIntegrand K (r + 1) hab f g (blockPartHom hab t) := by
    intro t
    rw [blkUnit_eq_blockUnipotent hab, ← constantTermIntegrand_mk]
    congr 1
    ext a b
    exact congrFun (torusMk_torusLift t) _
  unfold torusIntegral constantTerm
  simp_rw [hpt]
  exact integral_comp_surjective (torusHaar K (Fin (r + 1) × Fin (r + 1)))
    (matrixQuotientHaar K m (r + 1 - m)) (blockPartHom hab) (continuous_blockPartHom hab)
    (surjective_blockPartHom hab) (continuous_constantTermIntegrand hab f g)

end Block

/-- A continuous rational-left-invariant cuspidal function satisfies the level-`r` properties. -/
theorem levelProps_top (f : ContinuousRationalFunctions K (r + 1))
    (hf : ∀ (a b : ℕ) (h : a + b = r + 1), 0 < a → 0 < b → ∀ g,
      constantTerm K (r + 1) h f g = 0) :
    LevelProps r (evaluate K (r + 1) f) where
  continuous := continuous_evaluate K (r + 1) f
  invariant := fun γ _ g => evaluate_rational K (r + 1) f γ g
  vanishing := by
    intro m hm1 hmr g
    have hab : m + (r + 1 - m) = r + 1 := by omega
    rw [torusIntegral_blkUnit_eq_constantTerm hab f g]
    exact hf m (r + 1 - m) hab (by omega) (by omega) g
  equivariant := by
    intro u g hu
    have hu1 : u = 1 := by
      apply Units.ext
      ext i j
      exact hu i j (Or.inr (by omega))
    have hs : superSum r u = 0 := by
      unfold superSum
      exact Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)
    rw [hs, hu1, one_mul, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]

end Langlands.Automorphic.CuspidalWhittaker
