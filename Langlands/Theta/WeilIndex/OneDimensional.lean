import Langlands.Theta.WeilIndex.NormForm
import Langlands.ClassFieldTheory.Local.HilbertSymbol
import Langlands.HarmonicAnalysis.CharacterTransport
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The Weil index in dimension one

GKT §3.2.1–3.2.3: Proposition 3.13 (c) and Corollary 3.14 for quadratic forms, the reduction to
dimension one (p. 82), Corollary 3.15 (`γ⁸ = 1`), the norm form of a quaternion algebra
(Proposition 3.17), Lemma 3.18, the normalized Weil index (3.20) with Proposition 3.19
(`γ(ab, ψ) = γ(a, ψ) γ(b, ψ) (a, b)_F`), Corollaries 3.20 and 3.22.

`F` is a nonarchimedean local field with `2 ≠ 0` and `ψ` a non-trivial unitary character of `F`.
`weilIndexOne ψ = γ(ψ ∘ q₁)`, `q₁(x) = x²`, is the book's `γ(ψ)`; so
`γ(ψ_a) = weilIndexOne (ψ.scale a)`
is the Weil index of `x ↦ ψ(a x²)` ((3.19)), and `normalizedWeilIndex a ψ = γ(ψ_a)/γ(ψ)` is
`γ(a, ψ)` ((3.20)).

**Proposition 3.19 without the division quaternion algebra.** The book computes
`γ(ψ ∘ ⟨1, -a, -b, ab⟩) = (a, b)_F` from `γ(ψ ∘ N_D) = -1` for the division quaternion algebra `D`
(Proposition 3.17, an integral over a lattice of `D`). Here: if `a` is a square the form is
hyperbolic; otherwise `⟨1, -a, -b, ab⟩ = N ⊕ (-b) N` for the norm form `N` of `E = F(√a)`, and
`γ(ψ ∘ t N) = η(t) γ(ψ ∘ N)` (`weilIndex_mul_norm`, from the Gauss integrals of the norm form) gives
`γ(ψ ∘ N)² = η(-1)` (with `γ(ψ ∘ (-N)) = γ(ψ ∘ N)⁻¹`) and `γ(ψ ∘ ⟨1, -a, -b, ab⟩) =
η(-b) γ(ψ ∘ N)² = η(b) = (a, b)_F` (`weilIndexOne_mul_four`). Proposition 3.17 then follows for
every quaternion algebra which is a division algebra (`weilIndex_quaternion_of_isUnit`), and in
general `γ(ψ ∘ N_{(a,b)}) = (a, b)_F` (`weilIndex_quaternion`).
-/

noncomputable section

open MeasureTheory

namespace Langlands.Theta

open Langlands.HarmonicAnalysis Langlands.LocalClassField

section Defs

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **The Weil index of `ψ`** (GKT (3.19)): `γ(ψ) = γ(ψ ∘ q₁)`, `q₁(x) = x²`; for `ψ_a = ψ(a ·)`,
`weilIndexOne (ψ.scale a)` is the book's `γ(ψ_a) = γ(ψ ∘ q_a)`, `q_a(x) = a x²`. -/
def weilIndexOne (ψ : UnitaryAdditiveCharacter F) : ℂ :=
  weilIndex fun x : F => ψ.complex (x ^ 2)

/-- **The normalized Weil index** (Weil constant) `γ(a, ψ) = γ(ψ_a) / γ(ψ)` (GKT (3.20)). -/
def normalizedWeilIndex (a : Fˣ) (ψ : UnitaryAdditiveCharacter F) : ℂ :=
  weilIndexOne (ψ.scale a) / weilIndexOne ψ

end Defs

namespace WeilIndex.Internal

variable {F : Type*} [Field F] [TopologicalSpace F]

theorem conj_complex (ψ : UnitaryAdditiveCharacter F) (t : F) :
    starRingEnd ℂ (ψ.complex t) = ψ.complex (-t) := by
  rw [UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.complex_apply,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]

theorem complex_sum {ι : Type*} (ψ : UnitaryAdditiveCharacter F) (s : Finset ι) (g : ι → F) :
    ψ.complex (∑ i ∈ s, g i) = ∏ i ∈ s, ψ.complex (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- A linear equivalence of spaces with their module topologies is an additive homeomorphism. -/
def linearEquivToContinuousAddEquiv {K : Type*} [Field K] [TopologicalSpace K] {V W : Type*}
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V] [AddCommGroup W]
    [Module K W] [TopologicalSpace W] [IsModuleTopology K W] (e : V ≃ₗ[K] W) : V ≃ₜ+ W :=
  have := IsModuleTopology.toContinuousAdd K V
  have := IsModuleTopology.toContinuousAdd K W
  have := IsModuleTopology.toContinuousSMul K V
  have := IsModuleTopology.toContinuousSMul K W
  { e.toAddEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem linearEquivToContinuousAddEquiv_apply {K : Type*} [Field K] [TopologicalSpace K]
    {V W : Type*} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
    [AddCommGroup W] [Module K W] [TopologicalSpace W] [IsModuleTopology K W] (e : V ≃ₗ[K] W)
    (v : V) : linearEquivToContinuousAddEquiv e v = e v := rfl

end WeilIndex.Internal

open WeilIndex.Internal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

namespace WeilIndex.Internal

theorem secondCountableTopology_self : SecondCountableTopology F :=
  secondCountableTopology_of_finiteDimensional F F

theorem locallyCompactSpace_self : LocallyCompactSpace F :=
  locallyCompactSpace_of_finiteDimensional F F

theorem compactOpenExhaustion_self : CompactOpenExhaustion F :=
  compactOpenExhaustion_of_finiteDimensional F F

end WeilIndex.Internal

attribute [local instance] WeilIndex.Internal.secondCountableTopology_self
  WeilIndex.Internal.locallyCompactSpace_self WeilIndex.Internal.compactOpenExhaustion_self

variable [NeZero (2 : F)] (ψ : UnitaryAdditiveCharacter F)

/-! ### Dimension one -/

/-- `x ↦ ψ(a x²)` is a character of second degree on `F`, with bicharacter `ψ(2 a x y)`. -/
theorem isCharacterOfSecondDegree_mul_sq (a : Fˣ) :
    IsCharacterOfSecondDegree fun x : F => ψ.complex (a * x ^ 2) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let β : F →ₗ[F] F →ₗ[F] F := (2 * (a : F)) • LinearMap.mul F F
  have hβ : ∀ x y, β x y = 2 * a * (x * y) := fun x y => rfl
  have he := isSelfDualBicharacter_of_symm (V := F) ψ.continuous_complex ψ.norm_complex
    ψ.complex_ne_one β (fun x y => by rw [hβ, hβ, mul_comm x y]) fun y hy => by
      have := hy 1
      rw [hβ, one_mul] at this
      simpa [h2, a.ne_zero] using this
  refine IsCharacterOfSecondDegree.of_bicharacter he (fun x => ψ.norm_complex _)
    ((isLocallyConstant_of_continuous_addChar _ ψ.continuous_complex).comp_continuous
      (by fun_prop)) fun x y => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hβ]
  congr 1
  ring

omit [NeZero (2 : F)] in
theorem weilIndexOne_scale (a : Fˣ) :
    weilIndexOne (ψ.scale a) = weilIndex fun x : F => ψ.complex (a * x ^ 2) := rfl

theorem norm_weilIndexOne : ‖weilIndexOne ψ‖ = 1 := by
  have h := norm_weilIndex (isCharacterOfSecondDegree_mul_sq ψ 1)
  simpa [weilIndexOne] using h

theorem weilIndexOne_ne_zero : weilIndexOne ψ ≠ 0 := by
  intro h
  have := norm_weilIndexOne ψ
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **GKT Proposition 3.13 (b)** in dimension one: `γ(ψ_{-a}) = γ(ψ_a)⁻¹`. -/
theorem weilIndexOne_scale_neg (a : Fˣ) :
    weilIndexOne (ψ.scale (-a)) = (weilIndexOne (ψ.scale a))⁻¹ := by
  rw [weilIndexOne_scale, weilIndexOne_scale,
    ← weilIndex_conj_eq_inv (isCharacterOfSecondDegree_mul_sq ψ a)]
  congr 1
  funext x
  rw [conj_complex, Units.val_neg, neg_mul]

/-- The multiplication by a unit as an additive homeomorphism of `F`. -/
private def mulLeftAddEquiv (b : Fˣ) : F ≃ₜ+ F where
  toFun x := b * x
  invFun x := ((b⁻¹ : Fˣ) : F) * x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- **GKT Lemma 3.18**: `γ(ψ_{a b²}) = γ(ψ_a)`. -/
theorem weilIndexOne_scale_mul_sq (a b : Fˣ) :
    weilIndexOne (ψ.scale (a * b ^ 2)) = weilIndexOne (ψ.scale a) := by
  rw [weilIndexOne_scale, weilIndexOne_scale,
    ← weilIndex_comp_addEquiv (isCharacterOfSecondDegree_mul_sq ψ a) (mulLeftAddEquiv b)]
  congr 1
  funext x
  simp only [mulLeftAddEquiv, ContinuousAddEquiv.coe_mk, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    Units.val_mul, Units.val_pow_eq_pow_val]
  congr 1
  ring

theorem weilIndexOne_scale_sq (b : Fˣ) : weilIndexOne (ψ.scale (b ^ 2)) = weilIndexOne ψ := by
  have h := weilIndexOne_scale_mul_sq ψ 1 b
  rwa [one_mul, UnitaryAdditiveCharacter.scale_one] at h

/-- **Reduction to dimension one** (GKT p. 82): for a diagonal form `x ↦ ∑ aᵢ xᵢ²`,
`γ(ψ ∘ q) = ∏ γ(ψ_{aᵢ})` (Proposition 3.13 (d)). -/
theorem weilIndex_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → Fˣ) :
    weilIndex (fun x : ι → F => ψ.complex (∑ i, (a i : F) * x i ^ 2)) =
      ∏ i, weilIndexOne (ψ.scale (a i)) := by
  have e : (fun x : ι → F => ψ.complex (∑ i, (a i : F) * x i ^ 2)) =
      fun x => ∏ i, (fun i (y : F) => ψ.complex ((a i : F) * y ^ 2)) i (x i) := by
    funext x; rw [complex_sum]
  rw [e, weilIndex_pi fun i => isCharacterOfSecondDegree_mul_sq ψ (a i)]
  rfl

theorem isCharacterOfSecondDegree_diagonal {ι : Type} [Fintype ι] (a : ι → Fˣ) :
    IsCharacterOfSecondDegree fun x : ι → F => ψ.complex (∑ i, (a i : F) * x i ^ 2) := by
  classical
  have e : (fun x : ι → F => ψ.complex (∑ i, (a i : F) * x i ^ 2)) =
      fun x => ∏ i, (fun i (y : F) => ψ.complex ((a i : F) * y ^ 2)) i (x i) := by
    funext x; rw [complex_sum]
  rw [e]
  exact IsCharacterOfSecondDegree.pi fun i => isCharacterOfSecondDegree_mul_sq ψ (a i)

/-! ### Quadratic forms: Proposition 3.13 (c), Corollary 3.14 -/

section QuadraticForm

variable {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V]
  [IsModuleTopology F V] {V' : Type} [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
  [TopologicalSpace V'] [IsModuleTopology F V']

omit [NeZero (2 : F)] in
/-- **GKT Corollary 3.14** (Proposition 3.13 (a)): isometric quadratic spaces have the same Weil
index. -/
theorem weilIndex_quadraticForm_isometryEquiv {q : QuadraticForm F V} {q' : QuadraticForm F V'}
    (e : q.IsometryEquiv q') (hq' : (QuadraticMap.polarBilin q').SeparatingLeft) :
    weilIndex (fun x => ψ.complex (q x)) = weilIndex (fun x => ψ.complex (q' x)) := by
  have := IsModuleTopology.isTopologicalAddGroup F V
  have := IsModuleTopology.isTopologicalAddGroup F V'
  have := locallyCompactSpace_of_finiteDimensional F V
  have := secondCountableTopology_of_finiteDimensional F V
  have := compactOpenExhaustion_of_finiteDimensional F V
  have := t2Space_of_finiteDimensional F V
  have := locallyCompactSpace_of_finiteDimensional F V'
  have := secondCountableTopology_of_finiteDimensional F V'
  have := compactOpenExhaustion_of_finiteDimensional F V'
  have := t2Space_of_finiteDimensional F V'
  have h := weilIndex_comp_addEquiv (isCharacterOfSecondDegree_quadraticForm ψ.continuous_complex
    ψ.norm_complex ψ.complex_ne_one q' hq') (linearEquivToContinuousAddEquiv e.toLinearEquiv)
  rw [← h]
  congr 1
  funext x
  rw [linearEquivToContinuousAddEquiv_apply]
  exact congrArg _ (e.map_app x).symm

omit [NeZero (2 : F)] in
/-- **GKT Proposition 3.13 (c)**: if `-1` is a square in `F`, then `γ(ψ ∘ q)² = 1`. -/
theorem weilIndex_sq_eq_one_of_isSquare_neg_one (q : QuadraticForm F V)
    (hq : (QuadraticMap.polarBilin q).SeparatingLeft) (h : IsSquare (-1 : F)) :
    weilIndex (fun x => ψ.complex (q x)) ^ 2 = 1 := by
  have := IsModuleTopology.isTopologicalAddGroup F V
  have := locallyCompactSpace_of_finiteDimensional F V
  have := secondCountableTopology_of_finiteDimensional F V
  have := compactOpenExhaustion_of_finiteDimensional F V
  have := t2Space_of_finiteDimensional F V
  obtain ⟨i, hi⟩ := h
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  have hf := isCharacterOfSecondDegree_quadraticForm ψ.continuous_complex ψ.norm_complex
    ψ.complex_ne_one q hq
  let T : V ≃ₗ[F] V := LinearEquiv.smulOfNeZero F V i hi0
  have h1 := weilIndex_comp_addEquiv hf (linearEquivToContinuousAddEquiv T)
  have h2 := weilIndex_conj_eq_inv hf
  have e : (fun x => ψ.complex (q (linearEquivToContinuousAddEquiv T x))) =
      fun x => starRingEnd ℂ (ψ.complex (q x)) := by
    funext x
    rw [linearEquivToContinuousAddEquiv_apply, conj_complex]
    simp only [T, LinearEquiv.smulOfNeZero_apply, QuadraticMap.map_smul, smul_eq_mul]
    rw [← hi]
    ring_nf
  rw [e, h2] at h1
  have hw := weilIndex_ne_zero hf
  rw [sq]
  calc weilIndex (fun x => ψ.complex (q x)) * weilIndex (fun x => ψ.complex (q x))
      = weilIndex (fun x => ψ.complex (q x)) * (weilIndex (fun x => ψ.complex (q x)))⁻¹ := by
        rw [h1]
    _ = 1 := mul_inv_cancel₀ hw

end QuadraticForm

/-! ### The norm form of `F(√a)` and the four-dimensional form -/

/-- The Weil index of `t N` on `E = F(√a)` is `γ(ψ_t) γ(ψ_{-a t})`. -/
private theorem weilIndex_mul_norm_quadraticAlgebra (a : Fˣ)
    [TopologicalSpace (QuadraticAlgebra F (a : F) 0)]
    [IsModuleTopology F (QuadraticAlgebra F (a : F) 0)] (t : Fˣ) :
    weilIndex (fun z : QuadraticAlgebra F (a : F) 0 => ψ.complex (t * Algebra.norm F z)) =
      weilIndexOne (ψ.scale t) * weilIndexOne (ψ.scale (-(a * t))) := by
  have := IsModuleTopology.isTopologicalAddGroup F (QuadraticAlgebra F (a : F) 0)
  have := locallyCompactSpace_of_finiteDimensional F (QuadraticAlgebra F (a : F) 0)
  have := secondCountableTopology_of_finiteDimensional F (QuadraticAlgebra F (a : F) 0)
  have := compactOpenExhaustion_of_finiteDimensional F (QuadraticAlgebra F (a : F) 0)
  have := t2Space_of_finiteDimensional F (QuadraticAlgebra F (a : F) 0)
  let c : Fin 2 → Fˣ := ![t, -(a * t)]
  let T := linearEquivToContinuousAddEquiv (QuadraticAlgebra.linearEquivTuple (a : F) 0)
  have h := weilIndex_comp_addEquiv (isCharacterOfSecondDegree_diagonal ψ c) T
  have e : (fun z : QuadraticAlgebra F (a : F) 0 => ψ.complex (t * Algebra.norm F z)) =
      fun z => ψ.complex (∑ i, (c i : F) * T z i ^ 2) := by
    funext z
    rw [algebra_norm_quadraticAlgebra, Fin.sum_univ_two, linearEquivToContinuousAddEquiv_apply,
      QuadraticAlgebra.linearEquivTuple_apply]
    simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_neg, Units.val_mul]
    congr 1
    ring
  rw [e, h, weilIndex_diagonal, Fin.prod_univ_two]
  rfl

/-- **The four-dimensional form `⟨1, -a, -b, ab⟩`** (the norm form of the quaternion algebra
`(a, b)_F`, GKT Proposition B.50): `γ(ψ) γ(ψ_{-a}) γ(ψ_{-b}) γ(ψ_{ab}) = (a, b)_F` (the key step of
the proof of Proposition 3.19). -/
theorem weilIndexOne_mul_four (a b : Fˣ) :
    weilIndexOne ψ * weilIndexOne (ψ.scale (-a)) * weilIndexOne (ψ.scale (-b)) *
        weilIndexOne (ψ.scale (a * b)) = ((hilbertSymbol F a b : ℤ) : ℂ) := by
  classical
  have hneg : ∀ c : Fˣ, weilIndexOne (ψ.scale c) * weilIndexOne (ψ.scale (-c)) = 1 := fun c => by
    rw [weilIndexOne_scale_neg, mul_inv_cancel₀]
    have := weilIndexOne_ne_zero (ψ.scale c)
    exact this
  by_cases h : IsSquare (a : F)
  · -- `a = r²`: the form is hyperbolic
    obtain ⟨r, hr⟩ := h
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    set u := Units.mk0 r hr0
    have ha : a = u ^ 2 := Units.ext (by simp [u, hr, sq])
    have hab : hilbertSymbol F a b = 1 := by rw [ha, hilbertSymbol_sq_left]
    have h1 : weilIndexOne (ψ.scale (-a)) = weilIndexOne (ψ.scale (-1)) := by
      rw [ha, show -(u ^ 2) = (-1) * u ^ 2 by rw [neg_one_mul], weilIndexOne_scale_mul_sq]
    have h2 : weilIndexOne (ψ.scale (a * b)) = weilIndexOne (ψ.scale b) := by
      rw [ha, mul_comm, weilIndexOne_scale_mul_sq]
    rw [hab, h1, h2, Units.val_one, Int.cast_one]
    have := hneg 1
    rw [UnitaryAdditiveCharacter.scale_one] at this
    have := hneg b
    calc weilIndexOne ψ * weilIndexOne (ψ.scale (-1)) * weilIndexOne (ψ.scale (-b)) *
          weilIndexOne (ψ.scale b)
        = (weilIndexOne ψ * weilIndexOne (ψ.scale (-1))) *
            (weilIndexOne (ψ.scale b) * weilIndexOne (ψ.scale (-b))) := by ring
      _ = 1 := by rw [‹weilIndexOne ψ * weilIndexOne (ψ.scale (-1)) = 1›, hneg b, one_mul]
  · -- `a` not a square: `⟨1, -a, -b, ab⟩ = N ⊕ (-b) N` for `E = F(√a)`
    have : Fact (¬ IsSquare (a : F)) := ⟨h⟩
    let E := QuadraticAlgebra F (a : F) 0
    let _ : TopologicalSpace E := moduleTopology F E
    have : IsModuleTopology F E := ⟨rfl⟩
    have hE := isQuadraticInvolution_quadraticAlgebraConj (F := F) a.ne_zero
    have : IsGalois F E := hE.isGalois
    have hd : (QuadraticAlgebra.omega : E) * QuadraticAlgebra.omega = algebraMap F E a := by
      rw [QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
    have : FiniteDimensional F E := hE.finite
    have := IsModuleTopology.isTopologicalAddGroup F E
    have := locallyCompactSpace_of_finiteDimensional F E
    have := secondCountableTopology_of_finiteDimensional F E
    have := compactOpenExhaustion_of_finiteDimensional F E
    have := t2Space_of_finiteDimensional F E
    set n : Fˣ → ℂ := fun t => weilIndex fun z : E => ψ.complex (t * Algebra.norm F z)
    have hn : ∀ t, n t = normSign E t * n 1 := fun t => by
      have := weilIndex_mul_norm hE ψ.continuous_complex ψ.norm_complex ψ.complex_ne_one t
      simp only [n, Units.val_one, one_mul]
      exact this
    have hη : ∀ t, normSign E t = ((hilbertSymbol F a t : ℤ) : ℂ) := fun t =>
      normSign_eq_hilbertSymbol hE hd t
    have hn1 : n 1 * n (-1) = 1 := by
      have hf := isCharacterOfSecondDegree_mul_norm hE ψ.continuous_complex ψ.norm_complex
        ψ.complex_ne_one (1 : Fˣ)
      have h2 := weilIndex_conj_eq_inv hf
      have e : (fun z : E => starRingEnd ℂ (ψ.complex (((1 : Fˣ) : F) * Algebra.norm F z))) =
          fun z => ψ.complex (((-1 : Fˣ) : F) * Algebra.norm F z) := by
        funext z; rw [conj_complex]; simp
      rw [e] at h2
      simp only [n]
      rw [h2, mul_inv_cancel₀ (weilIndex_ne_zero hf)]
    have hsq : ∀ s : Fˣ, (((hilbertSymbol F a s : ℤ) : ℂ)) ^ 2 = 1 := fun s => by
      rcases hilbertSymbol_eq_one_or a s with h' | h' <;> simp [h']
    -- `n(1) = γ(ψ) γ(ψ_{-a})`, `n(-b) = γ(ψ_{-b}) γ(ψ_{ab})`
    have e1 := weilIndex_mul_norm_quadraticAlgebra ψ a 1
    have e2 := weilIndex_mul_norm_quadraticAlgebra ψ a (-b)
    rw [UnitaryAdditiveCharacter.scale_one, mul_one] at e1
    rw [show -(a * -b) = a * b by rw [mul_neg, neg_neg]] at e2
    change n 1 = _ at e1
    change n (-b) = _ at e2
    rw [mul_assoc (weilIndexOne ψ * _), ← e1, ← e2, hn (-b), hη]
    have hm1 := hn (-1)
    rw [hη] at hm1
    have key : n 1 * n 1 = ((hilbertSymbol F a (-1) : ℤ) : ℂ) := by
      have h3 : n 1 * (((hilbertSymbol F a (-1) : ℤ) : ℂ) * n 1) = 1 := by rw [← hm1, hn1]
      have h4 := hsq (-1)
      linear_combination ((hilbertSymbol F a (-1) : ℤ) : ℂ) * h3 - n 1 ^ 2 * h4
    have hmb : ((hilbertSymbol F a (-b) : ℤ) : ℂ) =
        ((hilbertSymbol F a (-1) : ℤ) : ℂ) * ((hilbertSymbol F a b : ℤ) : ℂ) := by
      rw [show -b = (-1) * b by rw [neg_one_mul], map_mul]
      push_cast
      ring
    rw [hmb]
    have hb := hsq (-1)
    linear_combination ((hilbertSymbol F a (-1) : ℤ) : ℂ) * ((hilbertSymbol F a b : ℤ) : ℂ) * key +
      ((hilbertSymbol F a b : ℤ) : ℂ) * hb

/-! ### Quaternion algebras (Proposition 3.17) -/

/-- **The Weil index of the norm form of a quaternion algebra** `D = (a, b)_F`
(`QuaternionAlgebra F a 0 b`, `i² = a`, `j² = b`), with the reduced norm `N_D(x) = (x x̄)`
(GKT Proposition B.50): `γ(ψ ∘ N_D) = (a, b)_F`. -/
theorem weilIndex_quaternion (a b : Fˣ) [TopologicalSpace (QuaternionAlgebra F (a : F) 0 (b : F))]
    [IsModuleTopology F (QuaternionAlgebra F (a : F) 0 (b : F))] :
    weilIndex (fun x : QuaternionAlgebra F (a : F) 0 (b : F) => ψ.complex (x * star x).re) =
      ((hilbertSymbol F a b : ℤ) : ℂ) := by
  have := IsModuleTopology.isTopologicalAddGroup F (QuaternionAlgebra F (a : F) 0 (b : F))
  have : FiniteDimensional F (QuaternionAlgebra F (a : F) 0 (b : F)) :=
    Module.Finite.equiv (QuaternionAlgebra.linearEquivTuple (a : F) 0 (b : F)).symm
  have := locallyCompactSpace_of_finiteDimensional F (QuaternionAlgebra F (a : F) 0 (b : F))
  have := secondCountableTopology_of_finiteDimensional F (QuaternionAlgebra F (a : F) 0 (b : F))
  have := compactOpenExhaustion_of_finiteDimensional F (QuaternionAlgebra F (a : F) 0 (b : F))
  have := t2Space_of_finiteDimensional F (QuaternionAlgebra F (a : F) 0 (b : F))
  let c : Fin 4 → Fˣ := ![1, -a, -b, a * b]
  let T := linearEquivToContinuousAddEquiv (QuaternionAlgebra.linearEquivTuple (a : F) 0 (b : F))
  have h := weilIndex_comp_addEquiv (isCharacterOfSecondDegree_diagonal ψ c) T
  have e : (fun x : QuaternionAlgebra F (a : F) 0 (b : F) => ψ.complex (x * star x).re) =
      fun x => ψ.complex (∑ i, (c i : F) * T x i ^ 2) := by
    funext x
    rw [Fin.sum_univ_four, linearEquivToContinuousAddEquiv_apply,
      QuaternionAlgebra.coe_linearEquivTuple, QuaternionAlgebra.equivTuple_apply]
    simp [c, QuaternionAlgebra.re_mul]
    congr 2
    ring
  rw [e, h, weilIndex_diagonal, Fin.prod_univ_four, ← weilIndexOne_mul_four ψ a b]
  simp [c, UnitaryAdditiveCharacter.scale_one]

/-- **GKT Proposition 3.17**: for a quaternion algebra `D = (a, b)_F` which is a division algebra,
`γ(ψ ∘ N_D) = -1`. (Over a nonarchimedean local field there is one such `D` up to isomorphism,
GKT Proposition B.53, and isomorphic quaternion algebras have isometric norm forms; the statement
here is for each of them.) -/
theorem weilIndex_quaternion_of_isUnit (a b : Fˣ)
    [TopologicalSpace (QuaternionAlgebra F (a : F) 0 (b : F))]
    [IsModuleTopology F (QuaternionAlgebra F (a : F) 0 (b : F))]
    (hD : ∀ x : QuaternionAlgebra F (a : F) 0 (b : F), x ≠ 0 → IsUnit x) :
    weilIndex (fun x : QuaternionAlgebra F (a : F) 0 (b : F) => ψ.complex (x * star x).re) =
      -1 := by
  rw [weilIndex_quaternion]
  have hab : hilbertSymbol F a b = -1 := by
    refine (hilbertSymbol_eq_neg_one_iff a b).2 fun ⟨x, y, hxy⟩ => ?_
    let q : QuaternionAlgebra F (a : F) 0 (b : F) := ⟨x, y, 1, 0⟩
    have hq : q ≠ 0 := fun h0 => one_ne_zero (congrArg QuaternionAlgebra.imJ h0)
    have hN : q * star q = 0 := by
      rw [QuaternionAlgebra.mul_star_eq_coe]
      have : (q * star q).re = 0 := by
        simp only [q, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
          QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
        linear_combination hxy
      rw [this, QuaternionAlgebra.coe_zero]
    obtain ⟨u, hu⟩ := hD q hq
    have : star q = 0 := by
      have := congrArg (fun z => (↑u⁻¹ : QuaternionAlgebra F (a : F) 0 (b : F)) * z) hN
      simp [← hu, ← mul_assoc] at this
    exact hq (by simpa using congrArg star this)
  rw [hab]
  simp

/-! ### The normalized Weil index: Proposition 3.19, Corollaries 3.20, 3.22 -/

theorem normalizedWeilIndex_one : normalizedWeilIndex 1 ψ = 1 := by
  rw [normalizedWeilIndex, UnitaryAdditiveCharacter.scale_one, div_self (weilIndexOne_ne_zero ψ)]

/-- **GKT Proposition 3.19 (a)**: `γ(a b², ψ) = γ(a, ψ)`. -/
theorem normalizedWeilIndex_mul_sq (a b : Fˣ) :
    normalizedWeilIndex (a * b ^ 2) ψ = normalizedWeilIndex a ψ := by
  rw [normalizedWeilIndex, normalizedWeilIndex, weilIndexOne_scale_mul_sq]

/-- **GKT Proposition 3.19 (b)**: `γ(a b, ψ) = γ(a, ψ) γ(b, ψ) (a, b)_F`. -/
theorem normalizedWeilIndex_mul (a b : Fˣ) :
    normalizedWeilIndex (a * b) ψ =
      normalizedWeilIndex a ψ * normalizedWeilIndex b ψ * ((hilbertSymbol F a b : ℤ) : ℂ) := by
  have h := weilIndexOne_mul_four ψ a b
  rw [weilIndexOne_scale_neg, weilIndexOne_scale_neg] at h
  have hw := weilIndexOne_ne_zero ψ
  have ha := weilIndexOne_ne_zero (ψ.scale a)
  have hb := weilIndexOne_ne_zero (ψ.scale b)
  rw [normalizedWeilIndex, normalizedWeilIndex, normalizedWeilIndex, ← h]
  field_simp

/-- `γ(a, ψ)` has modulus one. -/
theorem norm_normalizedWeilIndex (a : Fˣ) : ‖normalizedWeilIndex a ψ‖ = 1 := by
  rw [normalizedWeilIndex, norm_div, norm_weilIndexOne, norm_weilIndexOne, div_one]

/-- **GKT Corollary 3.20 (a)**: `γ(a, ψ_b) = γ(a, ψ) (a, b)_F`. -/
theorem normalizedWeilIndex_scale (a b : Fˣ) :
    normalizedWeilIndex a (ψ.scale b) =
      normalizedWeilIndex a ψ * ((hilbertSymbol F a b : ℤ) : ℂ) := by
  have h := normalizedWeilIndex_mul ψ b a
  rw [hilbertSymbol_comm] at h
  have hw := weilIndexOne_ne_zero ψ
  have hb := weilIndexOne_ne_zero (ψ.scale b)
  simp only [normalizedWeilIndex, UnitaryAdditiveCharacter.scale_scale] at h ⊢
  rw [div_eq_iff hb]
  rw [div_eq_iff hw] at h
  rw [h]
  field_simp

/-- **GKT Corollary 3.20 (b)**: `γ(-1, ψ) = γ(ψ)⁻²`. -/
theorem normalizedWeilIndex_neg_one : normalizedWeilIndex (-1) ψ = (weilIndexOne ψ ^ 2)⁻¹ := by
  rw [normalizedWeilIndex, weilIndexOne_scale_neg, UnitaryAdditiveCharacter.scale_one]
  field_simp [weilIndexOne_ne_zero ψ]

/-- **GKT Corollary 3.20 (c)**: `γ(a, ψ)² = (a, -1)_F`. -/
theorem normalizedWeilIndex_sq (a : Fˣ) :
    normalizedWeilIndex a ψ ^ 2 = ((hilbertSymbol F a (-1) : ℤ) : ℂ) := by
  have h := normalizedWeilIndex_mul ψ a a
  have h1 : normalizedWeilIndex (a * a) ψ = 1 := by
    rw [← one_mul (a * a), ← sq, normalizedWeilIndex_mul_sq, normalizedWeilIndex_one]
  rw [h1, hilbertSymbol_self] at h
  have hsq : (((hilbertSymbol F a (-1) : ℤ) : ℂ)) ^ 2 = 1 := by
    rcases hilbertSymbol_eq_one_or a (-1) with h' | h' <;> simp [h']
  linear_combination (-((hilbertSymbol F a (-1) : ℤ) : ℂ)) * h - normalizedWeilIndex a ψ ^ 2 * hsq

/-- **GKT Corollary 3.20 (c)**: `γ(a, ψ)² = (a, a)_F`. -/
theorem normalizedWeilIndex_sq' (a : Fˣ) :
    normalizedWeilIndex a ψ ^ 2 = ((hilbertSymbol F a a : ℤ) : ℂ) := by
  rw [normalizedWeilIndex_sq, hilbertSymbol_self]

/-- **GKT Corollary 3.20 (c)**: `γ(a, ψ)⁻¹ = γ(a, ψ) (a, -1)_F = conj γ(a, ψ)`. -/
theorem inv_normalizedWeilIndex (a : Fˣ) :
    (normalizedWeilIndex a ψ)⁻¹ =
      normalizedWeilIndex a ψ * ((hilbertSymbol F a (-1) : ℤ) : ℂ) ∧
    (normalizedWeilIndex a ψ)⁻¹ = starRingEnd ℂ (normalizedWeilIndex a ψ) := by
  have h0 : normalizedWeilIndex a ψ ≠ 0 := by
    intro h; have := norm_normalizedWeilIndex ψ a; rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨?_, ?_⟩
  · have h2 := normalizedWeilIndex_sq ψ a
    have hsq : (((hilbertSymbol F a (-1) : ℤ) : ℂ)) ^ 2 = 1 := by
      rcases hilbertSymbol_eq_one_or a (-1) with h' | h' <;> simp [h']
    rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_of_mul_eq_one_left]
    linear_combination ((hilbertSymbol F a (-1) : ℤ) : ℂ) * h2 + hsq
  · refine eq_inv_of_mul_eq_one_left ?_ |>.symm
    rw [mul_comm, Complex.mul_conj', norm_normalizedWeilIndex]
    simp

/-- **GKT Corollary 3.20 (d)**: `γ(a, ψ)⁴ = 1`. -/
theorem normalizedWeilIndex_pow_four (a : Fˣ) : normalizedWeilIndex a ψ ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, normalizedWeilIndex_sq]
  rcases hilbertSymbol_eq_one_or a (-1) with h' | h' <;> simp [h']

/-- **GKT Corollary 3.20 (e)**: `γ(ψ)⁴ = (-1, -1)_F`. -/
theorem weilIndexOne_pow_four : weilIndexOne ψ ^ 4 = ((hilbertSymbol F (-1) (-1) : ℤ) : ℂ) := by
  have h := normalizedWeilIndex_sq ψ (-1)
  rw [normalizedWeilIndex_neg_one, inv_pow, ← pow_mul] at h
  have hsq : (((hilbertSymbol F (-1) (-1) : ℤ) : ℂ)) ^ 2 = 1 := by
    rcases hilbertSymbol_eq_one_or (F := F) (-1) (-1) with h' | h' <;> simp [h']
  have hw : weilIndexOne ψ ^ 4 ≠ 0 := pow_ne_zero _ (weilIndexOne_ne_zero ψ)
  have h4 : weilIndexOne ψ ^ (2 * 2) = weilIndexOne ψ ^ 4 := by norm_num
  rw [h4] at h
  have h' : ((hilbertSymbol F (-1) (-1) : ℤ) : ℂ) * weilIndexOne ψ ^ 4 = 1 := by
    rw [← h, inv_mul_cancel₀ hw]
  linear_combination ((hilbertSymbol F (-1) (-1) : ℤ) : ℂ) * h' - weilIndexOne ψ ^ 4 * hsq

/-- **GKT Corollary 3.20 (e)**: `γ(ψ_a)⁸ = 1`. -/
theorem weilIndexOne_pow_eight : weilIndexOne ψ ^ 8 = 1 := by
  rw [show 8 = 4 * 2 by rfl, pow_mul, weilIndexOne_pow_four]
  rcases hilbertSymbol_eq_one_or (F := F) (-1) (-1) with h' | h' <;> simp [h']

/-- `γ(a⁻¹, ψ) = γ(a, ψ)`. -/
theorem normalizedWeilIndex_inv (a : Fˣ) : normalizedWeilIndex a⁻¹ ψ = normalizedWeilIndex a ψ := by
  rw [← normalizedWeilIndex_mul_sq ψ a⁻¹ a]
  congr 1
  group

/-- **GKT Corollary 3.22** for `k ≥ 0`: `γ(a^k, ψ) = (a, a)_F^{k(k-1)/2} γ(a, ψ)^k`. -/
theorem normalizedWeilIndex_pow (a : Fˣ) (k : ℕ) :
    normalizedWeilIndex (a ^ k) ψ =
      ((hilbertSymbol F a a : ℤ) : ℂ) ^ k.choose 2 * normalizedWeilIndex a ψ ^ k := by
  induction k with
  | zero => simp [normalizedWeilIndex_one]
  | succ k ih =>
    have hc : (k + 1).choose 2 = k.choose 2 + k := by
      simp [Nat.choose_succ_succ, add_comm]
    rw [pow_succ, normalizedWeilIndex_mul, ih, hc, hilbertSymbol_comm (a ^ k) a, map_pow]
    push_cast
    ring

/-- **GKT Corollary 3.22** for `k ≤ 0`: `γ(a^{-k}, ψ) = (a, a)_F^{k(k-1)/2} γ(a, ψ)^k`, `k ≥ 0` (the
book's formula for `-k` differs from this one by `(a, a)^{2k} = 1`). -/
theorem normalizedWeilIndex_zpow_neg (a : Fˣ) (k : ℕ) :
    normalizedWeilIndex (a ^ (-(k : ℤ))) ψ =
      ((hilbertSymbol F a a : ℤ) : ℂ) ^ k.choose 2 * normalizedWeilIndex a ψ ^ k := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, normalizedWeilIndex_pow, normalizedWeilIndex_inv,
    hilbertSymbol_inv_left, hilbertSymbol_inv_right]

/-! ### Corollary 3.15 -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Over a field with `2` invertible, the polar form of `q` is non-degenerate exactly when the
associated symmetric form is. -/
theorem separatingLeft_associated_iff [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
    (q : QuadraticForm F V) :
    (QuadraticMap.associated (R := F) q).SeparatingLeft ↔
      (QuadraticMap.polarBilin q).SeparatingLeft := by
  have key : ∀ x y, QuadraticMap.polarBilin q x y = 2 * QuadraticMap.associated (R := F) q x y := by
    intro x y
    rw [← QuadraticMap.two_nsmul_associated (S := F) (Q := q), LinearMap.smul_apply,
      LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  constructor
  · intro h x hx
    exact h x fun y => by
      have := hx y
      rw [key, mul_eq_zero] at this
      exact this.resolve_left h2
  · intro h x hx
    exact h x fun y => by rw [key, hx y, mul_zero]

/-- **Reduction to dimension one** (GKT p. 82, Proposition 3.13 (a), (d)): a non-degenerate
quadratic form is isometric to a diagonal one `⟨a₁, …, aₙ⟩`, and `γ(ψ ∘ q) = ∏ γ(ψ_{aᵢ})`. -/
theorem exists_weilIndex_eq_prod {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] (q : QuadraticForm F V)
    (hq : (QuadraticMap.polarBilin q).SeparatingLeft) :
    ∃ a : Fin (Module.finrank F V) → Fˣ, weilIndex (fun x => ψ.complex (q x)) =
      ∏ i, weilIndexOne (ψ.scale (a i)) := by
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' q
    ((separatingLeft_associated_iff q).2 hq)
  refine ⟨w, ?_⟩
  rw [← weilIndex_quadraticForm_isometryEquiv ψ e.symm hq, ← weilIndex_diagonal]
  congr 1
  funext x
  rw [QuadraticMap.weightedSumSquares_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def, smul_eq_mul, sq]

/-- **GKT Corollary 3.15**: `γ(ψ ∘ q)⁸ = 1` for every non-degenerate quadratic form (here by the
reduction to dimension one and Corollary 3.20 (e), as in Remark 3.21, instead of the Witt group). -/
theorem weilIndex_pow_eight {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] (q : QuadraticForm F V)
    (hq : (QuadraticMap.polarBilin q).SeparatingLeft) :
    weilIndex (fun x => ψ.complex (q x)) ^ 8 = 1 := by
  obtain ⟨a, ha⟩ := exists_weilIndex_eq_prod ψ q hq
  rw [ha, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => weilIndexOne_pow_eight _

end Langlands.Theta
