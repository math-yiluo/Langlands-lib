import Langlands.Group.Unitary.Hyperbolic
import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Langlands.HarmonicAnalysis.LinearHaarScaling
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Langlands.Theta.Heisenberg.Schrodinger
import Langlands.HarmonicAnalysis.QuadraticExtensionTopology

/-!
# The symplectic space of the unitary dual pair

GKT §10.5 (Theorem 10.28, p. 288) and §12.4.1 (p. 369) in Case `3₊`: let `E / F` be a quadratic
extension of nonarchimedean local fields with conjugation `c`, `Q` a Hermitian `α × α` matrix over
`E` (the Hermitian space `V`) and `U(ν, ν)` the quasi-split unitary group of the hyperbolic
skew-Hermitian form `J` (`Langlands/Group/Unitary/Hyperbolic.lean`; the space `W`). The space
`𝕎 = M_{α×2ν}(E)` carries the `F`-symplectic form

`hermitianSymplecticForm c Q w w' = ½ tr_{E/F} hermitianTensor c Q J w w'`,

one half of the book's form `⟪,⟫ = tr_{E/F}(⟨,⟩ \overline{(,)})` of Theorem 10.28; `U(ν, ν)`
preserves it by right multiplication (`hermitianSymplecticForm_mul`). Splitting
`𝕎 = M_{α×ν}(E) × M_{α×ν}(E)` into the first and last `ν` columns polarizes it (the book's
`𝕎 = 𝕏^* ⊕ 𝕏` of §12.4.1): it is `polarizedForm (hermitianPairing c Q)`
(`hermitianSymplecticForm_fromCols`), where

`hermitianPairing c Q x y = ½ tr_{E/F} tr(Qᵀ x c(y)ᵀ)`.

The group `U(ν, ν)` acts on the Heisenberg group of `𝕎` by `g · (w, t) = (w g⁻¹, t)`
(`UnitaryGroup.heisenbergAction`), the action (2.1) of GKT p. 47 for the image of `U(ν, ν)` in
`Sp(𝕎)`.
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

section PublicDefs

variable {R : Type*} [CommRing R] {E : Type*} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The tensor product `∑ x_{ij} JA_{ik} JB_{jl} c(y_{kl})` of the sesquilinear forms with Gram
matrices `JA` and `JB` on `α × β` matrices. -/
def hermitianTensor (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) : E :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)

end PublicDefs

section PublicForm

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The symplectic form `½ tr_{E/F}` of the tensor product of the Hermitian form `Q` and the
hyperbolic skew-Hermitian form on `M_{α × 2ν}(E)`. -/
def hermitianSymplecticForm (Q : Matrix α α E) (w w' : Matrix α (ν ⊕ ν) E) : F :=
  2⁻¹ * Algebra.trace F E (hermitianTensor c Q (hyperbolicForm ν E) w w')

end PublicForm

namespace Unitary.Internal

section Pair

variable {R : Type*} [CommRing R] {E : Type*} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]


/-- `J` is Hermitian and invertible. -/
def IsHerm {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι E) : Prop :=
  (∀ i j, c (J j i) = J i j) ∧ IsUnit J.det

end Pair

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

omit [DecidableEq α] in
theorem hTens_eq (Q : Matrix α α E) (w w' : Matrix α (ν ⊕ ν) E) :
    hermitianTensor c Q (hyperbolicForm ν E) w w' = ∑ i, ∑ k,
        Q i k * (w * hyperbolicForm ν E * (w'.map c)ᵀ) i k := by
  simp only [hermitianTensor, mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq α] in

theorem form_mul (Q : Matrix α α E) (g : ofForm c (hyperbolicForm ν E)) (w w' : Matrix α
    (ν ⊕ ν) E) :
    hermitianSymplecticForm c Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (w' * ((g : GL
        (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) =
      hermitianSymplecticForm c Q w w' := by
  have h := (mem_ofForm_hyperbolicForm_iff c _).mp g.2
  rw [hermitianSymplecticForm, hermitianSymplecticForm, hTens_eq, hTens_eq, Matrix.map_mul (f := c),
      transpose_mul]
  conv_rhs => rw [← h]
  simp only [Matrix.mul_assoc]

omit [DecidableEq α] in
theorem form_add_left (Q : Matrix α α E) (w₁ w₂ w' : Matrix α (ν ⊕ ν) E) :
    hermitianSymplecticForm c Q
        (w₁ + w₂) w' = hermitianSymplecticForm c Q w₁ w' + hermitianSymplecticForm c Q w₂ w' := by
  simp only [hermitianSymplecticForm, hermitianTensor, Matrix.add_apply, add_mul,
      Finset.sum_add_distrib, map_add, mul_add]

omit [DecidableEq α] in
theorem form_add_right (Q : Matrix α α E) (w w₁ w₂ : Matrix α (ν ⊕ ν) E) :
    hermitianSymplecticForm c Q w
        (w₁ + w₂) = hermitianSymplecticForm c Q w w₁ + hermitianSymplecticForm c Q w w₂ := by
  simp only [hermitianSymplecticForm, hermitianTensor, Matrix.add_apply, Finset.sum_add_distrib,
      map_add, mul_add]

omit [DecidableEq α] in
theorem form_swap (hc : ∀ z, c (c z) = z) {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q)
    (w w' : Matrix α (ν ⊕ ν) E) :
    hermitianSymplecticForm c Q w' w = -hermitianSymplecticForm c Q w w' := by
  have hQ' : ∀ i j, c (Q j i) = Q i j := hQ
  have hJ : ∀ j l, c (hyperbolicForm ν E j l) = -hyperbolicForm ν E l j := by
    rintro (j | j) (l | l) <;> simp [hyperbolicForm_eq_fromBlocks, one_apply, eq_comm]
  have h : hermitianTensor c Q (hyperbolicForm ν E) w' w = -c (hermitianTensor c Q
      (hyperbolicForm ν E) w w') := by
    simp only [hermitianTensor, map_sum, map_mul, hc, hJ, hQ', ← Finset.sum_neg_distrib]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    exact Fintype.sum_equiv ⟨fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1), fun p => (p.2.2.1, p.2.2.2,
        p.1, p.2.1),
      fun _ => rfl, fun _ => rfl⟩ _ _ fun p => by simp only [Equiv.coe_fn_mk]; ring
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  rw [hermitianSymplecticForm, hermitianSymplecticForm, h, map_neg, ht, mul_neg]

omit [DecidableEq α] in

theorem form_left_left (Q : Matrix α α E) (x x' : Matrix α ν E) : hermitianSymplecticForm c Q
    (fromCols x 0) (fromCols x' 0) = 0 := by
  simp [hermitianSymplecticForm, hermitianTensor, hyperbolicForm_eq_fromBlocks,
      Fintype.sum_sum_type]

omit [DecidableEq α] in

theorem form_right_right (Q : Matrix α α E) (y y' : Matrix α ν E) : hermitianSymplecticForm c Q
    (fromCols 0 y) (fromCols 0 y') = 0 := by
  simp [hermitianSymplecticForm, hermitianTensor, hyperbolicForm_eq_fromBlocks,
      Fintype.sum_sum_type]

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

omit [DecidableEq α] in
theorem continuous_form_left (Q : Matrix α α E) (w' : Matrix α (ν ⊕ ν) E) :
    Continuous fun x : Matrix α ν E => hermitianSymplecticForm c Q (fromCols x 0) w' := by
  have h : ∀ e : E, Continuous fun z : E => Algebra.trace F E (z * e) := fun e =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.trace F E).comp (LinearMap.mulRight F e))
  simp only [hermitianSymplecticForm, hermitianTensor, map_sum, mul_assoc]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => (h _).comp ?_)
  rcases j with j | j
  · exact continuous_id.matrix_elem i j
  · exact continuous_const

end Local

section PrDef

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The matrix of an element of `U(ν, ν)`. -/
abbrev mat (g : ofForm c (hyperbolicForm ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E :=
  ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)

theorem mat_inv (g : ofForm c (hyperbolicForm ν E)) :
    mat c g⁻¹ = -(hyperbolicForm ν E * ((mat c g).map c)ᵀ * hyperbolicForm ν E) :=
  val_inv c g

theorem mem_sieg {g : ofForm c (hyperbolicForm ν E)} :
    g ∈ siegelParabolic c ν ↔ (mat c g).toBlocks₂₁ = 0 := Iff.rfl

def pr (Q : Matrix α α E) (x y : Matrix α ν E) : F := hermitianSymplecticForm c Q (fromCols x 0)
    (fromCols 0 y)

end PrDef

section PairAlg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

omit [DecidableEq α] in
theorem pr_eq_trace (Q : Matrix α α E) (x y : Matrix α ν E) :
    pr c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  have h : fromCols x (0 : Matrix α ν E) * hyperbolicForm ν E * ((fromCols
      (0 : Matrix α ν E) y).map c)ᵀ = x * (y.map c)ᵀ := by
    ext i k
    simp [hyperbolicForm_eq_fromBlocks, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [pr, hermitianSymplecticForm, hTens_eq, h]
  congr 2
  simp only [Matrix.trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

theorem trace_single_pair (Q : Matrix α α E) (y : Matrix α ν E) (i : α) (j : ν) (z : E) :
    Matrix.trace (Qᵀ * (Matrix.single i j z * (y.map c)ᵀ)) = z * (Q * y.map c) i j := by
  simp [Matrix.trace, mul_apply, Matrix.single_apply, Finset.mul_sum, ite_and]
  refine Finset.sum_congr rfl fun _ _ => by ring

def prLin (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  LinearMap.mk₂ F (fun x y => 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))))
    (fun x x' y => by simp [Matrix.add_mul, mul_add])
    (fun t x y => by simp [Matrix.smul_mul, mul_left_comm])
    (fun x y y' => by
      rw [show (y + y').map c = y.map c + y'.map c from Matrix.map_add _ (map_add c) _ _]
      simp [Matrix.mul_add, mul_add])
    (fun t x y => by
      rw [show (t • y).map c = t • y.map c from by ext i j; simp [map_smul]]
      simp [Matrix.mul_smul, mul_left_comm])

end PairAlg


theorem pr_alg : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
        [DecidableEq ν]
    (Q : Matrix α α E) (_ : IsHerm c Q), ∃ β : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F,
      (∀ x y, β x y = pr c Q x y) ∧ (∀ x y, β x y = β y x) ∧ (∀ y, (∀ x, β x y = 0) → y = 0) ∧
      (∀ (x y : Matrix α ν E) (a : Matrix ν ν E), β (x * a) y = β x (y * (a.map c)ᵀ)) ∧
      ∀ x y, β x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
  intro F _ _ E _ _ c δ hE α _ _ ν _ _ Q hQ
  have hc : ∀ z, c (c z) = z := hE.involutive
  have ht : ∀ z, Algebra.trace F E (c z) = Algebra.trace F E z := fun z =>
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom c c (AlgHom.ext hc) (AlgHom.ext hc)) z
  have hap : ∀ x y : Matrix α ν E,
      prLin c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
    fun _ _ => rfl
  refine ⟨prLin c Q, fun x y => by
      rw [hap, pr_eq_trace], fun x y => ?_, fun y hy => ?_, fun x y a => ?_, hap⟩
  ·
    have h : Matrix.trace (Qᵀ * (y * (x.map c)ᵀ)) = c (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) := by
      simp only [Matrix.trace, diag, mul_apply, transpose_apply, map_apply, map_sum, map_mul, hc,
          hQ.1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrArg _ (Finset.sum_congr rfl fun j _ => mul_comm _ _)
    rw [hap, hap, h, ht]
  ·
    obtain ⟨bE, -, -⟩ := hE.exists_basis
    have : Module.Finite F E := Module.Finite.of_basis bE
    have htr : Algebra.trace F E 1 ≠ 0 := by
      rw [← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hw : Q * y.map c = 0 := by
      ext i j
      by_contra hij
      apply htr
      have := hy (Matrix.single i j ((Q * y.map c) i j)⁻¹)
      rw [hap, trace_single_pair, inv_mul_cancel₀ hij] at this
      simpa using this
    have hy0 : y.map c = 0 := by
      have := congrArg (fun m => Q⁻¹ * m) hw
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ.2] using this
    ext i j
    exact c.toRingHom.injective (by simpa using congrFun (congrFun hy0 i) j)
  ·
    have h : ((y * (a.map c)ᵀ).map c)ᵀ = a * (y.map c)ᵀ := by
      ext i j
      simp [mul_apply, hc, mul_comm]
    rw [hap, hap, h, Matrix.mul_assoc]


end Unitary.Internal

open Unitary.Internal

/-! ### The Hermitian pairing and the Schrödinger model -/

section Pairing

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
variable {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The pairing `(x, y) ↦ ½ tr_{E/F} tr(Qᵀ x c(y)ᵀ)` of `M_{α×ν}(E)` with itself, which polarizes
`hermitianSymplecticForm c Q` on `M_{α×2ν}(E) = M_{α×ν}(E) × M_{α×ν}(E)`. -/
def hermitianPairing (Q : Matrix α α E) : Matrix α ν E →ₗ[F] Matrix α ν E →ₗ[F] F :=
  prLin c Q

omit [DecidableEq ν] in
theorem hermitianPairing_apply (Q : Matrix α α E) (x y : Matrix α ν E) :
    hermitianPairing c Q x y = 2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * (x * (y.map c)ᵀ))) :=
  rfl

theorem hermitianPairing_eq_hermitianSymplecticForm (Q : Matrix α α E) (x y : Matrix α ν E) :
    hermitianPairing c Q x y = hermitianSymplecticForm c Q (fromCols x 0) (fromCols 0 y) :=
  (pr_eq_trace c Q x y).symm

/-- The symplectic form on `M_{α×2ν}(E)` is the polarized form of the Hermitian pairing. -/
theorem hermitianSymplecticForm_fromCols (hc : Function.Involutive c) {Q : Matrix α α E}
    (hQ : Matrix.IsHermitianFor c Q) (x y x' y' : Matrix α ν E) :
    hermitianSymplecticForm c Q (fromCols x y) (fromCols x' y') =
      HeisenbergGroup.polarizedForm (hermitianPairing c Q) (x, y) (x', y') := by
  have e : ∀ u v : Matrix α ν E, fromCols u v = fromCols u 0 + fromCols 0 v := fun u v => by
    ext i (j | j) <;> simp
  rw [HeisenbergGroup.polarizedForm_apply, hermitianPairing_eq_hermitianSymplecticForm,
    hermitianPairing_eq_hermitianSymplecticForm, e x y, e x' y', form_add_left, form_add_right,
    form_add_right, form_left_left, form_right_right, form_swap c hc hQ (fromCols x' 0)]
  ring

omit [DecidableEq α] in
/-- The unitary group `U(ν, ν)` preserves the symplectic form on `M_{α×2ν}(E)` by right
multiplication. -/
theorem hermitianSymplecticForm_mul (Q : Matrix α α E) (g : ofForm c (hyperbolicForm ν E))
    (w w' : Matrix α (ν ⊕ ν) E) :
    hermitianSymplecticForm c Q (w * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E))
      (w' * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) = hermitianSymplecticForm c Q w w' :=
  form_mul c Q g w w'

omit [DecidableEq α] in
theorem _root_.Langlands.UnitaryGroup.val_inv_mul_val (g : ofForm c (hyperbolicForm ν E)) :
    (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) *
      ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
  rfl

omit [DecidableEq α] in
theorem _root_.Langlands.UnitaryGroup.val_mul_val_inv (g : ofForm c (hyperbolicForm ν E)) :
    ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) *
      (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1 := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

/-- The linear automorphism `(x, y) ↦ (x, y) g⁻¹` of `M_{α×ν}(E) × M_{α×ν}(E) = M_{α×2ν}(E)`. -/
def _root_.Langlands.UnitaryGroup.rightMulInvEquiv (g : ofForm c (hyperbolicForm ν E)) :
    (Matrix α ν E × Matrix α ν E) ≃ₗ[F] (Matrix α ν E × Matrix α ν E) where
  toFun w := ((fromCols w.1 w.2 *
      (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)).toCols₁,
    (fromCols w.1 w.2 *
      (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)).toCols₂)
  invFun w := ((fromCols w.1 w.2 * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)).toCols₁,
    (fromCols w.1 w.2 * ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)).toCols₂)
  map_add' w w' := by
    have h : fromCols (w + w').1 (w + w').2 = fromCols w.1 w.2 + fromCols w'.1 w'.2 := by
      ext i (j | j) <;> simp
    rw [h, Matrix.add_mul]
    refine Prod.ext ?_ ?_ <;> ext i j <;> simp
  map_smul' r w := by
    have h : fromCols (r • w).1 (r • w).2 = r • fromCols w.1 w.2 := by
      ext i (j | j) <;> simp
    rw [h, Matrix.smul_mul]
    refine Prod.ext ?_ ?_ <;> ext i j <;> simp
  left_inv w := by
    simp only [fromCols_toCols, Matrix.mul_assoc, UnitaryGroup.val_inv_mul_val, Matrix.mul_one,
      toCols₁_fromCols, toCols₂_fromCols]
  right_inv w := by
    simp only [fromCols_toCols, Matrix.mul_assoc, UnitaryGroup.val_mul_val_inv, Matrix.mul_one,
      toCols₁_fromCols, toCols₂_fromCols]

omit [Fintype α] [DecidableEq α] in
theorem _root_.Langlands.UnitaryGroup.rightMulInvEquiv_apply (g : ofForm c (hyperbolicForm ν E))
    (w : Matrix α ν E × Matrix α ν E) :
    UnitaryGroup.rightMulInvEquiv c g w =
      ((fromCols w.1 w.2 *
        (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν)
            (ν ⊕ ν) E)).toCols₁,
      (fromCols w.1 w.2 *
        (((g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν)
            (ν ⊕ ν) E)).toCols₂) :=
  rfl

theorem _root_.Langlands.UnitaryGroup.polarizedForm_rightMulInvEquiv (hc : Function.Involutive c)
    {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q) (g : ofForm c (hyperbolicForm ν E))
    (w w' : Matrix α ν E × Matrix α ν E) :
    HeisenbergGroup.polarizedForm (hermitianPairing c Q) (UnitaryGroup.rightMulInvEquiv c g w)
      (UnitaryGroup.rightMulInvEquiv c g w') =
      HeisenbergGroup.polarizedForm (hermitianPairing c Q) w w' := by
  rw [UnitaryGroup.rightMulInvEquiv_apply, UnitaryGroup.rightMulInvEquiv_apply,
    ← hermitianSymplecticForm_fromCols c hc hQ, ← hermitianSymplecticForm_fromCols c hc hQ,
    fromCols_toCols, fromCols_toCols, hermitianSymplecticForm_mul]

/-- The action of `U(ν, ν)` on the Heisenberg group of `M_{α×2ν}(E)`: `g` acts by right
multiplication by `g⁻¹` on `M_{α×2ν}(E)`, an isometry of the symplectic form, fixing the centre. -/
def _root_.Langlands.UnitaryGroup.heisenbergAction [Invertible (2 : F)]
    (hc : Function.Involutive c) {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q) :
    ofForm c (hyperbolicForm ν E) →*
      MulAut (HeisenbergGroup (HeisenbergGroup.polarizedForm (hermitianPairing (ν := ν) c Q))) where
  toFun g := HeisenbergGroup.mapEquiv (UnitaryGroup.rightMulInvEquiv c g)
    (UnitaryGroup.polarizedForm_rightMulInvEquiv c hc hQ g)
  map_one' := by
    refine MulEquiv.ext fun k => HeisenbergGroup.ext ?_ rfl
    simp [UnitaryGroup.rightMulInvEquiv_apply]
  map_mul' g h := by
    refine MulEquiv.ext fun k => HeisenbergGroup.ext ?_ rfl
    simp only [HeisenbergGroup.mapEquiv_apply, MulAut.mul_apply,
      UnitaryGroup.rightMulInvEquiv_apply, fromCols_toCols, _root_.mul_inv_rev, Subgroup.coe_mul,
      Units.val_mul, Matrix.mul_assoc]

theorem _root_.Langlands.UnitaryGroup.heisenbergAction_apply [Invertible (2 : F)]
    (hc : Function.Involutive c) {Q : Matrix α α E} (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E))
    (k : HeisenbergGroup (HeisenbergGroup.polarizedForm (hermitianPairing (ν := ν) c Q))) :
    UnitaryGroup.heisenbergAction c hc hQ g k = ⟨UnitaryGroup.rightMulInvEquiv c g k.vec, k.cen⟩ :=
  rfl

end Pairing

section Schrodinger

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]
      [IsModuleTopology F E]
  (c : E →ₐ[F] E) {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

omit [Invertible (2 : F)] in
theorem continuous_hermitianPairing_left (Q : Matrix α α E) (y : Matrix α ν E) :
    Continuous fun x : Matrix α ν E => hermitianPairing c Q x y := by
  simp only [hermitianPairing_eq_hermitianSymplecticForm]
  exact continuous_form_left c Q (fromCols 0 y)

end Schrodinger

end Langlands.Theta
