import Langlands.Representation.Parabolic.NormalizedCompatibilityStatement

/-!
# Scalar central action on normalized parabolic induction

A central element of the inducing subgroup that acts by a scalar on the
inducing representation acts by the same scalar on smooth induction: right
translation by it equals left translation, which is the covariance. For the
standard upper block parabolic of `GL_n`, the ambient scalar matrix `a I_n`
lies in the parabolic, its Levi projection is the diagonal scalar
`(a I_(n_i))_i`, and the positive half modulus is one there.
-/

namespace Langlands

universe uF uV uR uG

namespace Induction

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]

/-- A central element `z` of `G` lying in `P` and acting on `σ` by the scalar `c`
acts by `c` on smooth induction. -/
theorem smoothInduced_central_apply (P : Subgroup G) (σ : Representation R P V)
    (z : P) (hz : ∀ g : G, (z : G) * g = g * z) (c : R) (hc : ∀ v, σ z v = c • v)
    (f : SmoothFunctions P σ) :
    smoothInduced P σ z f = c • f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change f.1.1 (x * (z : G)) = c • f.1.1 x
  rw [← hz x]
  exact (f.1.2 z x).trans (hc _)

end Induction

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (R : Type*) [CommRing R]

/-- Coordinates in distinct blocks have distinct standard indices. -/
theorem index_ne_of_ne {i j : Fin B.length} (x : Fin (B.size i)) (y : Fin (B.size j))
    (hij : i ≠ j) : B.index i x ≠ B.index j y := by
  intro h
  have h' : B.indexEquiv ⟨i, x⟩ = B.indexEquiv ⟨j, y⟩ := h
  exact hij (congrArg Sigma.fst (B.indexEquiv.injective h'))

/-- The ambient scalar matrix `a I_n` is upper block triangular. -/
theorem scalar_mem_parabolic (a : Rˣ) :
    GeneralLinear.scalar (n := n) a ∈ B.parabolic R := by
  rw [B.mem_parabolic_iff]
  intro i j x y hji
  change Matrix.scalar (Fin n) (a : R) (B.index i x) (B.index j y) = 0
  rw [Matrix.scalar_apply]
  exact Matrix.diagonal_apply_ne _ (B.index_ne_of_ne x y hji.ne')

/-- The ambient scalar matrices as elements of the actual upper block parabolic. -/
def ambientScalar : Rˣ →* B.parabolic R :=
  GeneralLinear.scalar.codRestrict (B.parabolic R) (B.scalar_mem_parabolic R)

@[simp]
theorem coe_ambientScalar (a : Rˣ) :
    ((B.ambientScalar R a : B.parabolic R) : GeneralLinear n R) =
      GeneralLinear.scalar a := rfl

/-- The Levi projection of `a I_n` is the diagonal scalar `(a I_(n_i))_i`. -/
theorem leviProjection_ambientScalar (a : Rˣ) :
    B.leviProjection R (B.ambientScalar R a) =
      fun i => GeneralLinear.scalar (n := B.size i) a := by
  funext i
  apply Units.ext
  ext x y
  change Matrix.scalar (Fin n) (a : R) (B.index i x) (B.index i y) =
    Matrix.scalar (Fin (B.size i)) (a : R) x y
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The positive half modulus is one on the ambient scalar matrices. -/
theorem parabolicHalfModulus_ambientScalar (a : F.Carrierˣ) :
    T.parabolicHalfModulus B (B.ambientScalar F.Carrier a) = 1 := by
  rw [parabolicHalfModulus_apply, B.leviProjection_ambientScalar]
  exact (T.leviHalfModulus_eq_one B _).mpr (T.leviModulus_scalar B a)

end PadicField.TopologicalData

namespace Parabolic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The diagonal scalar action `ω` on the Levi representation is the action of the
ambient scalar matrices on its normalized parabolic induction. -/
theorem normalizedInductionCentralClause :
    NormalizedInductionCentralClause.{uF, uV} F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro σ ω hσ a f
  refine Induction.smoothInduced_central_apply (B.parabolic F.Carrier) _
    (B.ambientScalar F.Carrier a)
    (fun g => Matrix.GeneralLinearGroup.scalar_commute a g) (ω a : ℂ) ?_ f
  intro v
  change (T.parabolicHalfModulus B (B.ambientScalar F.Carrier a) : ℂ) •
      σ (B.leviProjection F.Carrier (B.ambientScalar F.Carrier a)) v = _
  rw [T.parabolicHalfModulus_ambientScalar, B.leviProjection_ambientScalar, Units.val_one,
    one_smul]
  exact hσ a v

end Parabolic

end Langlands
