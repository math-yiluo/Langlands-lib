import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.JacobsonNoether
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Data.Nat.Sqrt

/-!
# Central simple algebras over a separably closed field

Every finite-dimensional central simple algebra over a separably closed field
is a full matrix algebra over that field.
-/

noncomputable section

namespace Langlands.CentralSimple

universe uF uB

section DivisionAlgebra

variable (F : Type uF) (D : Type uB) [Field F] [IsSepClosed F] [DivisionRing D] [Algebra F D]

/-- Over a separably closed field, a separable element of a division algebra is a scalar. -/
theorem mem_bot_of_isSeparable_of_isSepClosed {x : D} (hx : IsSeparable F x) :
    x ∈ (⊥ : Subalgebra F D) := by
  have hdeg := IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hx.isIntegral) hx
  rw [Algebra.mem_bot]
  exact minpoly.mem_range_of_degree_eq_one F x hdeg

/-- A finite-dimensional central division algebra over a separably closed field has
no nonscalar elements. -/
theorem bot_eq_top_of_isSepClosed [FiniteDimensional F D] [Algebra.IsCentral F D] :
    (⊥ : Subalgebra F D) = ⊤ := by
  by_contra h
  have : Algebra.IsAlgebraic F D := Algebra.IsAlgebraic.of_finite F D
  obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' h
  exact hx (mem_bot_of_isSeparable_of_isSepClosed F D hsep)

/-- The structure map of a finite-dimensional central division algebra over a separably
closed field is bijective. -/
theorem algebraMap_bijective_of_isSepClosed [FiniteDimensional F D] [Algebra.IsCentral F D] :
    Function.Bijective (algebraMap F D) := by
  refine ⟨FaithfulSMul.algebraMap_injective F D, fun x => ?_⟩
  have hx : x ∈ (⊥ : Subalgebra F D) := (bot_eq_top_of_isSepClosed F D).symm ▸ Algebra.mem_top
  exact Algebra.mem_bot.mp hx

end DivisionAlgebra

/-- If a central algebra is isomorphic to a nonzero square matrix algebra over `D`,
then `D` is central. -/
theorem isCentral_of_algEquiv_matrix {F : Type uF} {B : Type uB} {D : Type uB} [Field F]
    [Ring B] [Algebra F B] [Ring D] [Algebra F D] [Algebra.IsCentral F B]
    {n : ℕ} [NeZero n] (e : B ≃ₐ[F] Matrix (Fin n) (Fin n) D) : Algebra.IsCentral F D where
  out := by
    intro z hz
    have hM : Algebra.IsCentral F (Matrix (Fin n) (Fin n) D) :=
      Algebra.IsCentral.of_algEquiv F B (Matrix (Fin n) (Fin n) D) e
    have hmem : Matrix.scalar (Fin n) z ∈ Subalgebra.center F (Matrix (Fin n) (Fin n) D) := by
      rw [Matrix.subalgebraCenter_eq_scalarAlgHom_map]
      exact ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (hM.out hmem)
    refine Algebra.mem_bot.mpr ⟨c, ?_⟩
    have h00 := congrFun (congrFun hc 0) 0
    simpa [Matrix.algebraMap_matrix_apply] using h00

/-- The dimension of an algebra isomorphic to `n × n` matrices is `n * n`. -/
theorem finrank_eq_mul_self_of_algEquiv_matrix {F : Type uF} {B : Type uB} [Field F] [Ring B]
    [Algebra F B] {n : ℕ} (e : B ≃ₐ[F] Matrix (Fin n) (Fin n) F) :
    Module.finrank F B = n * n := by
  rw [e.toLinearEquiv.finrank_eq]
  simp [Module.finrank_matrix]

section Splitting

variable (F : Type uF) (B : Type uB) [Field F] [IsSepClosed F] [Ring B] [Algebra F B]
  [FiniteDimensional F B] [Algebra.IsCentral F B] [IsSimpleRing B]

/-- A finite-dimensional central simple algebra over a separably closed field is a
nonzero full matrix algebra over that field. -/
theorem exists_algEquiv_matrix_of_isSepClosed :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (B ≃ₐ[F] Matrix (Fin n) (Fin n) F) := by
  have := IsArtinianRing.of_finite F B
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F B
  have : Algebra.IsCentral F D := isCentral_of_algEquiv_matrix e
  exact ⟨n, hn, ⟨e.trans <| .mapMatrix <| .symm <|
    .ofBijective (Algebra.ofId F D) (algebraMap_bijective_of_isSepClosed F D)⟩⟩

/-- Over a separably closed field the dimension of a central simple algebra is the square
of its natural square root. -/
theorem finrank_eq_sqrt_mul_sqrt_of_isSepClosed :
    Module.finrank F B = Nat.sqrt (Module.finrank F B) * Nat.sqrt (Module.finrank F B) := by
  obtain ⟨n, _, ⟨e⟩⟩ := exists_algEquiv_matrix_of_isSepClosed F B
  rw [finrank_eq_mul_self_of_algEquiv_matrix e, Nat.sqrt_eq]

omit [IsSepClosed F] [Algebra.IsCentral F B] in
/-- The natural square root of the dimension of a nonzero finite-dimensional algebra
is positive. -/
theorem sqrt_finrank_pos_of_isSepClosed : 0 < Nat.sqrt (Module.finrank F B) := by
  rw [Nat.sqrt_pos]
  exact Module.finrank_pos

/-- A chosen full matrix chart of a central simple algebra over a separably closed field,
of size the natural square root of the dimension. -/
def sepClosedChart :
    B ≃ₐ[F] Matrix (Fin (Nat.sqrt (Module.finrank F B)))
      (Fin (Nat.sqrt (Module.finrank F B))) F :=
  have h : ∃ (n : ℕ) (_ : NeZero n), Nonempty (B ≃ₐ[F] Matrix (Fin n) (Fin n) F) :=
    exists_algEquiv_matrix_of_isSepClosed F B
  let n := h.choose
  let e : B ≃ₐ[F] Matrix (Fin n) (Fin n) F := h.choose_spec.choose_spec.some
  have hn : n = Nat.sqrt (Module.finrank F B) := by
    rw [finrank_eq_mul_self_of_algEquiv_matrix e, Nat.sqrt_eq]
  e.trans (Matrix.reindexAlgEquiv F F (finCongr hn))

end Splitting

end Langlands.CentralSimple
