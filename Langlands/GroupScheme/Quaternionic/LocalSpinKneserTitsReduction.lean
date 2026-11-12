import Langlands.LocalField.ValuativeInfinite
import Langlands.GroupScheme.Quaternionic.SpinEichlerLift
import Langlands.GroupScheme.Quaternionic.EichlerReducedNorm
import Langlands.GroupScheme.Quaternionic.WittIndexOneInputs
import Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsStatement

/-!
# Reduction of the quaternionic Kneser–Tits statement to two spin-cover inputs

`LocalSpinKneserTitsStatement` follows from two statements about the spin covers in its
setting:

* `SpinLeviReducedNormSquareStatement`: if a rational point of the spin cover lies over the
  Levi element `ℓ(a)` of a hyperbolic pair, then the reduced norm of `a` is a square in `K`;
* `SpinKernelElementaryStatement`: every rational point of the spin cover lying over the
  identity is in the parabolic elementary subgroup.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.CentralSimple
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

/-- **Spin input 1.** In the setting of `LocalSpinKneserTitsStatement`, for every spin cover
`π : S ⟶ O(q)`, every hyperbolic pair `(e, f)` of `q`, every rational point `s` of `S` and every
`a ∈ Dˣ`: if the matrix of `π(s)` is the Levi element `ℓ(a)` (`e ↦ a e`, `f ↦ σ(a)⁻¹ f`,
identity on `{e, f}^⊥`), then the reduced norm of `a` is a square in `K`. -/
def SpinLeviReducedNormSquareStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D],
    Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π →
      ∀ (e f : Fin m → D) (h : σ.IsHyperbolicPair q e f) (s : rationalPoints S) (a : Dˣ),
        FirstKindInvolution.Eichler.isometryRationalMatrix σ q (rationalPoints.map π s) =
            FirstKindInvolution.Eichler.levi σ q
              (FirstKindInvolution.Eichler.isHyperbolic_of_isHyperbolicPair h) a →
          ∃ t : K, reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = t ^ 2

/-- **Spin input 2.** In the setting of `LocalSpinKneserTitsStatement`, for every spin cover
`π : S ⟶ O(q)`, every rational point of `S` lying over the identity of `O(q)` is in the
parabolic elementary subgroup of `S`. -/
def SpinKernelElementaryStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D],
    Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π →
      ∀ s : rationalPoints S, rationalPoints.map π s = 1 →
        s ∈ parabolicElementarySubgroup S

open FirstKindInvolution.Eichler in
/-- **Reduction.** The two spin inputs imply `LocalSpinKneserTitsStatement`. -/
theorem localSpinKneserTits_of_spinInputs (h₁ : SpinLeviReducedNormSquareStatement.{u})
    (h₂ : SpinKernelElementaryStatement.{u}) : LocalSpinKneserTitsStatement.{u} := by
  intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ
  have : Infinite K := Langlands.LocalField.infinite_of_isNonarchimedeanLocalField K
  obtain ⟨e, f, h⟩ := σ.exists_hyperbolicPair_of_quadraticWittIndex_pos q hq (by omega)
  have hP := isHyperbolic_of_isHyperbolicPair h
  obtain ⟨a₀, ha₀, ha₀₀⟩ := exists_ne_zero_mem_alternatingSubspace σ hD hsym
  have hanis : ∀ y, σ.sesqForm (σ.polar q) y e = 0 → σ.sesqForm (σ.polar q) y f = 0 →
      σ.quadraticValue y q = 0 → y = 0 := fun y hye hyf hy =>
    eq_zero_of_ortho_of_quadraticWittIndex_le_one hP hw.le hye hyf hy
  obtain ⟨x₀, hx₀0, hx₀e, hx₀f⟩ := exists_ne_zero_ortho (σ := σ) (q := q) e f
    (by rw [Fintype.card_fin]; omega)
  have hx₀ : σ.quadraticValue x₀ q ≠ 0 := fun h0 => hx₀0 (hanis x₀ hx₀e hx₀f h0)
  refine parabolicElementarySubgroup_eq_top_of_levi_of_kernel h ha₀ ha₀₀ hanis hπ ?_
    (h₂ K D hD σ hsym m hm q hq hw S π hπ)
  intro s a hsa
  obtain ⟨t, ht⟩ := h₁ K D hD σ hsym m hm q hq hw S π hπ e f h s a hsa
  exact mem_eichlerLeviSubgroup_of_reducedNorm_eq_sq (reducedDegree_eq_two hD) hP ha₀ ha₀₀
    hx₀e hx₀f hx₀ a t ht

end Langlands.GroupScheme.Quaternionic
