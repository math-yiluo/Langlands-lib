import Langlands.Correspondence.ArithmeticFactors
import Langlands.Weil.Representation.DualClasses
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

namespace Langlands.Correspondence

universe uF uV uW uG

private theorem eigenvector_zpow {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) {v : V} {z : ℂ}
    (hv : v ≠ 0) (he : ρ g v = z • v) :
    z ≠ 0 ∧ ∀ n : ℤ, ρ (g ^ n) v = z ^ n • v := by
  have hz : z ≠ 0 := by
    intro hz
    have h := congrArg (ρ g⁻¹) he
    simp only [hz, zero_smul, map_zero, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact hv h
  have hi : ρ g⁻¹ v = z⁻¹ • v := by
    apply (eq_inv_smul_iff₀ hz).mpr
    have h := congrArg (ρ g⁻¹) he
    simpa only [map_smul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply] using h.symm
  refine ⟨hz, fun n => ?_⟩
  induction n using Int.induction_on with
  | zero => simp
  | succ n hn =>
    rw [zpow_add_one, map_mul, Module.End.mul_apply, he, map_smul,
      hn, smul_smul, zpow_add_one₀ hz, mul_comm]
  | pred n hn =>
    rw [zpow_sub_one, map_mul, Module.End.mul_apply, hi, map_smul,
      hn, smul_smul, zpow_sub_one₀ hz, mul_comm]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An inertia-equivariant map from an irreducible Weil representation to a
smaller representation must be zero. No continuity hypothesis is needed. -/
theorem lowerRank_invariantHom_eq_bot
    (A : Weil.Local.LocalWeilRepresentation.{uF, uV} F)
    (B : Weil.Local.LocalWeilRepresentation.{uF, uW} F)
    (hA : A.IsIrreducible) (hdim : B.rank < A.rank) :
    FiniteRepresentation.invariantSubspace
      (FiniteRepresentation.of (Representation.linHom A.representation B.representation))
      (Weil.Local.localInertia F) = ⊥ := by
  classical
  let H := FiniteRepresentation.of (Representation.linHom A.representation B.representation)
  let T := FiniteRepresentation.invariants (Weil.Local.localInertia F) H
  by_contra hbot
  let : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hbot
  let Φ := Weil.Local.localGeometricFrobenius F
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (T.representation Φ)
  obtain ⟨f, hf⟩ := hz.exists_hasEigenvector
  obtain ⟨hz0, hpow⟩ := eigenvector_zpow T.representation Φ hf.2 hf.apply_eq_smul
  have hscalar (g : Weil.Local.localWeilGroup F) :
      H.representation g f.val = z ^ Weil.Local.localDegreeInt F g • f.val := by
    let d := Weil.Local.localDegreeInt F g
    have hd : Weil.Local.localDegree F (Φ ^ d) = Weil.Local.localDegree F g := by
      rw [map_zpow, Weil.Local.localGeometricFrobenius_degree]
      apply Multiplicative.toAdd.injective
      simp [d, Weil.Local.localDegreeInt]
    have hi : g / Φ ^ d ∈ Weil.Local.localInertia F := by
      change Weil.Local.localDegree F (g / Φ ^ d) = 1
      rw [map_div, hd, div_self']
    have heq : T.representation g f = z ^ d • f := by
      calc
        T.representation g f =
            T.representation (g / Φ ^ d) (T.representation (Φ ^ d) f) := by
          simp only [← Module.End.mul_apply, ← map_mul, div_mul_cancel]
        _ = T.representation (Φ ^ d) f :=
          Representation.isTrivial_apply
            (T.representation.comp (Weil.Local.localInertia F).subtype) ⟨_, hi⟩ _
        _ = z ^ d • f := hpow d
    exact congrArg Subtype.val heq
  let S : Subrepresentation A.representation :=
    { toSubmodule := f.val.ker
      apply_mem_toSubmodule := by
        intro g x hx
        change f.val x = 0 at hx
        change f.val (A.representation g x) = 0
        have heq := LinearMap.congr_fun (hscalar g) (A.representation g x)
        change B.representation g
            (f.val (A.representation g⁻¹ (A.representation g x))) =
          (z ^ Weil.Local.localDegreeInt F g) • f.val (A.representation g x) at heq
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply, hx, map_zero] at heq
        exact (smul_eq_zero.mp heq.symm).resolve_left (zpow_ne_zero _ hz0) }
  let : A.IsIrreducible := hA
  rcases eq_bot_or_eq_top S with hS | hS
  · have hinj : Function.Injective f.val := by
      apply LinearMap.ker_eq_bot.mp
      exact congrArg Subrepresentation.toSubmodule hS
    exact (Nat.not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective hinj)
  · apply hf.2
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    have hx : x ∈ S := by rw [hS]; trivial
    exact hx

/-- The inertia-fixed tensor space vanishes when the first factor is
irreducible and the second has smaller rank. -/
theorem lowerRank_invariantTensor_eq_bot
    (A : Weil.Local.LocalWeilRepresentation.{uF, uV} F)
    (B : Weil.Local.LocalWeilRepresentation.{uF, uW} F)
    (hA : A.IsIrreducible) (hdim : B.rank < A.rank) :
    FiniteRepresentation.invariantSubspace (FiniteRepresentation.tensor A B)
      (Weil.Local.localInertia F) = ⊥ := by
  let A' := FiniteRepresentation.dual A
  let H := FiniteRepresentation.of (Representation.linHom A'.representation B.representation)
  let e : FiniteRepresentation.Equiv (FiniteRepresentation.tensor A B) H :=
    (FiniteRepresentation.tensorEquiv (FiniteRepresentation.dualDualEquiv A)
      (Representation.Equiv.refl B.representation)).trans
        (Representation.Equiv.dualTensorHom A'.representation B.representation)
  have hH : FiniteRepresentation.invariantSubspace H (Weil.Local.localInertia F) = ⊥ :=
    lowerRank_invariantHom_eq_bot F A' B
      ((FiniteRepresentation.isIrreducible_dual_iff A).mpr hA)
      (by simpa only [A', FiniteRepresentation.rank_dual] using hdim)
  apply le_antisymm ?_ bot_le
  intro x hx
  have hxH : e x ∈ FiniteRepresentation.invariantSubspace H (Weil.Local.localInertia F) := by
    intro i
    change H.representation (i : _) (e x) = e x
    exact (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
      (i : _) x).symm.trans (congrArg e (hx i))
  rw [hH] at hxH
  change x = 0
  apply e.toLinearEquiv.injective
  simpa using hxH

/-- A pair with no inertia-fixed vectors has Euler polynomial one, even
before imposing the monodromy-kernel condition. -/
theorem eulerPolynomial_eq_one_of_invariantSubspace_eq_bot
    (A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uV} F)
    (hA : FiniteRepresentation.invariantSubspace A.toFiniteRepresentation
      (Weil.Local.localInertia F) = ⊥)
    (g : Weil.Local.localWeilGroup F) :
    LocalFactor.WeilDeligne.eulerPolynomial A (Weil.Local.localInertia F) g = 1 := by
  have hzero (x : A.inertiaKernelRepresentation (Weil.Local.localInertia F)) : x = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val = 0
    have hx : x.val.val ∈ FiniteRepresentation.invariantSubspace A.toFiniteRepresentation
        (Weil.Local.localInertia F) := by
      intro i
      exact congrArg Subtype.val (x.property i)
    simpa only [hA, Submodule.mem_bot] using hx
  let : Subsingleton (A.inertiaKernelRepresentation (Weil.Local.localInertia F)) :=
    ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  unfold LocalFactor.WeilDeligne.eulerPolynomial LocalFactor.eulerPolynomial
  rw [Subsingleton.elim (LocalFactor.WeilDeligne.kernelOperator A
    (Weil.Local.localInertia F) g) 0]
  rw [LinearMap.charpoly_zero, Module.finrank_zero_of_subsingleton, pow_zero]
  simpa only [Polynomial.C_1] using Polynomial.reverse_C (1 : ℂ)

/-- The pair L-factor with an irreducible first Weil action is one against
every smaller second factor. No parameter or monodromy restriction is needed. -/
theorem lowerRank_pairLFactor_eq_one
    (A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uV} F)
    (B : Weil.Local.LocalWeilDeligneRepresentation.{uF, uW} F)
    (hA : A.toFiniteRepresentation.IsIrreducible)
    (hdim : B.toFiniteRepresentation.rank < A.toFiniteRepresentation.rank) :
    LocalFactor.WeilDeligne.pairLFactor A B (Weil.Local.localInertia F)
      (Weil.Local.localGeometricFrobenius F) = 1 := by
  have hinv := lowerRank_invariantTensor_eq_bot F
    A.toFiniteRepresentation B.toFiniteRepresentation hA hdim
  have hpoly := eulerPolynomial_eq_one_of_invariantSubspace_eq_bot F
    (WeilDeligneRepresentation.tensor A B) hinv (Weil.Local.localGeometricFrobenius F)
  change (algebraMap (Polynomial ℂ) (RatFunc ℂ)
    (LocalFactor.WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.tensor A B)
      (Weil.Local.localInertia F) (Weil.Local.localGeometricFrobenius F)))⁻¹ = 1
  rw [hpoly, map_one, inv_one]

/-- Lower-rank continuous irreducible Weil classes have trivial arithmetic
pair L-factor after equipping both with zero monodromy. -/
theorem arithmeticPairLFactor_weilPairClass_eq_one {n m : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uV} F n)
    (τ : IrreducibleWeilClass.{uF, uV} F m) (hmn : m < n) :
    arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) = 1 := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep σ.val
  obtain ⟨B, hB⟩ := Quotient.exists_rep τ.val
  have hcA : FiniteRepresentation.classOf A.val = weilClassForget F σ :=
    congrArg (FiniteRepresentation.forgetPropertyClass _) hA
  have hcB : FiniteRepresentation.classOf B.val = weilClassForget F τ :=
    congrArg (FiniteRepresentation.forgetPropertyClass _) hB
  have hdimA : A.val.rank = n :=
    (congrArg FiniteRepresentation.classRank hcA).trans σ.property
  have hdimB : B.val.rank = m :=
    (congrArg FiniteRepresentation.classRank hcB).trans τ.property
  unfold arithmeticPairLFactor weilPairClass
  rw [← hcA, ← hcB]
  apply lowerRank_pairLFactor_eq_one F _ _ A.property.2
  change B.val.rank < A.val.rank
  rw [hdimA, hdimB]
  exact hmn

/-- The zero-monodromy Weil pair of `σ` has trivial arithmetic L-factor
against every continuous irreducible Weil class of smaller positive rank. -/
def HasTrivialLowerRankWeilPairLFactors {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uV} F n) : Prop :=
  ∀ (m : ℕ+) (τ : IrreducibleWeilClass.{uF, uV} F m), m < n →
    arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) = 1

/-- Every continuous irreducible Weil class has trivial lower-rank
arithmetic pair L-factors. -/
theorem hasTrivialLowerRankWeilPairLFactors {n : ℕ+}
    (σ : IrreducibleWeilClass.{uF, uV} F n) :
    HasTrivialLowerRankWeilPairLFactors F σ := by
  intro m τ hmn
  exact arithmeticPairLFactor_weilPairClass_eq_one F σ τ hmn

end Langlands.Correspondence
