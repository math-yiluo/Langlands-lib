import Langlands.GroupScheme.Multiplicative
import Langlands.AbelianScheme.Tate.PrimeAdic
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison
universe u
variable {S : Scheme.{u}} (T : Over S)

/-- The actual torsion sections of the multiplicative group are roots of unity. -/
def levelEquiv (n : ℕ) :
    Tate.Level (Gm S).toGrp T n ≃+ TateTwist.Level Γ(T.left, ⊤) n :=
  (mu.torsionPointsUnitsEquiv S n T).toAdditive

@[simp] theorem toUnit_levelEquiv (n : ℕ) (x : Tate.Level (Gm S).toGrp T n) :
    TateTwist.toUnit Γ(T.left, ⊤) n (levelEquiv T n x) =
      (Gm.pointsEquiv S T).toAdditive (Tate.toSection (Gm S).toGrp T n x) := rfl

/-- The comparison agrees with the published actual kernel-points interpretation. -/
theorem levelEquiv_kernelLevelEquiv (n : ℕ) (x : Additive (T ⟶ (mu S n).X)) :
    levelEquiv T n (Tate.kernelLevelEquiv (Gm S).toGrp T n x) =
      mu.pointsLevelEquiv n T x := rfl

/-- Both transitions are the same quotient-power map on the underlying unit. -/
theorem levelEquiv_transition {n m : ℕ} (h : n ∣ m)
    (x : Tate.Level (Gm S).toGrp T m) :
    levelEquiv T n (Tate.transition (Gm S).toGrp T h x) =
      TateTwist.transition Γ(T.left, ⊤) h (levelEquiv T m x) := by
  apply TateTwist.toUnit_injective
  exact map_pow (Gm.pointsEquiv S T) (Additive.toMul x).val (m / n)

/-- The torsion comparison is linear for the existing finite residue actions. -/
def levelLinearEquiv (n : ℕ) :
    Tate.Level (Gm S).toGrp T n ≃ₗ[ZMod n] TateTwist.Level Γ(T.left, ⊤) n :=
  { levelEquiv T n with
    map_smul' := fun a x => ZMod.map_smul (levelEquiv T n).toAddMonoidHom a x }

@[simp] theorem levelLinearEquiv_apply (n : ℕ) (x : Tate.Level (Gm S).toGrp T n) :
    levelLinearEquiv T n x = levelEquiv T n x := rfl

variable {T} {T' : Over S}

/-- Restricting actual torsion points induces the existing map on roots of unity. -/
theorem levelEquiv_restrict (a : T' ⟶ T) (n : ℕ)
    (x : Tate.Level (Gm S).toGrp T n) :
    levelEquiv T' n
        ((torsionPointsRestrict (Gm S).toGrp (n : ℤ) a).toAdditive x) =
      TateTwist.levelMap a.left.appTop.hom n (levelEquiv T n x) := by
  apply TateTwist.toUnit_injective
  exact Gm.pointsEquiv_naturality S a (Additive.toMul x).val

variable (T) (p : ℕ) [Fact p.Prime]

/-- The prime-power comparison preserves the existing p-adic residue action. -/
theorem levelEquiv_padic_smul (n : ℕ) (a : ℤ_[p])
    (x : Tate.Level (Gm S).toGrp T (p ^ n)) :
    levelEquiv T (p ^ n) (a • x) = a • levelEquiv T (p ^ n) x :=
  ZMod.map_smul (levelEquiv T (p ^ n)).toAddMonoidHom (PadicInt.toZModPow n a) x

/-- The actual prime-adic Tate module of Gm is the roots-of-unity Tate twist. -/
def primeIntegralEquiv :
    Tate.PrimeAdic.Integral (Gm S).toGrp T p ≃ₗ[ℤ_[p]]
      TateTwist.Integral Γ(T.left, ⊤) p where
  toFun x := ⟨fun n => levelEquiv T (p ^ n) (x.val n), by
    intro n
    rw [← levelEquiv_transition, x.property n]⟩
  invFun x := ⟨fun n => (levelEquiv T (p ^ n)).symm (x.val n), by
    intro n
    apply (levelEquiv T (p ^ n)).injective
    rw [levelEquiv_transition, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact x.property n⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (levelEquiv T (p ^ n)).symm_apply_apply (x.val n)
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (levelEquiv T (p ^ n)).apply_symm_apply (x.val n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (levelEquiv T (p ^ n)) (x.val n) (y.val n)
  map_smul' a x := by
    apply Subtype.ext
    funext n
    exact levelEquiv_padic_smul T p n a (x.val n)

@[simp] theorem evaluation_primeIntegralEquiv (n : ℕ)
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp T p) :
    TateTwist.evaluation Γ(T.left, ⊤) p n (primeIntegralEquiv T p x) =
      levelEquiv T (p ^ n) (Tate.PrimeAdic.evaluation (Gm S).toGrp T p n x) := rfl

@[simp] theorem evaluation_primeIntegralEquiv_symm (n : ℕ)
    (x : TateTwist.Integral Γ(T.left, ⊤) p) :
    Tate.PrimeAdic.evaluation (Gm S).toGrp T p n ((primeIntegralEquiv T p).symm x) =
      (levelEquiv T (p ^ n)).symm (TateTwist.evaluation Γ(T.left, ⊤) p n x) := rfl

theorem continuous_primeIntegralEquiv : Continuous (primeIntegralEquiv T p) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := levelEquiv T (p ^ n))).comp
    (Tate.PrimeAdic.continuous_evaluation (Gm S).toGrp T p n)

theorem continuous_primeIntegralEquiv_symm :
    Continuous (primeIntegralEquiv T p).symm := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_of_discreteTopology (f := (levelEquiv T (p ^ n)).symm)).comp
    (TateTwist.continuous_evaluation Γ(T.left, ⊤) p n)

/-- The prime-adic comparison with both existing inverse-limit topologies. -/
def primeIntegralContinuousLinearEquiv :
    Tate.PrimeAdic.Integral (Gm S).toGrp T p ≃L[ℤ_[p]]
      TateTwist.Integral Γ(T.left, ⊤) p :=
  { primeIntegralEquiv T p with
    continuous_toFun := continuous_primeIntegralEquiv T p
    continuous_invFun := continuous_primeIntegralEquiv_symm T p }

@[simp] theorem primeIntegralContinuousLinearEquiv_apply
    (x : Tate.PrimeAdic.Integral (Gm S).toGrp T p) :
    primeIntegralContinuousLinearEquiv T p x = primeIntegralEquiv T p x := rfl

end Langlands.GroupScheme.Gm.TateComparison
