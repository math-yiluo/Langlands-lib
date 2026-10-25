import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.ConjugateParabolic
import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-! Explicit inner transport of whole-Levi Langlands data. -/

noncomputable section

namespace Langlands

universe uR uG uV uF uW

section Generic

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Acting by `g` identifies inverse-inner pullback with the original action. -/
def innerPullbackEquiv (ρ : Representation R G V) (g : G) :
    Representation.Equiv (ρ.comp (MulAut.conj g).symm.toMonoidHom) ρ where
  toLinearMap := ρ g
  invFun := ρ g⁻¹
  left_inv v := by
    change (ρ g⁻¹ * ρ g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change (ρ g * ρ g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  isIntertwining' h := by
    change ρ g * ρ (g⁻¹ * h * g) = ρ h * ρ g
    rw [← map_mul, ← map_mul]
    congr 1
    group

@[simp] theorem innerPullbackEquiv_apply (ρ : Representation R G V) (g : G) (v : V) :
    innerPullbackEquiv ρ g v = ρ g v := rfl

/-- A character with commutative codomain is unchanged under inner pullback. -/
theorem character_comp_inner_symm (χ : G →* Rˣ) (g : G) :
    χ.comp (MulAut.conj g).symm.toMonoidHom = χ := by
  apply MonoidHom.ext
  intro h
  change χ (g⁻¹ * h * g) = χ h
  simp [mul_comm]

/-- Twisting by a character commutes with inverse-inner pullback. -/
theorem twist_comp_inner_symm (χ : G →* Rˣ) (ρ : Representation R G V) (g : G) :
    twist χ (ρ.comp (MulAut.conj g).symm.toMonoidHom) =
      (twist χ ρ).comp (MulAut.conj g).symm.toMonoidHom := by
  ext h v
  have hχ := DFunLike.congr_fun (character_comp_inner_symm χ g) h
  change (χ h : R) • ρ ((MulAut.conj g).symm h) v =
    (χ ((MulAut.conj g).symm h) : R) • ρ ((MulAut.conj g).symm h) v
  change χ ((MulAut.conj g).symm h) = χ h at hχ
  rw [hχ]

end Generic

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The actual continuous coordinate change furnished by an inner Levi element. -/
def innerLeviEquiv (m : B.Levi F.Carrier) :
    letI := T.topology
    B.Levi F.Carrier ≃ₜ* B.Levi F.Carrier := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  exact
    { toMulEquiv := MulAut.conj m
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }

@[simp] theorem innerLeviEquiv_apply (m x : B.Levi F.Carrier) :
    T.innerLeviEquiv B m x = m * x * m⁻¹ := rfl

@[simp] theorem innerLeviEquiv_symm_apply (m x : B.Levi F.Carrier) :
    letI := T.topology
    (T.innerLeviEquiv B m).symm x = m⁻¹ * x * m := rfl

/-- Inner coordinate transport does not change any real determinant character. -/
theorem leviRealPowerCharacter_comp_innerLeviEquiv (m : B.Levi F.Carrier)
    (t : Fin B.length → ℝ) :
    letI := T.topology
    (T.leviRealPowerCharacter B t).comp
      (T.innerLeviEquiv B m).toMulEquiv.symm.toMonoidHom =
        T.leviRealPowerCharacter B t :=
  letI := T.topology
  character_comp_inner_symm _ _

/-- Whole-Levi analytic temperedness is invariant under actual representation equivalence. -/
theorem isLeviTempered_iff_of_equiv
    {σ : Rep.{uV} ℂ (B.Levi F.Carrier)} {τ : Rep.{uW} ℂ (B.Levi F.Carrier)}
    (e : σ.ρ.Equiv τ.ρ) :
    RelativeRegularComparison.IsLeviTempered T B σ ↔
      RelativeRegularComparison.IsLeviTempered T B τ := by
  let := T.topology
  let := T.leviTopologicalGroup B
  constructor
  · intro h _ _ μ _
    exact isTemperedModCenter_of_equiv e μ (h μ)
  · intro h _ _ μ _
    exact isTemperedModCenter_of_equiv e.symm μ (h μ)

/-- Inner Levi coordinate transport preserves and reflects analytic temperedness. -/
theorem isLeviTempered_inner_iff (m : B.Levi F.Carrier)
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    RelativeRegularComparison.IsLeviTempered T B
      (Rep.of (σ.ρ.comp (T.innerLeviEquiv B m).toMulEquiv.symm.toMonoidHom)) ↔
        RelativeRegularComparison.IsLeviTempered T B σ :=
  letI := T.topology
  T.isLeviTempered_iff_of_equiv B (innerPullbackEquiv σ.ρ m)

/-- A matrix standardizer in the original Levi gives the exact ambient
embedding formula for the continuous inner coordinate equivalence. -/
theorem innerLeviEquiv_embedding_of_standardizer
    (P : Exponents.ConjugateBlockPair n F.Carrier) (y : GeneralLinear n F.Carrier)
    (m : P.shape.Levi F.Carrier)
    (h : y * P.conjugator = P.shape.leviEmbedding F.Carrier m)
    (x : P.shape.Levi F.Carrier) :
    letI := T.topology
    P.shape.leviEmbedding F.Carrier (T.innerLeviEquiv P.shape m x) =
      y * P.leviEmbedding x * y⁻¹ := by
  simp only [innerLeviEquiv_apply, map_mul, map_inv,
    Exponents.ConjugateBlockPair.leviEmbedding_apply]
  rw [← h]
  group

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The common real twist of inverse-inner pullback is equivalent to the original twist. -/
def innerLeviTwistEquiv (m : B.Levi F.Carrier) (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    Representation.Equiv (T.leviRealPowerTwist B t
      (σ.comp (T.innerLeviEquiv B m).toMulEquiv.symm.toMonoidHom))
        (T.leviRealPowerTwist B t σ) :=
  letI := T.topology
  twistEquiv (T.leviRealPowerCharacter B t) (innerPullbackEquiv σ m)

/-- Normalized induction transports the twisted inner equivalence by postcomposition. -/
def innerLeviInducedEquiv (m : B.Levi F.Carrier) (t : Fin B.length → ℝ)
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    (T.normalizedParabolicInduced B (T.leviRealPowerTwist B t
      (σ.comp (T.innerLeviEquiv B m).toMulEquiv.symm.toMonoidHom))).Equiv
        (T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ)) :=
  letI := T.topology
  T.normalizedParabolicInducedEquiv B (T.innerLeviTwistEquiv B m t σ)

end PadicField.TopologicalData
end Langlands
