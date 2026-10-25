import Langlands.Representation.Induction.InnerLeviTransport
import Langlands.Representation.Exponents.PairConjugation
import Langlands.Group.GL.DiagonalLevi

/-! Removing a target-Levi factor from a supplied ambient representative. -/
noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV uW
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} {A B : GeneralLinear.BlockShape n}

/-- Remove the inner coordinate action of a factor in the target Levi. -/
def removeTargetLeviFactor
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) :
    letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier :=
  letI := T.topology
  e.trans (T.innerLeviEquiv B m⁻¹)

@[simp] theorem removeTargetLeviFactor_apply
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (x : A.Levi F.Carrier) :
    T.removeTargetLeviFactor e m x = m⁻¹ * e x * m := by
  simp [removeTargetLeviFactor]

/-- The new coordinate equivalence implements the representative with its left Levi factor removed. -/
theorem removeTargetLeviFactor_embedding
    (P : Exponents.ConjugateBlockPair n F.Carrier)
    (e : letI := T.topology; P.shape.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (z y : GeneralLinear n F.Carrier)
    (hz : z = B.leviEmbedding F.Carrier m * y)
    (he : ∀ x, B.leviEmbedding F.Carrier (e x) = z * P.leviEmbedding x * z⁻¹)
    (x : P.shape.Levi F.Carrier) :
    B.leviEmbedding F.Carrier (T.removeTargetLeviFactor e m x) =
      y * P.leviEmbedding x * y⁻¹ := by
  rw [removeTargetLeviFactor_apply, map_mul, map_mul, map_inv, he, hz]
  group

/-- Removing a target-Levi factor preserves an already established real-character identity. -/
theorem removeTargetLeviFactor_character
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (t : Fin A.length → ℝ) (u : Fin B.length → ℝ)
    (h : letI := T.topology; (T.leviRealPowerCharacter A t).comp
      e.toMulEquiv.symm.toMonoidHom = T.leviRealPowerCharacter B u) :
    letI := T.topology
    (T.leviRealPowerCharacter A t).comp
      (T.removeTargetLeviFactor e m).toMulEquiv.symm.toMonoidHom =
        T.leviRealPowerCharacter B u := by
  let := T.topology
  change ((T.leviRealPowerCharacter A t).comp e.toMulEquiv.symm.toMonoidHom).comp
    (T.innerLeviEquiv B m⁻¹).toMulEquiv.symm.toMonoidHom = _
  rw [h]
  exact T.leviRealPowerCharacter_comp_innerLeviEquiv B m⁻¹ u

/-- Inverse pullback for the adjusted coordinates is equivalent to the old pullback. -/
def removeTargetLeviFactorPullbackEquiv
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (σ : Rep.{uV} ℂ (A.Levi F.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (σ.ρ.comp (T.removeTargetLeviFactor e m).toMulEquiv.symm.toMonoidHom)
      (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom) :=
  letI := T.topology
  innerPullbackEquiv (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom) m⁻¹

/-- Any equivalence with the untwisted target representation survives the adjustment. -/
def removeTargetLeviFactorRepresentationEquiv
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (σ : Rep.{uV} ℂ (A.Levi F.Carrier))
    (τ : Rep.{uW} ℂ (B.Levi F.Carrier))
    (h : letI := T.topology; Representation.Equiv
      (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom) τ.ρ) :
    letI := T.topology
    Representation.Equiv
      (σ.ρ.comp (T.removeTargetLeviFactor e m).toMulEquiv.symm.toMonoidHom) τ.ρ :=
  letI := T.topology
  (T.removeTargetLeviFactorPullbackEquiv e m σ).trans h

/-- Analytic temperedness of the transported representation is unchanged. -/
theorem removeTargetLeviFactor_tempered_iff
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (σ : Rep.{uV} ℂ (A.Levi F.Carrier)) :
    letI := T.topology
    RelativeRegularComparison.IsLeviTempered T B
      (Rep.of (σ.ρ.comp (T.removeTargetLeviFactor e m).toMulEquiv.symm.toMonoidHom)) ↔
    RelativeRegularComparison.IsLeviTempered T B
      (Rep.of (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom)) :=
  letI := T.topology
  T.isLeviTempered_iff_of_equiv B (T.removeTargetLeviFactorPullbackEquiv e m σ)

/-- The same real twist and actual normalized induction preserve the adjusted pullback equivalence. -/
def removeTargetLeviFactorInducedEquiv
    (e : letI := T.topology; A.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (m : B.Levi F.Carrier) (u : Fin B.length → ℝ)
    (σ : Rep.{uV} ℂ (A.Levi F.Carrier)) :
    letI := T.topology
    (T.normalizedParabolicInduced B (T.leviRealPowerTwist B u
      (σ.ρ.comp (T.removeTargetLeviFactor e m).toMulEquiv.symm.toMonoidHom))).Equiv
    (T.normalizedParabolicInduced B (T.leviRealPowerTwist B u
      (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom))) :=
  letI := T.topology
  T.innerLeviInducedEquiv B m⁻¹ u (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom)

private theorem map_conj_remove_left {G : Type*} [Group G]
    (H K : Subgroup G) (d y : G)
    (hd : K.map (MulAut.conj d⁻¹).toMonoidHom = K)
    (h : H.map (MulAut.conj (d * y)).toMonoidHom = K) :
    H.map (MulAut.conj y).toMonoidHom = K := by
  have hc : (MulAut.conj d⁻¹).toMonoidHom.comp
      (MulAut.conj (d * y)).toMonoidHom = (MulAut.conj y).toMonoidHom := by
    ext x
    change d⁻¹ * ((d * y) * x * (d * y)⁻¹) * (d⁻¹)⁻¹ = y * x * y⁻¹
    group
  rw [← hd, ← h, Subgroup.map_map, hc]

/-- Parabolic equality survives removing a left factor from the target Levi. -/
theorem parabolic_map_conj_removeLeviFactor
    (P : Exponents.ConjugateBlockPair n F.Carrier)
    (m : B.Levi F.Carrier) (y : GeneralLinear n F.Carrier)
    (h : P.parabolic.map (MulAut.conj (B.leviEmbedding F.Carrier m * y)).toMonoidHom =
      B.parabolic F.Carrier) :
    P.parabolic.map (MulAut.conj y).toMonoidHom = B.parabolic F.Carrier := by
  apply map_conj_remove_left _ _ _ _ _ h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((B.parabolic F.Carrier).le_normalizer
      ((B.parabolic F.Carrier).inv_mem (B.leviInParabolic F.Carrier m).property))

/-- Split-component equality survives removing a left factor from the target Levi. -/
theorem splitComponent_map_conj_removeLeviFactor
    (P : Exponents.ConjugateBlockPair n F.Carrier)
    (m : B.Levi F.Carrier) (y : GeneralLinear n F.Carrier)
    (h : P.splitComponent.map
      (MulAut.conj (B.leviEmbedding F.Carrier m * y)).toMonoidHom =
        (Exponents.ConjugateBlockPair.standard (R := F.Carrier) B).splitComponent) :
    P.splitComponent.map (MulAut.conj y).toMonoidHom =
      (Exponents.ConjugateBlockPair.standard (R := F.Carrier) B).splitComponent := by
  apply map_conj_remove_left _ _ _ _ _ h
  exact Exponents.ConjugateBlockPair.splitComponent_map_conj_of_standardizer
    (Exponents.ConjugateBlockPair.standard (R := F.Carrier) B) _ m⁻¹ (by
      change (B.leviEmbedding F.Carrier m)⁻¹ * 1 = B.leviEmbedding F.Carrier m⁻¹
      rw [map_inv, mul_one])

/-- Embedded-Levi equality survives removing a left factor from the target Levi. -/
theorem leviSubgroup_map_conj_removeLeviFactor
    (P : Exponents.ConjugateBlockPair n F.Carrier)
    (m : B.Levi F.Carrier) (y : GeneralLinear n F.Carrier)
    (h : P.leviSubgroup.map (MulAut.conj (B.leviEmbedding F.Carrier m * y)).toMonoidHom =
      B.leviSubgroup F.Carrier) :
    P.leviSubgroup.map (MulAut.conj y).toMonoidHom = B.leviSubgroup F.Carrier := by
  apply map_conj_remove_left _ _ _ _ _ h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((B.leviSubgroup F.Carrier).le_normalizer
      ((B.leviSubgroup F.Carrier).inv_mem ⟨m, rfl⟩))

/-- For a supplied diagonal-times-permutation factorization, the adjusted coordinates
implement that exact permutation representative. -/
theorem removeDiagonalFactor_embedding
    (P : Exponents.ConjugateBlockPair n F.Carrier)
    (e : letI := T.topology; P.shape.Levi F.Carrier ≃ₜ* B.Levi F.Carrier)
    (a : Fin n → F.Carrierˣ) (w : Equiv.Perm (Fin n)) (z : GeneralLinear n F.Carrier)
    (hz : z = (GeneralLinear.BlockShape.singletons n).blockScalar F.Carrier a *
      GeneralLinear.permutation n F.Carrier w)
    (he : ∀ x, B.leviEmbedding F.Carrier (e x) = z * P.leviEmbedding x * z⁻¹)
    (x : P.shape.Levi F.Carrier) :
    B.leviEmbedding F.Carrier
      (T.removeTargetLeviFactor e (B.diagonalLevi F.Carrier a) x) =
        GeneralLinear.permutation n F.Carrier w * P.leviEmbedding x *
          (GeneralLinear.permutation n F.Carrier w)⁻¹ := by
  apply T.removeTargetLeviFactor_embedding P e _ z _ _ he x
  rw [B.leviEmbedding_diagonalLevi F.Carrier a]
  exact hz

end Langlands.PadicField.TopologicalData
