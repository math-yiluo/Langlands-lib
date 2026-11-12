import Langlands.Group.GL.SemistandardStandardizationProof
import Langlands.Representation.Induction.RepresentativeReplacement

/-! Diagonal normalizer factorization and replacement by pure permutations. -/

noncomputable section

namespace Langlands.GeneralLinear.BlockShape

universe uR

variable {n : ℕ} (R : Type uR)

section Ring

variable [CommRing R]

/-- Extract the unit in each one-dimensional Levi block by its determinant. -/
def singletonLeviUnits (m : (singletons n).Levi R) : Fin n → Rˣ :=
  fun i => GeneralLinear.determinant (m i)

@[simp] theorem singletonLevi_singletonLeviUnits (m : (singletons n).Levi R) :
    singletonLevi R (singletonLeviUnits R m) = m := by
  funext i
  apply Units.ext
  ext r s
  have hr : r = 0 := Subsingleton.elim _ _
  have hs : s = 0 := Subsingleton.elim _ _
  subst r
  subst s
  simp [singletonLevi, singletonLeviUnits, GeneralLinear.scalar,
    GeneralLinear.determinant, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.val_det_apply]

end Ring

variable [Field R] [CharZero R]

/-- Every normalizer element of the actual coordinate diagonal torus is a
diagonal matrix times a permutation matrix. -/
theorem exists_diagonal_mul_permutation_of_mem_normalizer
    (z : GeneralLinear n R)
    (hz : z ∈ Subgroup.normalizer
      ((Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).splitComponent :
        Set (GeneralLinear n R))) :
    ∃ (a : Fin n → Rˣ) (w : Equiv.Perm (Fin n)),
      z = (singletons n).blockScalar R a * GeneralLinear.permutation n R w := by
  let P := (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).conjugateBy z
  have hP : P.splitComponent ≤
      (Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).splitComponent := by
    change ((Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).conjugateBy z).splitComponent ≤ _
    rw [Exponents.ConjugateBlockPair.conjugateBy_splitComponent]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hz).le
  obtain ⟨w, m, hm⟩ := P.exists_permutation_standardizer hP
  change (singletons n).Levi R at m
  change GeneralLinear.permutation n R w * (z * 1) =
    (singletons n).leviEmbedding R m at hm
  rw [mul_one] at hm
  let a₀ := singletonLeviUnits R m
  have hm' : GeneralLinear.permutation n R w * z = (singletons n).blockScalar R a₀ := by
    rw [hm]
    change (singletons n).leviEmbedding R m =
      (singletons n).leviEmbedding R (singletonLevi R (singletonLeviUnits R m))
    rw [singletonLevi_singletonLeviUnits]
  refine ⟨fun i => a₀ (w i), w⁻¹, ?_⟩
  calc
    z = (GeneralLinear.permutation n R w)⁻¹ * (singletons n).blockScalar R a₀ := by
      rw [← hm']
      group
    _ = ((GeneralLinear.permutation n R w)⁻¹ * (singletons n).blockScalar R a₀ *
        GeneralLinear.permutation n R w) * (GeneralLinear.permutation n R w)⁻¹ := by
      group
    _ = (singletons n).blockScalar R (fun i => a₀ (w i)) *
        GeneralLinear.permutation n R w⁻¹ := by
      have hc := permutation_conj_singletons_blockScalar R w⁻¹ a₀
      simp only [inv_inv, ← GeneralLinear.permutation_inv] at hc
      rw [hc, GeneralLinear.permutation_inv]

/-- Chosen diagonal and permutation coordinates of an actual torus normalizer
element, together with their exact ambient factorization. -/
def diagonalPermutationOfNormalizer
    (z : GeneralLinear n R)
    (hz : z ∈ Subgroup.normalizer
      ((Exponents.ConjugateBlockPair.standard (R := R) (singletons n)).splitComponent :
        Set (GeneralLinear n R))) :
    { aw : (Fin n → Rˣ) × Equiv.Perm (Fin n) //
      z = (singletons n).blockScalar R aw.1 * GeneralLinear.permutation n R aw.2 } :=
  let h := exists_diagonal_mul_permutation_of_mem_normalizer R z hz
  ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Exponents

universe uF uV uW

/-- An arbitrary diagonal-torus normalizer representative implementing the
recovered datum can be replaced by an actual permutation matrix. -/
theorem exists_permutation_transport_of_normalizer
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (P : ConjugateBlockPair n F.Carrier) (B : BlockShape n) :
    letI := T.topology
    ∀ (σ : Rep.{uV} ℂ (P.shape.Levi F.Carrier))
      (τ : Rep.{uW} ℂ (B.Levi F.Carrier))
      (t : Fin P.shape.length → ℝ) (u : Fin B.length → ℝ)
      (z : GeneralLinear n F.Carrier),
      z ∈ Subgroup.normalizer
        ((ConjugateBlockPair.standard (R := F.Carrier) (BlockShape.singletons n)).splitComponent :
          Set (GeneralLinear n F.Carrier)) →
      ∀ (e : P.shape.Levi F.Carrier ≃ₜ* B.Levi F.Carrier),
        P.parabolic.map (MulAut.conj z).toMonoidHom = B.parabolic F.Carrier →
        P.splitComponent.map (MulAut.conj z).toMonoidHom =
          (ConjugateBlockPair.standard (R := F.Carrier) B).splitComponent →
        P.leviSubgroup.map (MulAut.conj z).toMonoidHom = B.leviSubgroup F.Carrier →
        (∀ x, B.leviEmbedding F.Carrier (e x) = z * P.leviEmbedding x * z⁻¹) →
        (T.leviRealPowerCharacter P.shape t).comp e.toMulEquiv.symm.toMonoidHom =
          T.leviRealPowerCharacter B u →
        Nonempty (Representation.Equiv
          (σ.ρ.comp e.toMulEquiv.symm.toMonoidHom) τ.ρ) →
        ∃ (w : Equiv.Perm (Fin n))
          (e' : P.shape.Levi F.Carrier ≃ₜ* B.Levi F.Carrier),
          let y := GeneralLinear.permutation n F.Carrier w
          y ∈ Subgroup.normalizer
              ((ConjugateBlockPair.standard (R := F.Carrier) (BlockShape.singletons n)).splitComponent :
                Set (GeneralLinear n F.Carrier)) ∧
            P.parabolic.map (MulAut.conj y).toMonoidHom = B.parabolic F.Carrier ∧
            P.splitComponent.map (MulAut.conj y).toMonoidHom =
              (ConjugateBlockPair.standard (R := F.Carrier) B).splitComponent ∧
            P.leviSubgroup.map (MulAut.conj y).toMonoidHom = B.leviSubgroup F.Carrier ∧
            (∀ x, B.leviEmbedding F.Carrier (e' x) = y * P.leviEmbedding x * y⁻¹) ∧
            (T.leviRealPowerCharacter P.shape t).comp e'.toMulEquiv.symm.toMonoidHom =
              T.leviRealPowerCharacter B u ∧
            Nonempty (Representation.Equiv
              (σ.ρ.comp e'.toMulEquiv.symm.toMonoidHom) τ.ρ) := by
  let := T.topology
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  intro σ τ t u z hz e hP hA hM he hχ hρ
  obtain ⟨a, w, hfact⟩ :=
    BlockShape.exists_diagonal_mul_permutation_of_mem_normalizer F.Carrier z hz
  let m := B.diagonalLevi F.Carrier a
  have hfact' : z = B.leviEmbedding F.Carrier m * GeneralLinear.permutation n F.Carrier w := by
    change z = B.leviEmbedding F.Carrier (B.diagonalLevi F.Carrier a) * _
    rw [B.leviEmbedding_diagonalLevi F.Carrier a]
    exact hfact
  rw [hfact'] at hP hA hM
  refine ⟨w, T.removeTargetLeviFactor e m,
    BlockShape.permutation_mem_singletonSplitComponent_normalizer F.Carrier w,
    parabolic_map_conj_removeLeviFactor P m _ hP,
    splitComponent_map_conj_removeLeviFactor P m _ hA,
    leviSubgroup_map_conj_removeLeviFactor P m _ hM,
    T.removeTargetLeviFactor_embedding P e m z _ hfact' he,
    T.removeTargetLeviFactor_character e m t u hχ, ?_⟩
  exact ⟨T.removeTargetLeviFactorRepresentationEquiv e m σ τ hρ.some⟩

end Langlands.PadicField.TopologicalData
