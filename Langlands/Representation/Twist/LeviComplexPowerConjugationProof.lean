import Langlands.Representation.Twist.LeviComplexPowerConjugationStatement

/-! # Complex twists commute with actual Levi conjugation -/

noncomputable section

open scoped BigOperators

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF

variable {F : Type uF} [Field F] {n : ℕ} {B C : BlockShape n}
  {w : Equiv.Perm (Fin n)}

/-- The inverse conjugate has the target entries reindexed by the actual
within-block bijection; no minimality is required. -/
theorem leviConjugation_symm_block_entry_innerMap
    (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F) (i : Fin B.length)
    (a b : Fin (B.size i)) :
    (leviConjugation B C w hw).symm m i a b =
      m (blockMap B C w i) (innerMap hw i a) (innerMap hw i b) := by
  rw [← B.leviEmbedding_apply_same F, leviConjugation_symm_embedding,
    mul_permutation_entry, permutation_inv, permutation_mul_entry, inv_inv,
    ← index_innerMap hw i a, ← index_innerMap hw i b, C.leviEmbedding_apply_same]

/-- Simultaneous reindexing preserves the determinant of the corresponding block. -/
theorem leviConjugation_symm_block_determinant
    (hw : ConjugatesLevi (F := F) B C w) (m : C.Levi F) (i : Fin B.length) :
    determinant ((leviConjugation B C w hw).symm m i) =
      determinant (m (blockMap B C w i)) := by
  let e := Equiv.ofBijective (innerMap hw i) (innerMap_bijective hw i)
  have hmatrix :
      ((leviConjugation B C w hw).symm m i :
          Matrix (Fin (B.size i)) (Fin (B.size i)) F) =
        (m (blockMap B C w i) :
          Matrix (Fin (C.size (blockMap B C w i)))
            (Fin (C.size (blockMap B C w i))) F).submatrix e e := by
    ext a b
    exact leviConjugation_symm_block_entry_innerMap hw m i a b
  apply Units.ext
  change Matrix.det _ = Matrix.det _
  rw [hmatrix, Matrix.det_submatrix_equiv_self]

end Langlands.CuspidalSupport

namespace Langlands.PadicField.TopologicalData

open GeneralLinear CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F.Carrier) B C w)

/-- Inverse actual conjugation pulls the source character to the target
character with parameters reindexed by the inverse block bijection. -/
theorem leviComplexPowerCharacter_conjugation (z : Fin B.length → ℂ) :
    (T.leviComplexPowerCharacter B z).comp
        (leviConjugation B C w hw).symm.toMonoidHom =
      T.leviComplexPowerCharacter C (fun j => z ((blockEquiv hw).symm j)) := by
  apply MonoidHom.ext
  intro m
  apply Units.ext
  change (T.leviComplexPowerCharacter B z ((leviConjugation B C w hw).symm m) : ℂ) = _
  rw [T.coe_leviComplexPowerCharacter B, T.coe_leviComplexPowerCharacter C]
  apply Fintype.prod_equiv (blockEquiv hw)
  intro i
  rw [leviConjugation_symm_block_determinant hw m i]
  simp only [Equiv.symm_apply_apply]
  rfl

/-- Actual representation transport commutes with the complex determinant twist. -/
theorem transport_leviComplexPowerTwist (z : Fin B.length → ℂ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    transport B C w hw (T.leviComplexPowerTwist B z ρ) =
      T.leviComplexPowerTwist C (fun j => z ((blockEquiv hw).symm j))
        (transport B C w hw ρ) := by
  ext m v
  change (T.leviComplexPowerCharacter B z ((leviConjugation B C w hw).symm m) : ℂ) •
      ρ ((leviConjugation B C w hw).symm m) v =
    (T.leviComplexPowerCharacter C (fun j => z ((blockEquiv hw).symm j)) m : ℂ) •
      ρ ((leviConjugation B C w hw).symm m) v
  have hχ := congrArg (fun χ : C.Levi F.Carrier →* ℂˣ => χ m)
    (T.leviComplexPowerCharacter_conjugation B C w hw z)
  change T.leviComplexPowerCharacter B z ((leviConjugation B C w hw).symm m) =
    T.leviComplexPowerCharacter C (fun j => z ((blockEquiv hw).symm j)) m at hχ
  rw [hχ]

end Langlands.PadicField.TopologicalData

namespace Langlands

universe uF uV

/-- The complete closed compatibility statement, with independent universes. -/
theorem leviComplexPowerConjugation : LeviComplexPowerConjugationStatement.{uF,uV} := by
  intro p _ F T n B C w hw z
  exact ⟨T.leviComplexPowerCharacter_conjugation B C w hw z,
    fun _ _ _ ρ => T.transport_leviComplexPowerTwist B C w hw z ρ⟩

end Langlands
