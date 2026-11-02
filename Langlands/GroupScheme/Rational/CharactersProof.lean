import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.Rational.BlockCharacterProof

noncomputable section

universe u

namespace Langlands.GroupScheme

open _root_.Langlands.GroupScheme.GeneralLinear

/-- The rational characters of GL and its block Levi subgroups are freely generated
by the corresponding determinants; the scalar torus is the positive-rank split component. -/
theorem generalLinearCharacters : GeneralLinearCharactersStatement.{u} := by
  intro k _
  constructor
  · intro n
    refine ⟨rationalCharacter_eq_zsmul_determinant, ?_, ?_, ?_, ?_⟩
    · intro hn χ
      subst n
      exact rationalCharacter_empty χ
    · intro hn m hm
      let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      apply determinant_zsmul_injective (n := Fin n) (R := CommRingCat.of k)
      simpa only [zero_zsmul] using hm
    · intro hn
      let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact scalarTorus_isSplitComponent k
    · simpa using (characterRestrict_scalar_determinant (n := Fin n) (R := CommRingCat.of k))
  · intro N B
    exact ⟨blockDeterminantBasis B (CommRingCat.of k),
      blockDeterminantBasis_apply B (CommRingCat.of k)⟩

end Langlands.GroupScheme
