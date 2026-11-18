import Langlands.GroupScheme.Rational.MultiplicativeTypeRepresentationStatement
import Langlands.GroupScheme.MatrixRepresentation.FixedFieldEndomorphisms
import Langlands.GroupScheme.MatrixRepresentation.IrreducibleWeightIsomorphism

/-! # Representations of multiplicative-type groups: the Galois-orbit theorem -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Every finite representation of a group of multiplicative type is semisimple,
its simple representations are classified by geometric character orbits, and
their endomorphism algebras are the corresponding stabilizer fixed fields. -/
theorem multiplicativeTypeRepresentationGaloisOrbit :
    MultiplicativeTypeRepresentationGaloisOrbitStatement.{u} := by
  intro k _ G _ hG Ks _ _ _
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k Ks)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (algebraBaseMap k Ks)))
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n ρ
    exact MatrixRepresentation.isSemisimple_of_isMultiplicativeType ρ hG
  · intro n ρ hρ
    exact MatrixRepresentation.exists_weights_eq_galoisOrbit_of_isMultiplicativeType
      (K := Ks) ρ hG hρ
  · intro χ
    exact MatrixRepresentation.exists_irreducible_weights_eq_galoisOrbit_of_isMultiplicativeType
      hG χ
  · intro n m ρ σ hρ hσ
    exact MatrixRepresentation.isomorphic_iff_weights_eq_of_isMultiplicativeType
      (K := Ks) ρ σ hG hρ hσ
  · intro n ρ χ hρ hχ H hH
    exact MatrixRepresentation.exists_fixedField_endomorphismAlgHom_of_isMultiplicativeType
      ρ hG hρ χ hχ H hH

end Langlands.GroupScheme
