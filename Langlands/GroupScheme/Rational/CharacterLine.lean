import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic

/-! # Character lines and triviality on unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section General

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- A rational character is trivial on every pointwise commutator. -/
theorem characterEval_commutator (χ : rationalCharacters G) (T : Over S)
    (x y : T ⟶ G.X) :
    characterEval χ T (x * y * x⁻¹ * y⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  simp [mul_assoc]

/-- Restriction along a scheme epimorphism detects equality of characters. -/
theorem characterRestrict_injective_of_scheme_epi (q : H ⟶ G) [Epi q.hom.hom.left] :
    Function.Injective (characterRestrict q) := by
  intro χ ψ h
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_epi q.hom.hom.left).mp
  exact congrArg (fun ξ : rationalCharacters H => ξ.toMul.hom.hom.left) h

end General

section Representation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}

/-- The one-dimensional matrix representation associated with an actual character. -/
def rationalCharacters.lineRepresentation (χ : rationalCharacters G) :
    MatrixRepresentation G (Fin 1) :=
  χ.toMul ≫ GeneralLinear.scalarTorus (Fin 1) R

/-- On every scheme test the character line is the scalar matrix of its character value. -/
theorem rationalCharacters.pointMatrix_lineRepresentation (χ : rationalCharacters G)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    χ.lineRepresentation.pointMatrix T x =
      Matrix.GeneralLinearGroup.scalar (Fin 1) (characterEval χ T x) := by
  rw [MatrixRepresentation.pointMatrix_apply, rationalCharacters.lineRepresentation,
    Grp.comp_hom_hom, ← Category.assoc, GeneralLinear.pointsEquiv_scalarTorus]
  rfl

end Representation

section Unipotent

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every rational character of a unipotent group is trivial on all scheme-test points. -/
theorem IsUnipotent.characterEval_eq_one (hG : IsUnipotent G)
    (χ : rationalCharacters G) (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    characterEval χ T x = 1 := by
  obtain ⟨v, hv, hfix⟩ := hG (Fin 1) χ.lineRepresentation
  have hv0 : v 0 ≠ 0 := by
    intro h
    apply hv
    funext i
    exact (congrArg v (Subsingleton.elim i 0)).trans h
  have hi := congrFun (hfix T x) 0
  rw [χ.pointMatrix_lineRepresentation] at hi
  have hscalar : (characterEval χ T x : Γ(T.left, ⊤)) * scalarMap T (v 0) =
      scalarMap T (v 0) := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec, dotProduct,
      Matrix.scalar, Matrix.diagonal] using hi
  have hu : IsUnit (scalarMap T (v 0)) :=
    (isUnit_iff_ne_zero.mpr hv0).map (scalarMap T)
  apply Units.ext
  exact hu.mul_eq_right.mp hscalar

/-- A unipotent group has only the zero rational character. -/
theorem IsUnipotent.rationalCharacter_eq_zero (hG : IsUnipotent G)
    (χ : rationalCharacters G) : χ = 0 := by
  apply rationalCharacters.ext_characterEval
  intro T x
  rw [hG.characterEval_eq_one, characterEval_zero]

end Unipotent

end Langlands.GroupScheme
