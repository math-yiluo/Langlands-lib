import Langlands.GroupScheme.LinearPicardTrivialStatement
import Langlands.GroupScheme.GeneralLinearLocalization
import Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-! # The Picard groups of `SLₙ` and `GLₙ` vanish: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CommRing

namespace Langlands.GroupScheme.LinearPicardTrivial

/-- A retract of a commutative ring with trivial Picard group has trivial Picard group:
base change along the section is injective on Picard groups. -/
theorem subsingleton_pic_of_retract {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (hgf : g.comp f = RingHom.id A)
    [Subsingleton (Pic B)] : Subsingleton (Pic A) := by
  constructor
  intro M N
  rw [← Pic.mapRingHom_id_apply (M := M), ← Pic.mapRingHom_id_apply (M := N), ← hgf,
    ← Pic.mapRingHom_mapRingHom, ← Pic.mapRingHom_mapRingHom,
    Subsingleton.elim (Pic.mapRingHom f M) (Pic.mapRingHom f N)]

section GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (k : Type u) [Field k]

/-- The determinant of the matrix of polynomial entry variables is nonzero. -/
theorem determinantPolynomial_ne_zero : GeneralLinear.determinantPolynomial n k ≠ 0 :=
  Matrix.det_mvPolynomialX_ne_zero n k

/-- The determinant localization of the polynomial ring is a domain. -/
instance isDomain_determinantLocalization :
    IsDomain (GeneralLinear.DeterminantLocalization n k) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (determinantPolynomial_ne_zero n k))

/-- The determinant localization is a unique factorization domain, so its Picard group is
trivial. -/
theorem subsingleton_pic_determinantLocalization :
    Subsingleton (Pic (GeneralLinear.DeterminantLocalization n k)) :=
  inferInstance

/-- The coordinate ring of `GLₙ` over a field has trivial Picard group. -/
theorem subsingleton_pic_generalLinear :
    Subsingleton (Pic (GeneralLinear.CoordinateRing n k)) :=
  haveI := subsingleton_pic_determinantLocalization n k
  Langlands.CommutativeAlgebra.subsingleton_pic_of_ringEquiv
    (GeneralLinear.determinantLocalizationEquiv n k).symm.toRingEquiv

end GeneralLinear

section SpecialLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : Type u) [CommRing R]

/-- Restriction of functions from `GLₙ` to `SLₙ`: the algebra map classifying the universal
determinant-one matrix as an invertible matrix. -/
def restriction : GeneralLinear.CoordinateRing n R →ₐ[R] SpecialLinear.CoordinateRing n R :=
  GeneralLinear.classify (Matrix.SpecialLinearGroup.toGL (SpecialLinear.universal n R))

/-- The invertible matrix classified by `restriction` is the universal determinant-one
matrix. -/
theorem point_restriction :
    GeneralLinear.point (restriction n R) =
      Matrix.SpecialLinearGroup.toGL (SpecialLinear.universal n R) :=
  GeneralLinear.point_classify _

/-- The inverse determinant of the universal invertible matrix. -/
def inverseDeterminant : GeneralLinear.CoordinateRing n R :=
  Matrix.det (((GeneralLinear.universal n R)⁻¹ : GL n (GeneralLinear.CoordinateRing n R)) :
    Matrix n n (GeneralLinear.CoordinateRing n R))

/-- The determinant of the universal invertible matrix times `inverseDeterminant` is one. -/
theorem det_universal_mul_inverseDeterminant :
    Matrix.det ((GeneralLinear.universal n R : GL n (GeneralLinear.CoordinateRing n R)) :
      Matrix n n (GeneralLinear.CoordinateRing n R)) * inverseDeterminant n R = 1 := by
  rw [inverseDeterminant, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one]

/-- The universal invertible matrix, with its column `i₀` scaled by the inverse determinant,
as a determinant-one matrix. -/
def normalizedUniversal (i₀ : n) :
    Matrix.SpecialLinearGroup n (GeneralLinear.CoordinateRing n R) :=
  ⟨((GeneralLinear.universal n R : GL n (GeneralLinear.CoordinateRing n R)) :
      Matrix n n (GeneralLinear.CoordinateRing n R)) *
    Matrix.diagonal (Pi.mulSingle i₀ (inverseDeterminant n R)), by
    rw [Matrix.det_mul, Matrix.det_diagonal, Fintype.prod_pi_mulSingle',
      det_universal_mul_inverseDeterminant]⟩

/-- Restricted to `SLₙ`, the inverse determinant is one. -/
theorem restriction_inverseDeterminant :
    restriction n R (inverseDeterminant n R) = 1 := by
  rw [inverseDeterminant, AlgHom.map_det]
  have h : (restriction n R).mapMatrix
      (((GeneralLinear.universal n R)⁻¹ : GL n (GeneralLinear.CoordinateRing n R)) :
        Matrix n n (GeneralLinear.CoordinateRing n R)) =
      ((SpecialLinear.universal n R)⁻¹ : Matrix.SpecialLinearGroup n
        (SpecialLinear.CoordinateRing n R)) := by
    ext a b
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, GeneralLinear.universal_inv_apply,
      ← GeneralLinear.point_inv_apply, point_restriction, ← map_inv]
    rfl
  rw [h]
  exact Matrix.SpecialLinearGroup.det_coe _

/-- Restriction to `SLₙ` after the normalizing section is the identity. -/
theorem restriction_comp_classify_normalizedUniversal (i₀ : n) :
    (restriction n R).comp (SpecialLinear.classify (normalizedUniversal n R i₀)) =
      AlgHom.id R (SpecialLinear.CoordinateRing n R) := by
  apply SpecialLinear.homEquiv.injective
  change SpecialLinear.point ((restriction n R).comp
      (SpecialLinear.classify (normalizedUniversal n R i₀))) =
    SpecialLinear.point (AlgHom.id R (SpecialLinear.CoordinateRing n R))
  rw [SpecialLinear.point_comp, SpecialLinear.point_classify, SpecialLinear.point_id]
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  change restriction n R (((((GeneralLinear.universal n R :
      GL n (GeneralLinear.CoordinateRing n R)) : Matrix n n _) *
    Matrix.diagonal (Pi.mulSingle i₀ (inverseDeterminant n R)) :
      Matrix n n (GeneralLinear.CoordinateRing n R))) a b) = _
  rw [Matrix.mul_diagonal, map_mul, GeneralLinear.universal_apply,
    ← GeneralLinear.point_apply, point_restriction]
  by_cases hb : b = i₀
  · subst hb
    rw [Pi.mulSingle_eq_same, restriction_inverseDeterminant, mul_one]
    rfl
  · rw [Pi.mulSingle_eq_of_ne hb, map_one, mul_one]
    rfl

/-- `SLₙ` is a retract of `GLₙ` on coordinate rings. -/
theorem exists_restriction_section :
    ∃ s : SpecialLinear.CoordinateRing n R →ₐ[R] GeneralLinear.CoordinateRing n R,
      (restriction n R).comp s = AlgHom.id R (SpecialLinear.CoordinateRing n R) := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · refine ⟨SpecialLinear.classify 1, ?_⟩
    apply SpecialLinear.homEquiv.injective
    apply Matrix.SpecialLinearGroup.ext
    intro a
    exact isEmptyElim a
  · exact ⟨_, restriction_comp_classify_normalizedUniversal n R i₀⟩

end SpecialLinear

/-- The coordinate ring of `SLₙ` over a field has trivial Picard group. -/
theorem subsingleton_pic_specialLinear (n : Type) [Fintype n] [DecidableEq n]
    (k : Type u) [Field k] : Subsingleton (Pic (SpecialLinear.CoordinateRing n k)) := by
  obtain ⟨s, hs⟩ := exists_restriction_section n k
  have := subsingleton_pic_generalLinear n k
  exact subsingleton_pic_of_retract s.toRingHom (restriction n k).toRingHom
    (RingHom.ext fun x => AlgHom.congr_fun hs x)

/-- On the spectrum of a ring with trivial Picard group, every line bundle is isomorphic in
`LineBundle` to the trivial line bundle. -/
theorem nonempty_iso_trivial_of_pic_trivial {R : CommRingCat.{u}}
    [Subsingleton (Pic R)] (L : Langlands.AlgebraicGeometry.Picard.LineBundle (Spec R)) :
    Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial (Spec R)) := by
  obtain ⟨e⟩ := Langlands.AlgebraicGeometry.Picard.nonempty_lineBundle_iso_structureSheaf_of_pic_trivial L
  exact ⟨ObjectProperty.isoMk _ e⟩

/-- **The Picard groups of `SLₙ` and `GLₙ` over a field vanish** (Milne, *Algebraic Groups*,
Proposition 20.30). -/
theorem linearPicardTrivialStatement : LinearPicardTrivialStatement.{u} := by
  intro k _ n _ _
  refine ⟨fun L => ?_, fun L => ?_⟩
  · exact @nonempty_iso_trivial_of_pic_trivial
      (CommRingCat.of (SpecialLinear.CoordinateRing n k)) (subsingleton_pic_specialLinear n k) L
  · exact @nonempty_iso_trivial_of_pic_trivial
      (CommRingCat.of (GeneralLinear.CoordinateRing n k)) (subsingleton_pic_generalLinear n k) L

end Langlands.GroupScheme.LinearPicardTrivial
