import Langlands.GroupScheme.Unipotent.SplitAffineSpaceStatement
import Langlands.GroupScheme.Rational.SplitSeriesProductDecomposition
import Langlands.GroupScheme.Rational.SplitSeriesUnipotent
import Langlands.GroupScheme.MatrixRepresentation.SchemeAction
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Split unipotent groups are affine spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitAffineSpace

open MatrixRepresentation

variable {R : CommRingCat.{u}}

/-- Natural coordinates on every test scheme identify an over-scheme with affine space. -/
def isoOfCoordinates {X : Over (Spec R)} {n : ℕ}
    (e : ∀ T : Over (Spec R), (T ⟶ X) ≃ (Fin n → Γ(T.left, ⊤)))
    (he : ∀ (T W : Over (Spec R)) (f : W ⟶ T) (x : T ⟶ X),
      e W (f ≫ x) = fun i => f.left.appTop (e T x i)) :
    X ≅ coefficientSpace (Fin n) R := by
  let p {T : Over (Spec R)} (x : T ⟶ X) : T ⟶ coefficientSpace (Fin n) R :=
    (coefficientPointEquiv T).symm (e T x)
  let q {T : Over (Spec R)} (x : T ⟶ coefficientSpace (Fin n) R) : T ⟶ X :=
    (e T).symm (coefficientPointEquiv T x)
  refine Yoneda.ext _ _ p q ?_ ?_ ?_
  · intro T x
    dsimp only [p, q]
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · intro T x
    dsimp only [p, q]
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · intro T W f x
    apply coefficientCoordinates_injective
    change coefficientCoordinates (coefficientPoint W (e W (f ≫ x))) =
      coefficientCoordinates (f ≫ coefficientPoint T (e T x))
    rw [coefficientCoordinates_coefficientPoint, coefficientCoordinates_comp,
      coefficientCoordinates_coefficientPoint]
    exact he T W f x

/-- The all-test vector-group condition supplies the underlying affine-space isomorphism. -/
def vectorIso {V : GroupScheme (Spec R)} {n : ℕ}
    (hV : RelativeRoot.IsVectorGroupOfDimension V n) :
    V.X ≅ coefficientSpace (Fin n) R := by
  let e := Classical.choose hV
  exact isoOfCoordinates
    (fun T => (e T).toEquiv.trans Multiplicative.toAdd) (Classical.choose_spec hV)

/-- Concatenating coordinate vectors identifies a product of affine spaces with affine space. -/
def productIso (R : CommRingCat.{u}) (n m : ℕ) :
    coefficientSpace (Fin n) R ⊗ coefficientSpace (Fin m) R ≅
      coefficientSpace (Fin (n + m)) R := by
  let e : ∀ T : Over (Spec R),
      (T ⟶ coefficientSpace (Fin n) R ⊗ coefficientSpace (Fin m) R) ≃
        (Fin (n + m) → Γ(T.left, ⊤)) := fun T =>
    homEquivToProd.trans
      ((Equiv.prodCongr (coefficientPointEquiv T) (coefficientPointEquiv T)).trans
        (Fin.appendEquiv n m))
  apply isoOfCoordinates e
  intro T W f x
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [e, homEquivToProd, coefficientPointEquiv, coefficientCoordinates,
      Category.assoc, Fin.appendEquiv]
    rfl
  · simp [e, homEquivToProd, coefficientPointEquiv, coefficientCoordinates,
      Category.assoc, Fin.appendEquiv]
    rfl

end SplitAffineSpace

/-- Milne 14.66: a split series of length `n` gives an isomorphism of the underlying
scheme with `n`-dimensional affine space over the field. -/
theorem splitUnipotentAffineSpaceStatement : SplitUnipotentAffineSpaceStatement.{u} := by
  intro k _ n
  induction n with
  | zero =>
      intro H _ hH
      exact ⟨SplitAffineSpace.vectorIso hH.isVectorGroupOfDimension_zero⟩
  | succ n ih =>
      intro H hAff hH
      let : IsAffineHom H.X.hom := hAff
      obtain ⟨K, V, e, hK, hV, hKAff⟩ :=
        SplitSeriesDecomposition.HasSplitSeries.exists_iso_tensor hH
      obtain ⟨eK⟩ := ih K hKAff hK
      exact ⟨e.symm ≪≫ (eK ⊗ᵢ SplitAffineSpace.vectorIso hV) ≪≫
        SplitAffineSpace.productIso (CommRingCat.of k) n 1⟩

end Langlands.GroupScheme
