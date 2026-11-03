import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.PointwiseSchemeAction

/-! # Fixed lifting for arbitrary diagonalizable scheme actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : PointwiseSchemeAction (Diagonalizable.groupScheme R M).toGrp G.X)

/-- The natural coordinate action of any actual diagonalizable scheme action. -/
def ofPointwiseSchemeAction : Action (M := M) (AffineCoordinates.algebra G) where
  act {C} t x := (AffineCoordinates.pointEquiv G C).symm
    (a.act (characterPoint t) (AffineCoordinates.pointEquiv G C x))
  one {C} x := by
    apply (AffineCoordinates.pointEquiv G C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_one, a.act_one_left]
  mul {C} t s x := by
    apply (AffineCoordinates.pointEquiv G C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_mul, a.act_mul_left]
  naturality {C D} f t x := by
    apply (AffineCoordinates.pointEquiv G D).injective
    simp only [Equiv.apply_symm_apply, AffineCoordinates.pointEquiv_comp,
      characterPoint_mapCharacter, ← a.naturality]

theorem pointEquiv_schemeAct {C : CommAlgCat.{u} R} (t : Multiplicative M →* Cˣ)
    (x : AffineCoordinates.algebra G ⟶ C) :
    AffineCoordinates.pointEquiv G C ((ofPointwiseSchemeAction a).act t x) =
      a.act (characterPoint t) (AffineCoordinates.pointEquiv G C x) :=
  Equiv.apply_symm_apply _ _

/-- Coordinate fixedness is the actual all-scheme condition. -/
theorem isFixed_iff_schemeAction {C : CommAlgCat.{u} R}
    (x : AffineCoordinates.algebra G ⟶ C) :
    IsFixed (ofPointwiseSchemeAction a) x ↔ a.IsFixed (AffineCoordinates.pointEquiv G C x) := by
  let : IsAffine (Diagonalizable.groupScheme R M).X.left := by
    change IsAffine (Spec (CommRingCat.of (AddMonoidAlgebra R M)))
    infer_instance
  rw [a.isFixed_iff_affineRefinements]
  constructor
  · intro hx D f h
    let t := Corepresented.affinePointsEquiv (Diagonalizable.functor R M)
      (Diagonalizable.grpCorepresentation R M) D h
    have ht : characterPoint t = h := MulEquiv.symm_apply_apply _ h
    have e := congrArg (AffineCoordinates.pointEquiv G D) (hx D f t)
    rw [pointEquiv_schemeAct, AffineCoordinates.pointEquiv_comp, ht] at e
    exact e
  · intro hx D f t
    apply (AffineCoordinates.pointEquiv G D).injective
    rw [pointEquiv_schemeAct, AffineCoordinates.pointEquiv_comp]
    exact hx D f (characterPoint t)

/-- Coefficient equations for the fixed locus of an arbitrary scheme action. -/
abbrev schemeActionFixedIdeal : Ideal (AffineCoordinates.algebra G) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
    (coaction (ofPointwiseSchemeAction a)).hom.toRingHom

theorem schemeActionFixedIdeal_le_ker_iff {C : CommAlgCat.{u} R}
    (x : AffineCoordinates.algebra G ⟶ C) :
    schemeActionFixedIdeal a ≤ RingHom.ker x.hom.toRingHom ↔
      a.IsFixed (AffineCoordinates.pointEquiv G C x) := by
  rw [← isFixed_iff_schemeAction, ← fixedIdeal_le_ker_iff_isFixed]

/-- Arbitrary scheme actions have formally smooth fixed coordinate quotients. -/
theorem formallySmooth_schemeActionFixedQuotient
    [Algebra.FormallySmooth R (AffineCoordinates.algebra G)] :
    Algebra.FormallySmooth R (AffineCoordinates.algebra G ⧸ schemeActionFixedIdeal a) :=
  formallySmooth_fixedQuotient (ofPointwiseSchemeAction a)

end CharacterAction

end Langlands.GroupScheme
