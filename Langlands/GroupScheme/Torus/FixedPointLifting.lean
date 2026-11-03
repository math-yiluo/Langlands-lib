import Langlands.GroupScheme.Torus.AffineSchemeAction

/-! # Nilpotent lifting of diagonalizable fixed points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {B : CommAlgCat.{u} R} (a : Action (M := M) B)

/-- A point fixed after every algebra refinement lifts through a nilpotent quotient
as a point with the same fixedness property. -/
theorem exists_fixed_lift [Algebra.FormallySmooth R B]
    {C : CommAlgCat.{u} R} (I : Ideal C) (hI : IsNilpotent I)
    (x : B ⟶ CommAlgCat.of R (C ⧸ I)) (hx : IsFixed a x) :
    ∃ y : B ⟶ C, IsFixed a y ∧
      y ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) = x := by
  let J := Langlands.CommutativeAlgebra.GradedFixedQuotient.fixedIdeal
    (coaction a).hom.toRingHom
  have hxJ : J ≤ RingHom.ker x.hom.toRingHom :=
    (fixedIdeal_le_ker_iff_isFixed a x).2 hx
  let x' : B ⧸ J →ₐ[R] C ⧸ I := Ideal.Quotient.liftₐ J x.hom hxJ
  let : Algebra.FormallySmooth R (B ⧸ J) := formallySmooth_fixedQuotient a
  obtain ⟨y', hy'⟩ := Algebra.FormallySmooth.exists_lift I hI x'
  let y : B ⟶ C := CommAlgCat.ofHom (y'.comp (Ideal.Quotient.mkₐ R J))
  refine ⟨y, (fixedIdeal_le_ker_iff_isFixed a y).1 ?_, ?_⟩
  · intro b hb
    change y' (Ideal.Quotient.mk J b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
  · apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    change Ideal.Quotient.mk I (y' (Ideal.Quotient.mk J b)) = x.hom b
    exact AlgHom.congr_fun hy' (Ideal.Quotient.mk J b)

/-- A chosen fixed lift through a nilpotent quotient. -/
def fixedLift [Algebra.FormallySmooth R B]
    {C : CommAlgCat.{u} R} (I : Ideal C) (hI : IsNilpotent I)
    (x : B ⟶ CommAlgCat.of R (C ⧸ I)) (hx : IsFixed a x) : B ⟶ C :=
  (exists_fixed_lift a I hI x hx).choose

theorem fixedLift_isFixed [Algebra.FormallySmooth R B]
    {C : CommAlgCat.{u} R} (I : Ideal C) (hI : IsNilpotent I)
    (x : B ⟶ CommAlgCat.of R (C ⧸ I)) (hx : IsFixed a x) :
    IsFixed a (fixedLift a I hI x hx) :=
  (exists_fixed_lift a I hI x hx).choose_spec.1

@[simp]
theorem fixedLift_comp_quotient [Algebra.FormallySmooth R B]
    {C : CommAlgCat.{u} R} (I : Ideal C) (hI : IsNilpotent I)
    (x : B ⟶ CommAlgCat.of R (C ⧸ I)) (hx : IsFixed a x) :
    fixedLift a I hI x hx ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) = x :=
  (exists_fixed_lift a I hI x hx).choose_spec.2

end CharacterAction

namespace PointwiseSchemeAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : PointwiseSchemeAction (Diagonalizable.groupScheme R M).toGrp G.X)

/-- Fixed points of an actual diagonalizable scheme action lift through nilpotent
quotients, with fixedness still tested after every scheme refinement. -/
theorem exists_fixed_lift [Algebra.FormallySmooth R (AffineCoordinates.algebra G)]
    {C : CommAlgCat.{u} R} (I : Ideal C) (hI : IsNilpotent I)
    (x : (algSpec R).obj (op (CommAlgCat.of R (C ⧸ I))) ⟶ G.X)
    (hx : a.IsFixed x) :
    ∃ y : (algSpec R).obj (op C) ⟶ G.X, a.IsFixed y ∧
      (algSpec R).map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)).op ≫ y = x := by
  let x' := (AffineCoordinates.pointEquiv G (CommAlgCat.of R (C ⧸ I))).symm x
  have hx' : CharacterAction.IsFixed (CharacterAction.ofPointwiseSchemeAction a) x' := by
    rw [CharacterAction.isFixed_iff_schemeAction]
    simpa only [x', Equiv.apply_symm_apply] using hx
  obtain ⟨y', hy', he⟩ := CharacterAction.exists_fixed_lift
    (CharacterAction.ofPointwiseSchemeAction a) I hI x' hx'
  refine ⟨AffineCoordinates.pointEquiv G C y',
    (CharacterAction.isFixed_iff_schemeAction a y').1 hy', ?_⟩
  have h := congrArg (AffineCoordinates.pointEquiv G (CommAlgCat.of R (C ⧸ I))) he
  rw [AffineCoordinates.pointEquiv_comp] at h
  simpa only [x', Equiv.apply_symm_apply] using h

end PointwiseSchemeAction

end Langlands.GroupScheme
