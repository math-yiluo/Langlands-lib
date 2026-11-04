import Langlands.GroupScheme.Nilpotent.UniformPoints
import Langlands.GroupScheme.Lie.Adjoint

/-! # Nilpotence of adjoint differences -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite commutatorElement
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
    [IsAffineHom G.X.hom]
    {A : Type u} [CommRing A] [Algebra R A]

/-- The difference between conjugation by a point and the identity on the
actual dual-number Lie kernel. -/
def adjointDifference (g : AffinePoints G A) :
    Module.End A (Additive (lieKernel G A)) :=
  adjoint G A g - 1

/-- An adjoint difference is an actual group commutator on dual-number
points. -/
theorem adjointDifference_val (g : AffinePoints G A)
    (X : Additive (lieKernel G A)) :
    (adjointDifference G g X).toMul.val = ⁅constant G g, X.toMul.val⁆ := by
  change (lieKernelConjugation G g X.toMul * X.toMul⁻¹).val = _
  rfl

/-- Each power of the difference lies in the matching lower central term
of the actual dual-number point group. -/
theorem adjointDifference_pow_mem_lowerCentralSeries
    (g : AffinePoints G A) (X : Additive (lieKernel G A)) (n : ℕ) :
    ((adjointDifference G g ^ n) X).toMul.val ∈
      (⊤ : Subgroup (AffinePoints G (DualNumber A))).lowerCentralSeries n := by
  induction n with
  | zero => exact Subgroup.mem_top _
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, adjointDifference_val,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) ih

end Lie

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {A : Type u} [CommRing A] [Algebra k A]

/-- An all-test nilpotence bound annihilates each adjoint difference with
the same bound, over every coefficient algebra. -/
theorem Lie.adjointDifference_pow_eq_zero_of_uniformNilpotence
    {d : ℕ} (hd : HasUniformNilpotentPoints G d) (g : Lie.AffinePoints G A) :
    Lie.adjointDifference G g ^ d = 0 := by
  apply LinearMap.ext
  intro X
  apply Additive.toMul.injective
  apply Subtype.ext
  have h := Lie.adjointDifference_pow_mem_lowerCentralSeries G g X d
  rw [hd _, Subgroup.mem_bot] at h
  exact h

/-- For a smooth connected affine geometrically nilpotent group, every
point acts unipotently on the Lie algebra over every coefficient algebra. -/
theorem IsNilpotentGroupScheme.isNilpotent_adjointDifference
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hG : IsNilpotentGroupScheme G) (g : Lie.AffinePoints G A) :
    IsNilpotent (Lie.adjointDifference G g) :=
  ⟨hG.uniformNilpotenceBound,
    Lie.adjointDifference_pow_eq_zero_of_uniformNilpotence
      hG.uniformNilpotenceBound_spec g⟩

end Langlands.GroupScheme
