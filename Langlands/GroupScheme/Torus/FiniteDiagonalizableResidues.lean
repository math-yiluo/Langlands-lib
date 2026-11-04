import Langlands.GroupScheme.Torus.DiagonalizableDecomposition
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Artinian.Module

/-! # Residue fields of finite diagonalizable groups -/

noncomputable section

universe u v

open AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (k : Type u) [Field k] {L : Type v} [Field L] [Algebra k L]

/-- Finite multiplicative order gives separability, even when the supplied order
is divisible by the characteristic. The actual order is prime to it. -/
theorem isSeparable_of_isOfFinOrder {x : L} (hx : IsOfFinOrder x) :
    IsSeparable k x := by
  have : NeZero (orderOf x) := ⟨hx.orderOf_pos.ne'⟩
  have : NeZero ((orderOf x : ℕ) : L) := (IsPrimitiveRoot.orderOf x).neZero'
  have hn : ((orderOf x : ℕ) : k) ≠ 0 := by
    intro h
    apply NeZero.ne ((orderOf x : ℕ) : L)
    simpa using congrArg (algebraMap k L) h
  exact (Polynomial.separable_X_pow_sub_C (1 : k) hn one_ne_zero).of_dvd
    (minpoly.dvd k x (by simp))

variable (A : Type u) [AddCommGroup A] [Finite A]

/-- Every element in the image of a finite group algebra in a field is separable. -/
theorem isSeparable_groupAlgebra_image (f : AddMonoidAlgebra k A →ₐ[k] L)
    (z : AddMonoidAlgebra k A) : IsSeparable k (f z) := by
  induction z using AddMonoidAlgebra.induction_on with
  | of a =>
      let g : Multiplicative A →* L := f.toMonoidHom.comp (AddMonoidAlgebra.of k A)
      apply isSeparable_of_isOfFinOrder k
      change IsOfFinOrder (g (.ofAdd a))
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨orderOf (Multiplicative.ofAdd a), orderOf_pos _, ?_⟩
      rw [← map_pow, pow_orderOf_eq_one, map_one]
  | add x y hx hy =>
      simpa using Field.isSeparable_add hx hy
  | smul r x hx =>
      rw [map_smul, Algebra.smul_def]
      exact Field.isSeparable_mul (isSeparable_algebraMap r) hx

/-- A field quotient of the finite group algebra is a separable extension. -/
theorem isSeparable_of_surjective_groupAlgebra
    (f : AddMonoidAlgebra k A →ₐ[k] L) (hf : Function.Surjective f) :
    Algebra.IsSeparable k L := by
  constructor
  intro z
  obtain ⟨z, rfl⟩ := hf z
  exact isSeparable_groupAlgebra_image k A f z

/-- The finite group algebra has finitely many prime points, with no reducedness
or restriction on the characteristic. -/
instance finite_groupAlgebra_spectrum : Finite (PrimeSpectrum (AddMonoidAlgebra k A)) := by
  let : IsArtinianRing (AddMonoidAlgebra k A) := IsArtinianRing.of_finite k _
  infer_instance

variable (P : Ideal (AddMonoidAlgebra k A)) [P.IsPrime]

/-- The actual canonical algebra map to the prime residue field. -/
def groupAlgebraResidueFieldMap : AddMonoidAlgebra k A →ₐ[k] P.ResidueField :=
  IsScalarTower.toAlgHom k (AddMonoidAlgebra k A) P.ResidueField

/-- Finiteness of the indexing group makes the canonical residue map surjective. -/
theorem groupAlgebraResidueFieldMap_surjective :
    Function.Surjective (groupAlgebraResidueFieldMap k A P) := by
  let : IsArtinianRing (AddMonoidAlgebra k A) := IsArtinianRing.of_finite k _
  exact P.algebraMap_residueField_surjective

/-- Every prime residue field of the full finite group algebra is finite over k. -/
instance groupAlgebra_residueField_finite : Module.Finite k P.ResidueField := by
  let : IsArtinianRing (AddMonoidAlgebra k A) := IsArtinianRing.of_finite k _
  exact Module.Finite.trans (AddMonoidAlgebra k A) P.ResidueField

/-- Every prime residue field of the full finite group algebra is separable over k. -/
instance groupAlgebra_residueField_isSeparable : Algebra.IsSeparable k P.ResidueField := by
  exact isSeparable_of_surjective_groupAlgebra k A
    (groupAlgebraResidueFieldMap k A P) (groupAlgebraResidueFieldMap_surjective k A P)

end Langlands.GroupScheme.Diagonalizable
