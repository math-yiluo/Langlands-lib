import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

noncomputable section
open scoped TensorProduct
open CategoryTheory Algebra

namespace Langlands.GroupScheme.SU3Root

universe u v w w' w''

variable (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
  [IsQuadraticExtension k L] [Algebra.IsSeparable k L]

local instance quadraticFiniteDimensional : FiniteDimensional k L :=
  .of_finrank_pos (by rw [IsQuadraticExtension.finrank_eq_two k L]; decide)

theorem quadratic_aut_card : Fintype.card (L ≃ₐ[k] L) = 2 := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
    IsQuadraticExtension.finrank_eq_two k L]

theorem exists_quadratic_conjugation : ∃ c : L ≃ₐ[k] L, c ≠ 1 := by
  apply Fintype.exists_ne_of_one_lt_card
  rw [quadratic_aut_card k L]
  decide

/-- The unique nonidentity automorphism of the actual separable quadratic extension. -/
def conjugation : L ≃ₐ[k] L := Classical.choose (exists_quadratic_conjugation k L)

theorem conjugation_ne_one : conjugation k L ≠ 1 :=
  Classical.choose_spec (exists_quadratic_conjugation k L)

local instance : DecidableEq (L ≃ₐ[k] L) := Classical.typeDecidableEq _

theorem quadratic_aut_univ : (Finset.univ : Finset (L ≃ₐ[k] L)) = {(1 : L ≃ₐ[k] L), conjugation k L} := by
  classical
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [quadratic_aut_card k L, Ne.symm (conjugation_ne_one k L)]

theorem conjugation_unique (c : L ≃ₐ[k] L) (hc : c ≠ 1) : c = conjugation k L := by
  classical
  have h : c ∈ ({(1 : L ≃ₐ[k] L), conjugation k L} : Finset (L ≃ₐ[k] L)) := by
    rw [← quadratic_aut_univ k L]
    exact Finset.mem_univ _
  simpa [hc] using h

theorem conjugation_involutive : Function.Involutive (conjugation k L) := by
  have h : conjugation k L ^ 2 = 1 := by
    rw [← quadratic_aut_card k L]
    exact pow_card_eq_one
  intro x
  exact congrArg (fun c : L ≃ₐ[k] L => c x) h

/-- The generic ring involution supplied by the actual extension conjugation. -/
def fieldInvolution : RingInvolution L where
  bar := (conjugation k L).toRingEquiv
  involutive := conjugation_involutive k L

@[simp] theorem fieldInvolution_bar (x : L) :
    (fieldInvolution k L).bar x = conjugation k L x := rfl

/-- The ordinary field trace is the sum of an element and its conjugate. -/
theorem algebraMap_trace (x : L) :
    algebraMap k L (Algebra.trace k L x) = x + conjugation k L x := by
  classical
  rw [trace_eq_sum_automorphisms, quadratic_aut_univ k L]
  simp [Ne.symm (conjugation_ne_one k L)]

section Tensor

variable (R : Type w) [CommRing R] [Algebra k R]

/-- The involution `id_R tensor conjugation` on the actual tensor algebra. -/
def tensorConjugation : R ⊗[k] L ≃ₐ[R] R ⊗[k] L :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (conjugation k L)

@[simp] theorem tensorConjugation_tmul (r : R) (x : L) :
    tensorConjugation k L R (r ⊗ₜ[k] x) = r ⊗ₜ[k] conjugation k L x := rfl

theorem tensorConjugation_involutive : Function.Involutive (tensorConjugation k L R) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp [conjugation_involutive k L x]
  | add x y hx hy => simp [hx, hy]

/-- The involutive ring used in quadratic root parameters over a test algebra. -/
def tensorInvolution : RingInvolution (R ⊗[k] L) where
  bar := (tensorConjugation k L R).toRingEquiv
  involutive := tensorConjugation_involutive k L R

/-- The actual quadratic root parameter group on a commutative test algebra. -/
abbrev tensorParameters := Parameters (tensorInvolution k L R)

end Tensor

section BaseChange

variable {R : Type w} {S : Type w'} {T : Type w''}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra k S] [Algebra k T]

/-- Coefficient change acts on the first tensor factor. -/
def tensorCoefficientMap (f : R →ₐ[k] S) : R ⊗[k] L →ₐ[k] S ⊗[k] L :=
  Algebra.TensorProduct.map f (AlgHom.id k L)

omit [IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
@[simp] theorem tensorCoefficientMap_tmul (f : R →ₐ[k] S) (r : R) (x : L) :
    tensorCoefficientMap k L f (r ⊗ₜ[k] x) = f r ⊗ₜ[k] x := rfl

theorem tensorCoefficientMap_bar (f : R →ₐ[k] S) (x : R ⊗[k] L) :
    tensorCoefficientMap k L f ((tensorInvolution k L R).bar x) =
      (tensorInvolution k L S).bar (tensorCoefficientMap k L f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
@[simp] theorem tensorCoefficientMap_id :
    tensorCoefficientMap k L (AlgHom.id k R) = AlgHom.id k (R ⊗[k] L) :=
  Algebra.TensorProduct.map_id

omit [IsQuadraticExtension k L] [Algebra.IsSeparable k L] in
theorem tensorCoefficientMap_comp (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    tensorCoefficientMap k L (g.comp f) =
      (tensorCoefficientMap k L g).comp (tensorCoefficientMap k L f) :=
by
  apply Algebra.TensorProduct.ext
  · ext r
    rfl
  · ext x
    rfl

/-- The coefficient map on the concrete coordinate group. -/
def tensorParametersMap (f : R →ₐ[k] S) :
    tensorParameters k L R →* tensorParameters k L S :=
  Parameters.map (tensorCoefficientMap k L f).toRingHom (tensorCoefficientMap_bar k L f)

@[simp] theorem first_tensorParametersMap (f : R →ₐ[k] S) (x : tensorParameters k L R) :
    (tensorParametersMap k L f x).first = tensorCoefficientMap k L f x.first := rfl

@[simp] theorem second_tensorParametersMap (f : R →ₐ[k] S) (x : tensorParameters k L R) :
    (tensorParametersMap k L f x).second = tensorCoefficientMap k L f x.second := rfl

@[simp] theorem tensorParametersMap_id :
    tensorParametersMap k L (AlgHom.id k R) = MonoidHom.id (tensorParameters k L R) := by
  apply MonoidHom.ext
  intro x
  apply Parameters.ext <;> simp [tensorParametersMap]

theorem tensorParametersMap_comp (f : R →ₐ[k] S) (g : S →ₐ[k] T) :
    tensorParametersMap k L (g.comp f) =
      (tensorParametersMap k L g).comp (tensorParametersMap k L f) := by
  apply MonoidHom.ext
  intro x
  apply Parameters.ext <;> simp [tensorCoefficientMap_comp]

end BaseChange

/-- The genuine covariant group-valued functor on commutative k-algebras. -/
def tensorParametersFunctor : CommAlgCat.{w} k ⥤ GrpCat.{max w v} where
  obj R := GrpCat.of (tensorParameters k L R)
  map f := GrpCat.ofHom (tensorParametersMap k L f.hom)
  map_id R := by
    apply GrpCat.hom_ext
    exact tensorParametersMap_id k L
  map_comp f g := by
    apply GrpCat.hom_ext
    exact tensorParametersMap_comp k L f.hom g.hom

end Langlands.GroupScheme.SU3Root
