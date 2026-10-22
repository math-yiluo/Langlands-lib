import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# General linear groups over actual number-field adeles

These are specializations of Mathlib's matrix unit groups. The finite/infinite
decomposition is constructed on entries, including both inverse matrices.
-/

noncomputable section

universe u

namespace Langlands.Global

open NumberField IsDedekindDomain

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Rational matrix points. No topology on `K` is selected. -/
abbrev RationalGL := Matrix.GeneralLinearGroup (Fin n) K

/-- Matrix units over the actual full adele ring, with the units topology. -/
abbrev AdelicGL := Matrix.GeneralLinearGroup (Fin n) (AdeleRing (𝓞 K) K)

/-- Matrix units over the finite restricted-product adele ring. -/
abbrev FiniteAdelicGL :=
  Matrix.GeneralLinearGroup (Fin n) (FiniteAdeleRing (𝓞 K) K)

/-- Matrix units over the product of the archimedean completions. -/
abbrev InfiniteAdelicGL := Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)

namespace AdelicGL

/-- The rational diagonal map, applied to every matrix entry. -/
def rational : RationalGL K n →* AdelicGL K n :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K))

@[simp]
theorem rational_apply (g : RationalGL K n) (i j : Fin n) :
    rational K n g i j = algebraMap K (AdeleRing (𝓞 K) K) (g i j) := rfl

theorem rational_injective : Function.Injective (rational K n) := by
  intro g h he
  apply Units.ext
  ext i j
  exact AdeleRing.algebraMap_injective (𝓞 K) K
    (congrArg (fun a : AdelicGL K n => a i j) he)

/-- Projection to the archimedean matrix group. -/
def infinite : AdelicGL K n →ₜ* InfiniteAdelicGL K n where
  __ := Matrix.GeneralLinearGroup.map
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  continuous_toFun := continuous_fst.generalLinearGroup_map

/-- Projection to the finite adelic matrix group. -/
def finite : AdelicGL K n →ₜ* FiniteAdelicGL K n where
  __ := Matrix.GeneralLinearGroup.map
    (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
  continuous_toFun := continuous_snd.generalLinearGroup_map

@[simp]
theorem infinite_apply (g : AdelicGL K n) (i j : Fin n) :
    infinite K n g i j = (g i j).1 := rfl

@[simp]
theorem finite_apply (g : AdelicGL K n) (i j : Fin n) :
    finite K n g i j = (g i j).2 := rfl

private def pairMatrix
    (a : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
    (b : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :
    Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K) :=
  fun i j => (a i j, b i j)

private theorem pairMatrix_mul (a a' : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))
    (b b' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :
    pairMatrix K n a b * pairMatrix K n a' b' =
      pairMatrix K n (a * a') (b * b') := by
  apply Matrix.ext
  intro i j
  change @Eq (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) _ _
  apply Prod.ext
  · change (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
      (∑ k, (a i k, b i k) * (a' k j, b' k j)) = _
    rw [map_sum]
    rfl
  · change (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))
      (∑ k, (a i k, b i k) * (a' k j, b' k j)) = _
    rw [map_sum]
    rfl

private theorem pairMatrix_one :
    pairMatrix K n 1 1 = 1 := by
  ext i j
  simp [pairMatrix, Matrix.one_apply]
  all_goals split_ifs <;> rfl

/-- Pair two invertible matrices using their actual inverse matrices. -/
def pair (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) : AdelicGL K n where
  val := pairMatrix K n a.val b.val
  inv := pairMatrix K n a.inv b.inv
  val_inv := by rw [pairMatrix_mul, a.val_inv, b.val_inv, pairMatrix_one]
  inv_val := by rw [pairMatrix_mul, a.inv_val, b.inv_val, pairMatrix_one]

@[simp]
theorem pair_apply (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n)
    (i j : Fin n) : pair K n a b i j = (a i j, b i j) := rfl

@[simp]
theorem infinite_pair (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    infinite K n (pair K n a b) = a := by
  apply Units.ext
  rfl

@[simp]
theorem finite_pair (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    finite K n (pair K n a b) = b := by
  apply Units.ext
  rfl

@[simp]
theorem pair_projections (g : AdelicGL K n) :
    pair K n (infinite K n g) (finite K n g) = g := by
  apply Units.ext
  rfl

theorem continuous_pair :
    Continuous (fun p : InfiniteAdelicGL K n × FiniteAdelicGL K n =>
      pair K n p.1 p.2) := by
  rw [Units.continuous_iff]
  constructor
  · exact continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply j).comp
        (Matrix.GeneralLinearGroup.continuous_apply _ continuous_fst i)).prodMk
        ((continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd i))
  · exact continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply j).comp
        (Matrix.GeneralLinearGroup.continuous_apply _ continuous_fst.inv i)).prodMk
        ((continuous_apply j).comp
          (Matrix.GeneralLinearGroup.continuous_apply _ continuous_snd.inv i))

/-- The full adelic matrix group is the product of its infinite and finite factors. -/
def split : AdelicGL K n ≃ₜ* InfiniteAdelicGL K n × FiniteAdelicGL K n where
  toFun g := (infinite K n g, finite K n g)
  invFun p := pair K n p.1 p.2
  left_inv := pair_projections K n
  right_inv p := by simp
  map_mul' _ _ := by ext <;> simp
  continuous_toFun := (infinite K n).continuous.prodMk (finite K n).continuous
  continuous_invFun := continuous_pair K n

/-- Inclusion of the infinite factor, with the finite factor equal to the identity. -/
def ofInfinite : InfiniteAdelicGL K n →ₜ* AdelicGL K n :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split K n).symm).comp
    (ContinuousMonoidHom.id _ |>.prod (1 : InfiniteAdelicGL K n →ₜ* FiniteAdelicGL K n))

/-- Inclusion of the finite factor, with the infinite factor equal to the identity. -/
def ofFinite : FiniteAdelicGL K n →ₜ* AdelicGL K n :=
  (ContinuousMonoidHom.toContinuousMonoidHom (split K n).symm).comp
    ((1 : FiniteAdelicGL K n →ₜ* InfiniteAdelicGL K n).prod (ContinuousMonoidHom.id _))

/-- The continuous determinant, valued in the actual idele group. -/
def determinant : AdelicGL K n →ₜ* IdeleGroup (𝓞 K) K where
  __ := Matrix.GeneralLinearGroup.det
  continuous_toFun := Matrix.GeneralLinearGroup.continuous_det

/-- Scalar ideles act by scalar matrices. -/
def scalar : IdeleGroup (𝓞 K) K →ₜ* AdelicGL K n where
  __ := Matrix.GeneralLinearGroup.scalar (Fin n)
  continuous_toFun := by
    have h : Continuous (Matrix.scalar (Fin n) :
        AdeleRing (𝓞 K) K → Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) := by
      apply continuous_matrix
      intro i j
      change Continuous (fun a : AdeleRing (𝓞 K) K => if i = j then a else 0)
      split_ifs <;> fun_prop
    exact h.units_map

theorem scalar_commute (z : IdeleGroup (𝓞 K) K) (g : AdelicGL K n) :
    Commute (scalar K n z) g := by
  change scalar K n z * g = g * scalar K n z
  apply Units.ext
  exact Matrix.scalar_comm (z : AdeleRing (𝓞 K) K) (Commute.all _) g.val

end AdelicGL

end Langlands.Global
