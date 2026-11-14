import Langlands.Automorphic.CuspidalOperatorRealization
import Langlands.Automorphic.GroupSchemeFiniteLevel
import Langlands.Global.GeneralLinearGlobalWhittaker
import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Group.GL.Maps
import Langlands.Group.GL.Mirabolic

/-! # Actual global Rankin–Selberg projections and unequal-rank integrals -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The actual general linear group scheme over the number field. -/
abbrev Scheme (F : Type u) [Field F] (n : ℕ) :=
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance schemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance schemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

/-- The group-scheme carrier used for global Whittaker coefficients. -/
abbrev Points (F : Type u) [Field F] [NumberField F] (n : ℕ) :=
  AdelicGroupPoints F (Scheme F n)

variable (F : Type u) [Field F] [NumberField F]

/-- Actual normalized determinant absolute value, written as a positive real number. -/
def detNorm (n : ℕ) (g : Points F n) : ℝ :=
  (((AdelicBlockDeterminantCharacter.determinantNorm F n
    (GeneralLinearGroupPoints.adelicEquiv F n g) : ℝ≥0ˣ) : ℝ≥0) : ℝ)

/-- Positive-real complex power; the logarithm is the real logarithm. -/
def detPower (n : ℕ) (g : Points F n) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (detNorm F n g) : ℂ))

section Padding
variable {R : Type*} [CommRing R]
/-- `A ↦ diag(A,I_k)`, with the first block occupying the first indices. -/
def padMatrix (m k : ℕ) :
    Matrix (Fin m) (Fin m) R →* Matrix (Fin (m + k)) (Fin (m + k)) R where
  toFun A := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin k) (Fin k) R))
  map_one' := by simp
  map_mul' A B := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

/-- Padding to an arbitrary larger rank. -/
def padGL {m n : ℕ} (h : m ≤ n) :
    Matrix.GeneralLinearGroup (Fin m) R →* Matrix.GeneralLinearGroup (Fin n) R :=
  (GeneralLinear.reindex (R := R) (finCongr (Nat.add_sub_of_le h))).toMonoidHom.comp
    (Units.map (padMatrix m (n - m)))
end Padding

/-- `diag(g,I_(n-m))` on actual adelic points. -/
def pad {m n : ℕ} (h : m ≤ n) (g : Points F m) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (padGL h (GeneralLinearGroupPoints.adelicEquiv F m g))

/-- Transpose inverse, the automorphism `ι(g)=ᵗg⁻¹`. -/
def iota (n : ℕ) (g : Points F n) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm
    (GeneralLinear.inverseTranspose n (Adeles F)
      (GeneralLinearGroupPoints.adelicEquiv F n g))

/-- The contragredient convention `φ̃(g)=φ(w_n ᵗg⁻¹)`. -/
def dualFunction (n : ℕ) (φ : Points F n → ℂ) (g : Points F n) : ℂ :=
  φ ((GeneralLinearGroupPoints.adelicEquiv F n).symm
    (GeneralLinear.weylLong n (Adeles F) * GeneralLinear.inverseTranspose n (Adeles F)
      (GeneralLinearGroupPoints.adelicEquiv F n g)))

/-- Weight constant on the initial block of size `m+1`, then strictly decreasing. -/
def projectionWeight (n m : ℕ) (i : Fin n) : ℤ := -((i.val - m : ℕ) : ℤ)

/-- The radical `Y_(n,m)` of type `(m+1,1,…,1)`. -/
abbrev projectionUnipotent (n m : ℕ) : GroupScheme.SubgroupFunctor (Scheme F n) :=
  GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F)
    (projectionWeight n m)

instance projectionUnipotentClosed (n m : ℕ) :
    IsClosed (AdelicSubgroupPoints.adelicPoints F (Scheme F n)
      (projectionUnipotent F n m) : Set (Points F n)) := by
  let j := GroupScheme.GeneralLinear.blockUnipotentHom (Fin n) (CommRingCat.of F)
    (projectionWeight n m)
  have hj := GroupScheme.GeneralLinear.isClosedSubgroup_blockUnipotentHom
    (Fin n) (CommRingCat.of F) (projectionWeight n m)
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffine
      (GroupScheme.GeneralLinear.blockUnipotentScheme (Fin n) (CommRingCat.of F)
        (projectionWeight n m)).X.left := isAffine_of_isAffineHom j.hom.hom.left
  have hrange : GroupScheme.SubgroupFunctor.range j = projectionUnipotent F n m :=
    (GroupScheme.GeneralLinear.isRepresentedBy_blockUnipotent
      (Fin n) (CommRingCat.of F) (projectionWeight n m)).2
  rw [← hrange]
  exact AdelicSubgroupPoints.isClosed_adelicPoints_range F _ j

/-- Restriction of the standard character of `N_(r+1)` to `Y_(r+1,m)`. -/
def projectionCharacter (r m : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (y : AdelicSubgroupPoints.adelicPoints F (Scheme F (r + 1))
      (projectionUnipotent F (r + 1) m)) : ℂ :=
  ψ (∑ i : Fin r, (GeneralLinearGroupPoints.adelicEquiv F (r + 1) y.val)
    i.castSucc i.succ)

/-- `P^n_m φ`: the displayed compact-quotient integral, extended to all `GL_(m+1)`.
Its restriction to the mirabolic is Cogdell's projection. No continuation is used. -/
def projection {r m : ℕ} (h : m < r + 1) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (p : Points F (m + 1)) : ℂ :=
  detPower F (m + 1) p (-((r - m : ℕ) : ℂ) / 2) *
    subgroupCharacterCoefficient F (Scheme F (r + 1))
      (projectionUnipotent F (r + 1) m) (projectionCharacter F r m ψ) φ
      (pad F (Nat.succ_le_of_lt h) p)

/-- Conjugating the projection by transpose inverse gives `P̃=ι∘P∘ι`.
The character is kept as the parameter of the inner projection. -/
def dualProjection {r m : ℕ} (h : m < r + 1) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (p : Points F (m + 1)) : ℂ :=
  projection F h ψ (fun g => φ (iota F (r + 1) g)) (iota F (m + 1) p)

/-- The integrand of the unequal-rank global integral on `GL_m(F)\GL_m(𝔸)`. -/
def unequalIntegrand {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ)
    (q : AdelicGroupPoints.RationalQuotient F (Scheme F (t + 1))) : ℂ :=
  let g := q.out
  projection F (show t + 1 < r + 1 from Nat.succ_lt_succ h) ψ φ
    (pad F (Nat.le_succ (t + 1)) g) * φ' g * detPower F (t + 1) g (s - 1 / 2)

/-- The defining unequal-rank Bochner integral. Its convergence is a separate claim. -/
def unequalIntegral {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q, unequalIntegrand F h ψ φ φ' s q
    ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1))

/-- Integrand for the dual global integral. -/
def dualUnequalIntegrand {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ)
    (q : AdelicGroupPoints.RationalQuotient F (Scheme F (t + 1))) : ℂ :=
  let g := q.out
  dualProjection F (show t + 1 < r + 1 from Nat.succ_lt_succ h) ψ φ
    (pad F (Nat.le_succ (t + 1)) g) * φ' g * detPower F (t + 1) g (s - 1 / 2)

/-- The dual defining global integral `Ĩ(s;φ,φ')`. -/
def dualUnequalIntegral {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q, dualUnequalIntegrand F h ψ φ φ' s q
    ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1))

variable [CompactSpace (AdeleQuotient F)]
/-- The actual function of a cuspidal realized vector, via the existing comparison. -/
def cuspFunction {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (v : T.Space) : Points F (r + 1) → ℂ :=
  Automorphic.GroupSchemeFunctions.evaluate F (Scheme F (r + 1))
    ((Automorphic.GroupSchemeFunctions.continuousGeneralLinearEquiv F (r + 1)).symm
      (T.realization.toContinuous v))

/-- The Library global Whittaker coefficient with all simple-root coefficients one. -/
def cuspWhittaker {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (v : T.Space) : Points F (r + 1) → ℂ :=
  generalLinearWhittakerFunction F r ψ (fun _ => 1) (cuspFunction F T v)

end Langlands.Global.RankinSelbergGlobal
