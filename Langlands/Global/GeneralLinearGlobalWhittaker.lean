import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.GeneralLinearSmoothProof

/-! # Global Whittaker functions on `GL_n`

Character coefficients `∫_{U(F) \ U(𝔸)} f(u g) conj(χ(u)) du` along a subgroup functor with
closed adelic points, the upper unitriangular subgroup functor `N_n` of the general linear
group scheme, the generic characters `n ↦ ψ(m₀ n_{0,1} + ⋯ + m_{r-1} n_{r-1,r})` of
`N_{r+1}(𝔸)` (Getz–Hahn, Example 11.1), the global Whittaker function
`W_f(g) = ∫_{N(F) \ N(𝔸)} f(n g) conj(ψ_N(n)) dn` (Getz–Hahn (11.6)), the coset space
`N_r(F) \ GL_r(F)` and the points `diag(γ, 1)` of `GL_{r+1}(𝔸)`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme

section Coefficient

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (U : SubgroupFunctor G)
  [IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G))]

/-- The `χ`-coefficient `∫_{U(F) \ U(𝔸)} f(u g) conj(χ(u)) du` of a function `f` on `G(𝔸)`
along a subgroup functor `U` with closed adelic points, for a function `χ` on `U(𝔸)`. The
integrand is evaluated at the chosen representative `u ∈ U(𝔸)` of each class, and the measure
is the quotient Haar measure scaled to total mass one when it is finite
(`normalizedRationalQuotientHaarMeasure`). For `f` left invariant under `U(F)` and `χ` a
character trivial on `U(F)` the integrand does not depend on the representatives. The integral
is `0` where the integrand is not integrable. -/
def subgroupCharacterCoefficient (χ : AdelicSubgroupPoints.adelicPoints F G U → ℂ)
    (f : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) : ℂ :=
  ∫ x, f (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G U) :
      AdelicGroupPoints F G) * g) * starRingEnd ℂ (χ (Quotient.out x))
    ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U

end Coefficient

section Corner

variable {R : Type*} [CommRing R]

/-- The block-diagonal matrix `diag(A, 1)` of size `r + 1`, as a monoid homomorphism. -/
def cornerMatrix (r : ℕ) : Matrix (Fin r) (Fin r) R →* Matrix (Fin (r + 1)) (Fin (r + 1)) R where
  toFun A := Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) R))
  map_one' := by simp
  map_mul' A B := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

/-- The embedding `γ ↦ diag(γ, 1)` of `GL_r` into `GL_{r+1}`. -/
def cornerEmbedding (r : ℕ) :
    Matrix.GeneralLinearGroup (Fin r) R →* Matrix.GeneralLinearGroup (Fin (r + 1)) R :=
  Units.map (cornerMatrix r)

end Corner

section GeneralLinear

local instance whittakerGeneralLinearIsAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance whittakerGeneralLinearSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The weights `i ↦ -i`: the block unipotent subgroup for them is the upper unitriangular
group. -/
def upperUnipotentWeight (n : ℕ) : Fin n → ℤ := fun i => -(i : ℤ)

variable (F : Type u) [Field F] [NumberField F]

/-- The upper unitriangular subgroup functor `N_n` of `GL_n` over `F`: points whose matrix has
the entries of the identity at every position `(i, j)` with `j ≤ i`. -/
abbrev upperUnipotent (n : ℕ) :
    SubgroupFunctor (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) :=
  GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F) (upperUnipotentWeight n)

/-- `N_n(𝔸)` is closed in `GL_n(𝔸)`: `N_n` is represented by a closed subgroup scheme. -/
theorem isClosed_upperUnipotent_adelicPoints (n : ℕ) :
    IsClosed (AdelicSubgroupPoints.adelicPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (upperUnipotent F n) :
        Set (AdelicGroupPoints F
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))) := by
  let j := GroupScheme.GeneralLinear.blockUnipotentHom (Fin n) (CommRingCat.of F)
    (upperUnipotentWeight n)
  have hj := GroupScheme.GeneralLinear.isClosedSubgroup_blockUnipotentHom
    (Fin n) (CommRingCat.of F) (upperUnipotentWeight n)
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffine
      (GroupScheme.GeneralLinear.blockUnipotentScheme (Fin n) (CommRingCat.of F)
        (upperUnipotentWeight n)).X.left :=
    isAffine_of_isAffineHom j.hom.hom.left
  have hrange : SubgroupFunctor.range j = upperUnipotent F n :=
    (GroupScheme.GeneralLinear.isRepresentedBy_blockUnipotent
      (Fin n) (CommRingCat.of F) (upperUnipotentWeight n)).2
  rw [← hrange]
  exact AdelicSubgroupPoints.isClosed_adelicPoints_range F _ j

instance upperUnipotentAdelicPointsIsClosed (n : ℕ) :
    IsClosed (AdelicSubgroupPoints.adelicPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (upperUnipotent F n) :
        Set (AdelicGroupPoints F
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))) :=
  isClosed_upperUnipotent_adelicPoints F n

/-- The character `n ↦ ψ(m₀ n_{0,1} + ⋯ + m_{r-1} n_{r-1,r})` of `N_{r+1}(𝔸)` attached to an
additive character `ψ` of `𝔸` and `m : Fin r → F` (Getz–Hahn, Example 11.1); it is generic
when every `m i` is nonzero and `ψ` is nontrivial. -/
def genericCharacter (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (m : Fin r → F) :
    AdelicSubgroupPoints.adelicPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
      (upperUnipotent F (r + 1)) → ℂ :=
  fun x => ψ (∑ i : Fin r, algebraMap F (Adeles F) (m i) *
    (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (x : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i.castSucc i.succ)

/-- The global Whittaker function `W_f(g) = ∫_{N(F) \ N(𝔸)} f(n g) conj(ψ_N(n)) dn` on
`GL_{r+1}(𝔸)` (Getz–Hahn (11.6)), with the measure of total mass one. -/
def generalLinearWhittakerFunction (r : ℕ) (ψ : AddChar (Adeles F) ℂ) (m : Fin r → F)
    (f : AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) → ℂ) :
    AdelicGroupPoints F
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) → ℂ :=
  subgroupCharacterCoefficient F _ (upperUnipotent F (r + 1)) (genericCharacter F r ψ m) f

/-- `N_r(F)`, the rational points of `N_r`, as a subgroup of the rational matrices. -/
def rationalUpperUnipotent (r : ℕ) : Subgroup (RationalGL F r) :=
  (AdelicSubgroupPoints.rationalPoints F
    (GroupScheme.GeneralLinear.groupScheme (Fin r) (CommRingCat.of F))
    (upperUnipotent F r)).map (GeneralLinearGroupPoints.rationalEquiv F r).toMonoidHom

/-- The coset space `N_r(F) \ GL_r(F)` of right cosets `N_r(F) γ`. -/
abbrev UnipotentRationalCosets (r : ℕ) :=
  Quotient (QuotientGroup.rightRel (rationalUpperUnipotent F r))

/-- The adelic point `diag(γ, 1)` of `GL_{r+1}` for `γ ∈ GL_r(F)`. -/
def cornerAdelicPoint (r : ℕ) (γ : RationalGL F r) :
    AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) :=
  (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
    (AdelicGL.rational F (r + 1) (cornerEmbedding r γ))

end GeneralLinear

end Langlands.Global
