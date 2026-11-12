import Langlands.Automorphic.CuspidalAdmissible.CasimirAnnihilator
import Langlands.Automorphic.CuspidalAdmissible.CompactCasimirAnnihilator
import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Representation.Unitary.Basic

/-!
# The energy bound for vectors killed by Casimir polynomials

Let `b` be a unitary form on a realization: real Lie operators `D_X` are skew for `b`.
Then `D_X²`, the Casimir operator and the compact Casimir operator are `b`-symmetric, and
for the normalized Cartan basis `X_i` the energy `∑ b(D_{X_i} e, D_{X_i} e)` equals
`-b(Ω e, e) - 2 b(Ω_K e, e)`. If `q(Ω) e = 0` and `p(Ω_K) e = 0` for nonzero polynomials
`q, p`, the Rayleigh bound gives

`∑ b(D_{X_i} e, D_{X_i} e) ≤ (rootBound q + 2 rootBound p) · b(e, e)`.
-/

noncomputable section

universe uF

open Polynomial

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.Automorphic

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance energyBoundRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance energyBoundContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance energyBoundSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance energyBoundFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance energyBoundStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

section Core

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : InnerProductSpace.Core ℂ V)

/-- `D` is skew for the Hermitian form `c`. -/
def IsCoreSkew (D : Module.End ℂ V) : Prop :=
  ∀ f g, c.inner (D f) g = -c.inner f (D g)

/-- `T` is symmetric for the Hermitian form `c`. -/
def IsCoreSymm (T : Module.End ℂ V) : Prop :=
  ∀ f g, c.inner (T f) g = c.inner f (T g)

variable {c}

theorem IsCoreSymm.add {T T' : Module.End ℂ V} (hT : IsCoreSymm c T) (hT' : IsCoreSymm c T') :
    IsCoreSymm c (T + T') := by
  intro f g
  have h1 : c.inner ((T + T') f) g = c.inner (T f) g + c.inner (T' f) g := c.add_left _ _ _
  have h2 : c.inner f ((T + T') g) = c.inner f (T g) + c.inner f (T' g) := by
    rw [← c.conj_inner_symm, LinearMap.add_apply, c.add_left, map_add, c.conj_inner_symm,
      c.conj_inner_symm]
  rw [h1, h2, hT, hT']

theorem IsCoreSymm.neg {T : Module.End ℂ V} (hT : IsCoreSymm c T) : IsCoreSymm c (-T) := by
  intro f g
  have h1 : c.inner ((-T) f) g = -c.inner (T f) g := by
    rw [LinearMap.neg_apply, ← neg_one_smul ℂ (T f), c.smul_left]
    simp
  have h2 : c.inner f ((-T) g) = -c.inner f (T g) := by
    rw [← c.conj_inner_symm, LinearMap.neg_apply, ← neg_one_smul ℂ (T g), c.smul_left]
    simp [c.conj_inner_symm]
  rw [h1, h2, hT]

theorem IsCoreSymm.sub {T T' : Module.End ℂ V} (hT : IsCoreSymm c T) (hT' : IsCoreSymm c T') :
    IsCoreSymm c (T - T') := by
  rw [sub_eq_add_neg]
  exact hT.add hT'.neg

theorem inner_zero_left_core (y : V) : c.inner 0 y = 0 := by
  rw [← zero_smul ℂ (0 : V), c.smul_left]
  simp

theorem inner_zero_right_core (y : V) : c.inner y 0 = 0 := by
  rw [← c.conj_inner_symm, inner_zero_left_core, map_zero]

theorem IsCoreSymm.zero : IsCoreSymm c (0 : Module.End ℂ V) := by
  intro f g
  simp only [LinearMap.zero_apply, inner_zero_left_core, inner_zero_right_core]

theorem IsCoreSkew.mul_self {D : Module.End ℂ V} (hD : IsCoreSkew c D) :
    IsCoreSymm c (D * D) := by
  intro f g
  rw [Module.End.mul_apply, Module.End.mul_apply, hD, hD, neg_neg]

theorem isCoreSymm_sum_sq {ι : Type*} (D : ι → Module.End ℂ V) (hD : ∀ i, IsCoreSkew c (D i))
    (s : Finset ι) : IsCoreSymm c (∑ i ∈ s, D i * D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsCoreSymm.zero : IsCoreSymm c (0 : Module.End ℂ V))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hD a).mul_self.add ih

theorem energy_eq_core {ι : Type*} (D : ι → Module.End ℂ V) (hD : ∀ i, IsCoreSkew c (D i))
    (s : Finset ι) (e : V) :
    ∑ i ∈ s, (c.inner (D i e) (D i e)).re = -(c.inner ((∑ i ∈ s, D i * D i) e) e).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inner_zero_left_core]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Finset.sum_insert ha, LinearMap.add_apply,
      Module.End.mul_apply, c.add_left, hD a (D a e) e, Complex.add_re, Complex.neg_re]
    ring

/-- The Rayleigh bound for a form given as an inner product core. -/
theorem norm_inner_le_of_aeval_core (T : Module.End ℂ V) (hT : IsCoreSymm c T) {q : ℂ[X]}
    (hq : q ≠ 0) {x : V} (hx : aeval T q x = 0) :
    ‖c.inner (T x) x‖ ≤ rootBound q * (c.inner x x).re := by
  let _ : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ c
  let _ : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have h := norm_inner_self_le_of_aeval T hT hq hx
  have hn : ‖x‖ ^ 2 = (c.inner x x).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  rw [hn] at h
  exact h

/-- **Energy bound (abstract form).** If `∑_{i ∈ s} D_i² = A + 2 B` with `A, B` symmetric
and `D_i` skew, and nonzero `q, p` kill `e` under `A` and `B`, then the energy
`∑ c(D_i e, D_i e)` is at most `(rootBound q + 2 rootBound p) · c(e, e)`. -/
theorem energy_le_core {ι : Type*} (D : ι → Module.End ℂ V) (hD : ∀ i, IsCoreSkew c (D i))
    (s : Finset ι) {A B : Module.End ℂ V} (hA : IsCoreSymm c A) (hB : IsCoreSymm c B)
    (hsum : ∑ i ∈ s, D i * D i = A + (2 : ℂ) • B) {q p : ℂ[X]} (hq : q ≠ 0) (hp : p ≠ 0)
    {e : V} (hqe : aeval A q e = 0) (hpe : aeval B p e = 0) :
    ∑ i ∈ s, (c.inner (D i e) (D i e)).re ≤
      ((rootBound q : ℝ) + 2 * rootBound p) * (c.inner e e).re := by
  have h1 := norm_inner_le_of_aeval_core A hA hq hqe
  have h2 := norm_inner_le_of_aeval_core B hB hp hpe
  rw [energy_eq_core D hD s e, hsum, LinearMap.add_apply, LinearMap.smul_apply, c.add_left,
    c.smul_left]
  have hre : (c.inner (A e) e + (starRingEnd ℂ) (2 : ℂ) * c.inner (B e) e).re =
      (c.inner (A e) e).re + 2 * (c.inner (B e) e).re := by
    simp [Complex.add_re, Complex.mul_re]
  rw [hre]
  have r1 := (neg_le_abs (c.inner (A e) e).re).trans (Complex.abs_re_le_norm _)
  have r2 := (neg_le_abs (c.inner (B e) e).re).trans (Complex.abs_re_le_norm _)
  have hpos : 0 ≤ (c.inner e e).re := c.re_inner_nonneg e
  nlinarith

end Core

variable (S : OperatorRealization F n)

local instance energyBoundSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The real Lie operator `D_X` of a realization. -/
abbrev realOperator (X : ArchimedeanGL.RealLieAlgebra F n) : Module.End ℂ S.Space :=
  S.envelopingAction (ArchimedeanGL.realEnvelopingGenerator F n X)

/-- The sum of squares `∑_{i ∈ s} D_{X_i}²`. -/
abbrev squareSumOperator {ι : Type*} (s : Finset ι)
    (X : ι → ArchimedeanGL.RealLieAlgebra F n) : Module.End ℂ S.Space :=
  ∑ i ∈ s, realOperator S (X i) * realOperator S (X i)

theorem envelopingAction_sum_sq {ι : Type*} (s : Finset ι)
    (X : ι → ArchimedeanGL.RealLieAlgebra F n) :
    S.envelopingAction (∑ i ∈ s, ArchimedeanGL.realEnvelopingGenerator F n (X i) *
      ArchimedeanGL.realEnvelopingGenerator F n (X i)) = squareSumOperator S s X :=
  (map_sum S.envelopingAction _ s).trans
    (Finset.sum_congr rfl fun _ _ => map_mul S.envelopingAction _ _)

theorem casimirOperator_eq :
    casimirOperator S =
      squareSumOperator S Finset.univ
          (fun i => (ArchimedeanGL.complementaryCartanBasis F n i :
            ArchimedeanGL.RealLieAlgebra F n)) -
        squareSumOperator S Finset.univ
          (fun i => (ArchimedeanGL.compactCartanBasis F n i :
            ArchimedeanGL.RealLieAlgebra F n)) :=
  (congrArg S.envelopingAction (ArchimedeanGL.matrixCasimir_eq_complementary_sub_compact F n)).trans
    ((map_sub S.envelopingAction _ _).trans
      (congrArg₂ (· - ·) (envelopingAction_sum_sq S _ _) (envelopingAction_sum_sq S _ _)))

theorem compactCasimirOperator_eq_squareSum :
    compactCasimirOperator S =
      squareSumOperator S Finset.univ
        (fun i => (ArchimedeanGL.compactCartanBasis F n i :
          ArchimedeanGL.RealLieAlgebra F n)) :=
  envelopingAction_sum_sq S _ _

theorem cartanSquareSum_eq :
    squareSumOperator S Finset.univ (ArchimedeanGL.cartanAdaptedBasis F n) =
      casimirOperator S + (2 : ℂ) • compactCasimirOperator S :=
  (envelopingAction_sum_sq S _ _).symm.trans
    ((congrArg S.envelopingAction
      (ArchimedeanGL.cartanSquareSum_eq_casimir_add_twice_compact F n)).trans
      ((map_add S.envelopingAction _ _).trans
        (congrArg₂ (· + ·) rfl (map_smul S.envelopingAction _ _))))

variable {S} (b : S.UnitaryForm)

theorem isCoreSkew_realOperator (X : ArchimedeanGL.RealLieAlgebra F n) :
    IsCoreSkew b.finiteForm.toInnerProductCore (realOperator S X) :=
  fun f g => eq_neg_of_add_eq_zero_left (b.real_skew X f g)

theorem isCoreSymm_casimirOperator :
    IsCoreSymm b.finiteForm.toInnerProductCore (casimirOperator S) :=
  (congrArg (IsCoreSymm b.finiteForm.toInnerProductCore) (casimirOperator_eq S)).mpr
    ((isCoreSymm_sum_sq _ (fun _ => isCoreSkew_realOperator b _) _).sub
      (isCoreSymm_sum_sq _ (fun _ => isCoreSkew_realOperator b _) _))

theorem isCoreSymm_compactCasimirOperator :
    IsCoreSymm b.finiteForm.toInnerProductCore (compactCasimirOperator S) :=
  (congrArg (IsCoreSymm b.finiteForm.toInnerProductCore)
    (compactCasimirOperator_eq_squareSum S)).mpr
    (isCoreSymm_sum_sq _ (fun _ => isCoreSkew_realOperator b _) _)

/-- The energy of `e` along the normalized Cartan basis. -/
def energy (e : S.Space) : ℝ :=
  ∑ i, (b.inner (realOperator S (ArchimedeanGL.cartanAdaptedBasis F n i) e)
    (realOperator S (ArchimedeanGL.cartanAdaptedBasis F n i) e)).re

/-- **Energy bound.** If nonzero polynomials `q` and `p` kill `e` under the Casimir and the
compact Casimir operators, the energy of `e` along the normalized Cartan basis is at most
`(rootBound q + 2 rootBound p) · b(e, e)`. -/
theorem energy_le {q p : ℂ[X]} (hq : q ≠ 0) (hp : p ≠ 0) {e : S.Space}
    (hqe : aeval (casimirOperator S) q e = 0)
    (hpe : aeval (compactCasimirOperator S) p e = 0) :
    energy b e ≤ ((rootBound q : ℝ) + 2 * rootBound p) * (b.inner e e).re :=
  energy_le_core (fun i => realOperator S (ArchimedeanGL.cartanAdaptedBasis F n i))
    (fun _ => isCoreSkew_realOperator b _) Finset.univ (isCoreSymm_casimirOperator b)
    (isCoreSymm_compactCasimirOperator b) (cartanSquareSum_eq S) hq hp hqe hpe

end Langlands.Automorphic.CuspidalAdmissible
