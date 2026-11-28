import Langlands.Global.Factors.CuspidalPairEisensteinArchimedeanNumeratorStatement
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerIdentityEvaluation

/-! # The archimedean Jacquet integral for a pair of cuspidal Whittaker spaces

The inducing spaces are obtained by evaluating the cuspidal Whittaker coefficients at the
identity finite component. The scalar section of normalized archimedean induction varies over
the full smooth compact-finite space. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open scoped Classical Matrix.Norms.Operator

namespace Langlands.Global

open MeasureTheory NumberField Automorphic RankinSelbergGlobal
open RankinSelbergGlobal.ArchimedeanWhittakerEvaluation (coefficient)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

namespace CuspidalPairEisenstein.ArchimedeanJacquet

variable {F : Type u} [Field F] [NumberField F]

private local instance (m : ℕ) : AddCommGroup (RationalInvariantFunctions F m) :=
  Submodule.addCommGroup _
private local instance (m : ℕ) : AddCommGroup (ContinuousRationalFunctions F m) :=
  Submodule.addCommGroup _
private local instance (m : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F m) :=
  Submodule.addCommGroup _
private local instance (m : ℕ) : AddCommGroup (AutomorphicForms F m) := Submodule.addCommGroup _
private local instance (m : ℕ) : AddCommGroup (StableAutomorphicFunctions F m) :=
  Submodule.addCommGroup _
private local instance {n : ℕ} (R : OperatorRealization F n) : AddCommGroup R.Space :=
  Submodule.addCommGroup _

set_option maxHeartbeats 2000000 in
/-- The vectors of a cuspidal realization spherical at each finite place outside `S`. -/
def sphericalSubmodule [CompactSpace (AdeleQuotient F)] {n : ℕ}
    (T : CuspidalOperatorRealization F n) (S : Finset (FinitePlace F)) : Submodule ℂ T.Space where
  carrier := {x | RankinSelbergGlobal.IsSphericalOutside F T S x}
  add_mem' hx hy v hv k hk := by rw [map_add, hx v hv k hk, hy v hv k hk]
  zero_mem' v _ k _ := map_zero _
  smul_mem' c x hx v hv k hk := by rw [map_smul, hx v hv k hk]

/-- The space of Whittaker coefficients at finite argument `1` of cusp vectors spherical
outside `S`, regarded as smooth functions on the full archimedean group. -/
def whittakerSpace [CompactSpace (AdeleQuotient F)] {n : ℕ} (T : CuspidalOperatorRealization F n)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (S : Finset (FinitePlace F)) :
    Submodule ℂ (ArchimedeanGL.SmoothFunctions F (n + 1)) :=
  (sphericalSubmodule T S).map (coefficient T ψ hψ 1)

variable {r t : ℕ}

/-- The span of products of functions from the two inducing Whittaker spaces, as functions
on the archimedean Levi. -/
def leviWhittakerSpace (W : Submodule ℂ (ArchimedeanGL.SmoothFunctions F (r + 1)))
    (W' : Submodule ℂ (ArchimedeanGL.SmoothFunctions F (t + 1))) :
    Submodule ℂ (InfiniteLevi F (blockShape r t) → ℂ) :=
  Submodule.span ℂ (Set.range fun w : W × W' => fun m : InfiniteLevi F (blockShape r t) =>
    w.1.val.val (m (0 : Fin 2)) * w.2.val.val (m (1 : Fin 2)))

/-- The normalized slice `m ↦ δ_P(m)^(-1/2) f(m k)`, with the modulus restricted to the
archimedean Levi. -/
def infiniteNormalizedSlice (f : InfiniteAdelicGL F (r + t + 2) → ℂ)
    (k : InfiniteAdelicGL F (r + t + 2)) (m : InfiniteLevi F (blockShape r t)) : ℂ :=
  (leviHalfCharacter F (blockShape r t) (AdelicBlockParabolic.leviPair F (blockShape r t) m 1) : ℂ)⁻¹ *
    f ((blockShape r t).leviEmbedding (InfiniteAdeleRing F) m * k)

/-- The right compact action on smooth functions on the archimedean group. -/
def compactRightAction (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    Representation ℂ (standardInfiniteCompact F n) (ArchimedeanGL.SmoothFunctions F n) :=
  (ArchimedeanGL.smoothRightAction F n).comp (standardInfiniteCompact F n).subtype

/-- Scalar form of a smooth `K_∞`-finite section of normalized induction from `W`. Its
left `U_P(F_∞)` invariance and normalized slices describe the inducing values. -/
def IsInducedSection (W : Submodule ℂ (InfiniteLevi F (blockShape r t) → ℂ))
    (f : ArchimedeanGL.SmoothFunctions F (r + t + 2)) : Prop :=
  (∀ (v : (blockShape r t).unipotentRadical (InfiniteAdeleRing F))
    (g : InfiniteAdelicGL F (r + t + 2)), f.val (v.val.val * g) = f.val g) ∧
  (∀ k : standardInfiniteCompact F (r + t + 2), infiniteNormalizedSlice f.val k.val ∈ W) ∧
  FiniteVectors.IsFiniteVector (compactRightAction F (r + t + 2)) f

/-- The Jacquet integrand `f(w_∞ u'(X)) H(w_∞ u'(X))^s conj(ψ_∞(u'(X)))`. The height
is evaluated at finite component `1`. The adelic matrix used in the additive phase has
vanishing finite component in every entry of its rectangular parameter. -/
def jacquetIntegrand (ψ : AddChar (Adeles F) ℂ) (f : InfiniteAdelicGL F (r + t + 2) → ℂ) (s : ℂ)
    (X : Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) : ℂ :=
  let v := openCellUnipotent F r t (archimedeanMatrix F r t X)
  let g := AdelicGL.infinite F (r + t + 2) (openCellWeyl F r t * v)
  f g * heightPower F r t s (AdelicGL.ofInfinite F (r + t + 2) g) *
    starRingEnd ℂ (ψ (∑ i : Fin (r + t + 1),
      (v : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) i.castSucc i.succ))

end CuspidalPairEisenstein.ArchimedeanJacquet

open CuspidalPairEisenstein CuspidalPairEisenstein.ArchimedeanJacquet

/-- For the nonzero archimedean Whittaker spaces of two actual cuspidal realizations with
unitary central characters (using the contragredient of the second), there is, at every
`Re s₀ = 0`, a smooth compact-finite section whose Jacquet integral converges absolutely on
a right half-plane and agrees there with a meromorphic function analytic and nonzero at `s₀`. -/
def CuspidalPairEisensteinArchimedeanJacquetStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (S : Finset (FinitePlace F)),
    let W := whittakerSpace T ψ hψ S
    let W' := whittakerSpace (dualRealization T') ψ hψ S
    W ≠ ⊥ → W' ≠ ⊥ →
  ∀ s₀ : ℂ, s₀.re = 0 →
    ∃ f : ArchimedeanGL.SmoothFunctions F (r + t + 2), IsInducedSection (leviWhittakerSpace W W') f ∧
      ∃ c : ℂ → ℂ, MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧
        ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
          (letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :=
              borel _;
            Integrable (jacquetIntegrand ψ f.val s) (archimedeanOpenCellHaar F r t)) ∧
          c s = (letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (InfiniteAdeles F)) :=
              borel _;
            ∫ X, jacquetIntegrand ψ f.val s X ∂(archimedeanOpenCellHaar F r t))

end Langlands.Global
