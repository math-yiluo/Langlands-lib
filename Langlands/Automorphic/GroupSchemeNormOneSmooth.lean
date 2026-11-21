import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicGroupRationalTopology
import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Geometry.Manifold.LieGroupEllipticEstimateStatement
import Mathlib.Geometry.Manifold.Immersion

/-! # Fixed-level differentiability on the norm-one adelic group

Use the actual infinite subgroup with trivial ambient character norms. At each norm-one point,
its positive right orbit is the fibre of the finite component. For an embedded Lie atlas on this
subgroup, define the `Cʳ` condition along those fibres, together with the rational invariance and
fixed open compact level. The derivative operators are finite combinations of actual invariant
word derivatives. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

/-- Arthur's `G(F∞)¹`, inside the actual infinite adelic group. -/
def infiniteNormOneSubgroup : Subgroup (InfiniteAdelicGroupPoints F G) :=
  (normOneSubgroup F G).comap (ofInfinite F G).toMonoidHom

/-- Include this subgroup as actual norm-one adelic points. -/
def infiniteNormOneInclusion : infiniteNormOneSubgroup F G →* normOneSubgroup F G where
  toFun a := ⟨ofInfinite F G a, a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (ofInfinite F G) a.val b.val)

/-- The infinite norm-one subgroup is closed in the actual infinite adelic group. -/
theorem isClosed_infiniteNormOneSubgroup :
    IsClosed (infiniteNormOneSubgroup F G : Set (InfiniteAdelicGroupPoints F G)) :=
  (isClosed_normOneSubgroup F G).preimage (ofInfinite F G).continuous

/-- Positive right translation by the included infinite subgroup stays in the same finite fibre. -/
theorem finite_mul_infiniteNormOneInclusion (x : normOneSubgroup F G)
    (a : infiniteNormOneSubgroup F G) :
    finite F G ((x * infiniteNormOneInclusion F G a : normOneSubgroup F G) :
      AdelicGroupPoints F G) = finite F G x := by
  change finite F G ((x : AdelicGroupPoints F G) * ofInfinite F G a) = _
  rw [map_mul, finite_ofInfinite, mul_one]

/-- Every point of the same finite fibre is obtained from this right orbit. -/
theorem exists_mul_infiniteNormOneInclusion {x y : normOneSubgroup F G}
    (hxy : finite F G x = finite F G y) :
    ∃ a : infiniteNormOneSubgroup F G, x * infiniteNormOneInclusion F G a = y := by
  let z : normOneSubgroup F G := x⁻¹ * y
  have hz : finite F G z = 1 := by
    change finite F G ((x : AdelicGroupPoints F G)⁻¹ * (y : AdelicGroupPoints F G)) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h : ofInfinite F G (infinite F G z) = (z : AdelicGroupPoints F G) := by
    rw [ofInfinite_eq_pair, ← hz, pair_projections]
  refine ⟨⟨infinite F G z, ?_⟩, ?_⟩
  · change ofInfinite F G (infinite F G z) ∈ normOneSubgroup F G
    rw [h]
    exact z.property
  · apply Subtype.ext
    change (x : AdelicGroupPoints F G) * ofInfinite F G (infinite F G z) = y
    rw [h]
    exact mul_inv_cancel_left _ _

/-- The finite levels in the source act inside `G(𝔸)¹`: all compact subgroups have trivial
ambient logarithmic character norms. -/
def finiteLevelInclusion (K₀ : Subgroup (FiniteAdelicGroupPoints F G))
    (hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))) : K₀ →* normOneSubgroup F G where
  toFun k := ⟨ofFinite F G k, compactSubgroup_le_normOneSubgroup F G
    (K₀.map (ofFinite F G).toMonoidHom) (hK₀.image (ofFinite F G).continuous)
    ⟨k.val, k.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul (ofFinite F G) a.val b.val)

/-- Data for the induced finite-dimensional smooth Lie structure of `G(F∞)¹`. The inclusion in
the ambient infinite adelic manifold is an immersion and has the inherited topology. -/
structure NormOneLieAtlas {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) (e : ℕ) where
  chartedSpace : ChartedSpace (Fin e → ℝ) (infiniteNormOneSubgroup F G)
  isManifold : letI := chartedSpace
    IsManifold 𝓘(ℝ, Fin e → ℝ) ∞ (infiniteNormOneSubgroup F G)
  lieGroup : letI := chartedSpace
    LieGroup 𝓘(ℝ, Fin e → ℝ) ∞ (infiniteNormOneSubgroup F G)
  immersion : letI := chartedSpace
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    _root_.Manifold.IsImmersion 𝓘(ℝ, Fin e → ℝ) 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      ((↑) : infiniteNormOneSubgroup F G → InfiniteAdelicGroupPoints F G)

/-- The function on the infinite norm-one group given by the slice through a norm-one adelic
point `x`. This parametrizes the whole fibre of the finite projection at `x`. -/
def normOneInfiniteSlice (f : normOneSubgroup F G → ℂ) (x : normOneSubgroup F G)
    (a : infiniteNormOneSubgroup F G) : ℂ :=
  f (x * infiniteNormOneInclusion F G a)

variable {F G} {d e : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}

/-- The pullback form of `Cʳ(G(F) \ G(𝔸)¹ / K₀)`, for an open compact `K₀`. -/
def IsNormOneCr (A : NormOneLieAtlas F G hsmooth e) (r : WithTop ℕ∞)
    (K₀ : Subgroup (FiniteAdelicGroupPoints F G))
    (hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G)))
    (f : normOneSubgroup F G → ℂ) : Prop :=
  letI := A.chartedSpace
  (∀ (γ : rationalNormOneSubgroup F G) x, f ((γ : normOneSubgroup F G) * x) = f x) ∧
    (∀ (k : K₀) x, f (x * finiteLevelInclusion F G K₀ hK₀ k) = f x) ∧
    ∀ x, ContMDiff 𝓘(ℝ, Fin e → ℝ) 𝓘(ℝ, ℂ) r (normOneInfiniteSlice F G f x)

/-- Coefficients for a finite complex combination of differential words in the coordinate tangent
basis at the identity of `G(F∞)¹`. The filtration is by word length. -/
abbrev NormOneDifferentialWord (e : ℕ) := MonoidAlgebra ℂ (FreeMonoid (Fin e))

/-- All words with nonzero coefficient have length at most `r`. -/
def NormOneDifferentialWord.OrderLE (D : NormOneDifferentialWord e) (r : ℕ) : Prop :=
  ∀ w ∈ D.coeff.support, w.length ≤ r

/-- Evaluate the left-invariant differential operator along the positive right orbit of `x`.
The word algebra is used rather than requiring an enveloping action on a fixed finite `Cʳ` space:
a word of length `s ≤ r` differentiates an input of class `Cʳ` to class `Cʳ⁻ˢ`. -/
def normOneDifferential (A : NormOneLieAtlas F G hsmooth e) (D : NormOneDifferentialWord e)
    (f : normOneSubgroup F G → ℂ) (x : normOneSubgroup F G) : ℂ :=
  letI := A.chartedSpace
  letI := A.lieGroup
  lieWordAction (fun j => Pi.single j (1 : ℝ)) D (normOneInfiniteSlice F G f x) 1

end Langlands.Automorphic.GroupSchemeFunctions
