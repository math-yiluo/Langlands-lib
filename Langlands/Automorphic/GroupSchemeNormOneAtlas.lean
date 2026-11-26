import Langlands.Automorphic.GroupSchemeNormOneSmooth
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.Global.InfiniteAdelicLinearRealization
import Langlands.Geometry.Manifold.LinearLieGroup.ClosedSubgroupImmersion

/-! # The embedded Lie atlas of `G(F∞)¹`

For a connected reductive group `G` over a number field `F`, the actual archimedean norm-one
subgroup `G(F∞)¹` is a closed subgroup of the real Lie group `G(F∞)`, and `G(F∞)` has a closed
linear realization. The closed-subgroup construction of
`Langlands.Geometry.Manifold.LinearLieGroup.ClosedSubgroupImmersion` therefore gives an embedded
Lie atlas `NormOneLieAtlas` on `G(F∞)¹` (`exists_normOneLieAtlas`). The module also proves that,
for an open level, every function satisfying `IsNormOneCr` is continuous on `G(𝔸_F)¹`
(`continuous_of_isNormOneCr`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme

section Continuity

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d e : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}

/-- A norm-one point whose finite component lies in a compact subgroup `K₀` has its infinite
component in `G(F∞)¹`. -/
theorem ofInfinite_infinite_mem_normOneSubgroup (K₀ : Subgroup (FiniteAdelicGroupPoints F G))
    (hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))) (z : normOneSubgroup F G)
    (hz : finite F G z ∈ K₀) :
    infinite F G z ∈ infiniteNormOneSubgroup F G := by
  change ofInfinite F G (infinite F G z) ∈ normOneSubgroup F G
  have hk : ofFinite F G (finite F G z) ∈ normOneSubgroup F G :=
    (finiteLevelInclusion F G K₀ hK₀ ⟨_, hz⟩).property
  have heq : ofInfinite F G (infinite F G z) =
      (z : AdelicGroupPoints F G) * (ofFinite F G (finite F G z))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one,
      one_mul, pair_projections]
  rw [heq]
  exact mul_mem z.property (inv_mem hk)

/-- A norm-one point `y` is `x` times its infinite and finite relative components. -/
theorem mul_ofInfinite_mul_ofFinite (x y : AdelicGroupPoints F G) :
    x * ofInfinite F G (infinite F G (x⁻¹ * y)) * ofFinite F G (finite F G (x⁻¹ * y)) = y := by
  rw [mul_assoc, ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul,
    pair_projections, mul_inv_cancel_left]

/-- **Continuity of fixed-level functions.** For an open level `K₀`, a function satisfying
`IsNormOneCr` (of any order) is continuous on `G(𝔸_F)¹`. Near `x`, every norm-one point is
`x · a · k` with `a ∈ G(F∞)¹` depending continuously on the point and `k ∈ K₀`, so the
function agrees with the continuous slice `a ↦ f(x a)`. -/
theorem continuous_of_isNormOneCr (A : NormOneLieAtlas F G hsmooth e) {r : WithTop ℕ∞}
    {K₀ : Subgroup (FiniteAdelicGroupPoints F G)}
    {hK₀ : IsCompact (K₀ : Set (FiniteAdelicGroupPoints F G))}
    (hopen : IsOpen (K₀ : Set (FiniteAdelicGroupPoints F G)))
    {f : normOneSubgroup F G → ℂ} (hf : IsNormOneCr A r K₀ hK₀ f) : Continuous f := by
  let := A.chartedSpace
  refine continuous_iff_continuousAt.2 fun x => ?_
  -- the relative point `x⁻¹ y` and its open neighbourhood condition
  let z : normOneSubgroup F G → normOneSubgroup F G := fun y => x⁻¹ * y
  have hz : Continuous z := continuous_const.mul continuous_id
  let U : Set (normOneSubgroup F G) := {y | finite F G (z y : AdelicGroupPoints F G) ∈ K₀}
  have hU : IsOpen U :=
    hopen.preimage ((finite F G).continuous.comp (continuous_subtype_val.comp hz))
  have hxU : x ∈ U := by
    change finite F G ((x⁻¹ * x : normOneSubgroup F G) : AdelicGroupPoints F G) ∈ K₀
    rw [inv_mul_cancel]
    exact (map_one (finite F G)).symm ▸ K₀.one_mem
  have hcont : ContinuousOn f U := by
    rw [continuousOn_iff_continuous_domRestrict]
    let a : U → infiniteNormOneSubgroup F G := fun y =>
      ⟨infinite F G (z y : AdelicGroupPoints F G),
        ofInfinite_infinite_mem_normOneSubgroup K₀ hK₀ (z y) y.property⟩
    have ha : Continuous a :=
      ((infinite F G).continuous.comp
        (continuous_subtype_val.comp (hz.comp continuous_subtype_val))).subtype_mk _
    have heq : U.domRestrict f = normOneInfiniteSlice F G f x ∘ a := by
      funext y
      have hy : (y : normOneSubgroup F G) =
          x * infiniteNormOneInclusion F G (a y) *
            finiteLevelInclusion F G K₀ hK₀ ⟨_, y.property⟩ := by
        apply Subtype.ext
        exact (mul_ofInfinite_mul_ofFinite (x : AdelicGroupPoints F G)
          ((y : normOneSubgroup F G) : AdelicGroupPoints F G)).symm
      change f y = f (x * infiniteNormOneInclusion F G (a y))
      conv_lhs => rw [hy]
      exact hf.2.1 _ _
    rw [heq]
    exact (hf.2.2 x).continuous.comp ha
  exact hcont.continuousAt (hU.mem_nhds hxU)

end Continuity

section Existence

open NumberField
open scoped Classical Matrix.Norms.Operator

/-- **The embedded Lie atlas of `G(F∞)¹`.** For every number field `F` and every connected
reductive `F`-group `G`, the actual infinite norm-one subgroup carries a `NormOneLieAtlas` for
the Library's atlas of `G(F∞)`. The charts are the exponential charts of the image of `G(F∞)¹`
under a closed linear realization of `G(F∞)`, read in a basis of its Lie algebra. -/
theorem exists_normOneLieAtlas (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    letI := hG.affineScheme
    ∃ e : ℕ, Nonempty (NormOneLieAtlas F G hG.smoothDimension_spec e) := by
  let := hG.affineScheme
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG
  have := InfiniteAdelicGroupPoints.reductiveIsManifold F G hG
  obtain ⟨N, ρ, hρ⟩ := InfiniteAdelicGroupPoints.exists_isClosedLinearRealization F G hG
  have hS := isClosed_infiniteNormOneSubgroup F G
  exact ⟨hρ.subgroupDim hS, ⟨{
    chartedSpace := hρ.subgroupChartedSpace hS
    isManifold := hρ.subgroupIsManifold hS ∞
    lieGroup := hρ.subgroupLieGroup hS ∞
    immersion := hρ.isImmersion_subtype hS }⟩⟩

/-- The model dimension of the embedded Lie atlas `normOneLieAtlas`, the dimension of `G(F∞)¹`. -/
def normOneLieDim (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) : ℕ :=
  (exists_normOneLieAtlas F G hG).choose

/-- **An embedded Lie atlas of `G(F∞)¹`**, chosen by `exists_normOneLieAtlas`. -/
def normOneLieAtlas (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    letI := hG.affineScheme
    NormOneLieAtlas F G hG.smoothDimension_spec (normOneLieDim F G hG) :=
  letI := hG.affineScheme
  (exists_normOneLieAtlas F G hG).choose_spec.some

end Existence

end Langlands.Automorphic.GroupSchemeFunctions
