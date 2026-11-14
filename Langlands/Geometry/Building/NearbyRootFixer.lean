import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.FacetClosureLipschitz
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.IntegerBuildingFacetPartition

/-! # Root fixers of nearby subsets in a facet closure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V P : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]

/-- Along any real affine line, bounded finiteness of the affine roots
makes the original point belong to the facet closure of every sufficiently
near parameter. No topology on the affine space is needed. -/
theorem eventually_mem_facetClosure_smul_vadd {Ψ : Set (P →ᵃ[ℝ] ℝ)}
    (hΨ : ∀ (x : P) (bound : Module.Dual ℝ V → ℝ),
      {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ bound ψ.linear}.Finite)
    (x : P) (v : V) :
    ∀ᶠ t : ℝ in 𝓝 0, x ∈ facetClosure Ψ (t • v +ᵥ x) := by
  let S := {ψ | ψ ∈ Ψ ∧ |ψ x| ≤ |ψ.linear v|}
  have hS : S.Finite := hΨ x fun a => |a v|
  have hnear : ∀ ψ ∈ S,
      ∀ᶠ t : ℝ in 𝓝 0, ψ x = 0 ∨ |ψ (t • v +ᵥ x) - ψ x| < |ψ x| := by
    intro ψ _
    by_cases hzero : ψ x = 0
    · exact Eventually.of_forall fun _ => Or.inl hzero
    · have hcont : Continuous (fun t : ℝ => t * ψ.linear v + ψ x) :=
        (continuous_id.mul_const _).add_const _
      have hlim : Tendsto (fun t : ℝ => t * ψ.linear v + ψ x) (𝓝 0) (𝓝 (ψ x)) := by
        simpa only [zero_mul, zero_add] using hcont.tendsto 0
      have hevent := hlim.eventually
        (Metric.ball_mem_nhds (ψ x) (abs_pos.2 hzero))
      filter_upwards [hevent] with t ht
      right
      simpa only [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add,
        Metric.mem_ball, Real.dist_eq] using ht
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
    have hevent : ∀ᶠ t : ℝ in 𝓝 0, t ∈ Metric.ball 0 1 :=
      Metric.ball_mem_nhds (0 : ℝ) one_pos
    filter_upwards [hevent] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  filter_upwards [hS.eventually_all.2 hnear, hsmall] with t ht htsmall
  intro ψ hψ
  have hlt : ψ x = 0 ∨ |ψ (t • v +ᵥ x) - ψ x| < |ψ x| := by
    by_cases hmem : ψ ∈ S
    · exact ht ψ hmem
    · right
      have hbig : |ψ.linear v| < |ψ x| :=
        lt_of_not_ge fun h => hmem ⟨hψ, h⟩
      calc
        |ψ (t • v +ᵥ x) - ψ x| = |t| * |ψ.linear v| := by
          rw [AffineMap.map_vadd, map_smul, smul_eq_mul, vadd_eq_add,
            add_sub_cancel_right, abs_mul]
        _ ≤ 1 * |ψ.linear v| :=
          mul_le_mul_of_nonneg_right htsmall.le (abs_nonneg _)
        _ < |ψ x| := by simpa only [one_mul] using hbig
  rcases hlt with hzero | hlt
  · left
    rw [hzero, sign_zero]
  · right
    exact (sign_eq_of_abs_sub_lt hlt).symm

end AffineRootSystem

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)
  (hAS4 : ∀ ψ ∈ D.extendedAffineRoots,
    ψ ∈ D.affineRoots ∨ (2 : ℝ) • ψ ∈ D.affineRoots)

include hAS4

/-- A subset of a closed facet containing its facet point has exactly
that point's depth-zero root fixer. -/
theorem rootFixer_eq_singleton_of_subset_facetClosure
    {x : D.Apartment} {Ω : Set D.Apartment} (hx : x ∈ Ω)
    (hΩ : Ω ⊆ AffineRootSystem.facetClosure D.affineRoots x)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.rootFixer a Ω = D.rootFixer a {x} := by
  apply le_antisymm
  · exact D.rootFixer_anti a (Set.singleton_subset_iff.2 hx)
  · intro g hg
    rw [D.rootFixer_singleton] at hg
    exact D.mem_rootFixer.2 ⟨hg.1, fun y hy =>
      (D.filtration_comparison_of_mem_facetClosure hAS4 (hΩ hy) ha).2 hg⟩

/-- The sharp fixer has the same constancy for any such subset. -/
theorem sharpFixer_eq_singleton_of_subset_facetClosure
    {x : D.Apartment} {Ω : Set D.Apartment} (hx : x ∈ Ω)
    (hΩ : Ω ⊆ AffineRootSystem.facetClosure D.affineRoots x) :
    D.sharpFixer Ω = D.sharpFixer {x} := by
  unfold sharpFixer
  congr 1
  funext a
  exact D.rootFixer_eq_singleton_of_subset_facetClosure hAS4 hx hΩ a.property

/-- Adding a point in the facet closure leaves the root fixer unchanged. -/
theorem rootFixer_pair_eq_singleton_of_mem_facetClosure
    {x y : D.Apartment} (hxy : x ∈ AffineRootSystem.facetClosure D.affineRoots y)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) :
    D.rootFixer a {x, y} = D.rootFixer a {y} := by
  apply D.rootFixer_eq_singleton_of_subset_facetClosure hAS4 (by simp) _ ha
  intro z hz
  rcases Set.mem_insert_iff.1 hz with rfl | hz
  · exact hxy
  · have hz' : z = y := Set.mem_singleton_iff.1 hz
    subst z
    exact AffineRootSystem.mem_facetClosure_self _ _

/-- Adding a point in the facet closure leaves the sharp fixer unchanged. -/
theorem sharpFixer_pair_eq_singleton_of_mem_facetClosure
    {x y : D.Apartment} (hxy : x ∈ AffineRootSystem.facetClosure D.affineRoots y) :
    D.sharpFixer {x, y} = D.sharpFixer {y} := by
  unfold sharpFixer
  congr 1
  funext a
  exact D.rootFixer_pair_eq_singleton_of_mem_facetClosure hAS4 hxy a.property

/-- The resulting multiplicative equivalence preserves each actual rational
point of the sharp fixer. -/
def sharpFixerPairEquivSingletonOfMemFacetClosure
    {x y : D.Apartment} (hxy : x ∈ AffineRootSystem.facetClosure D.affineRoots y) :
    D.sharpFixer {x, y} ≃* D.sharpFixer {y} :=
  MulEquiv.subgroupCongr
    (D.sharpFixer_pair_eq_singleton_of_mem_facetClosure hAS4 hxy)

@[simp] theorem sharpFixerPairEquivSingletonOfMemFacetClosure_coe
    {x y : D.Apartment} (hxy : x ∈ AffineRootSystem.facetClosure D.affineRoots y)
    (g : D.sharpFixer {x, y}) :
    (D.sharpFixerPairEquivSingletonOfMemFacetClosure hAS4 hxy g :
      rationalPoints G) = g := by
  exact MulEquiv.subgroupCongr_apply
    (D.sharpFixer_pair_eq_singleton_of_mem_facetClosure hAS4 hxy) g

end KPApartmentData

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- The original point is in the closed facet of nearby points on every
translation line of the supplied integer-valued apartment. -/
theorem eventually_mem_facetClosure_smul_vadd
    (x : B.Apartment) (w : TranslationSpace B.i) :
    ∀ᶠ t : ℝ in 𝓝 0,
      x ∈ AffineRootSystem.facetClosure B.affineRoots (t • w +ᵥ x) := by
  have hpair : RelativeRoot.HasOppositeFactorPairs B.i := by
    have hrank := rootRankOneFactorization k G B.isConnectedReductive
      B.S B.i B.isMaximalSplitTorus
    exact fun a ha g hg hg1 => (hrank a ha g hg hg1).1.exists
  exact AffineRootSystem.eventually_mem_facetClosure_smul_vadd
    (B.finite_bounded_affineRoots_of_oppositePairs hpair) x w

/-- The two-point root fixers agree simultaneously with the translated
singleton root fixers near the zero parameter. -/
theorem eventually_rootFixer_pair_eq_singleton
    (x : B.Apartment) (w : TranslationSpace B.i) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ a : relativeRoots B.i,
      B.rootFixer a {x, t • w +ᵥ x} = B.rootFixer a {t • w +ᵥ x} := by
  filter_upwards [B.eventually_mem_facetClosure_smul_vadd x w] with t ht a
  exact B.apartment.rootFixer_pair_eq_singleton_of_mem_facetClosure
    B.affineRoot_mem_or_two_smul_mem ht a.property

/-- The two-point and translated singleton sharp fixers agree near zero. -/
theorem eventually_sharpFixer_pair_eq_singleton
    (x : B.Apartment) (w : TranslationSpace B.i) :
    ∀ᶠ t : ℝ in 𝓝 0,
      B.sharpFixer {x, t • w +ᵥ x} = B.sharpFixer {t • w +ᵥ x} := by
  filter_upwards [B.eventually_mem_facetClosure_smul_vadd x w] with t ht
  exact B.apartment.sharpFixer_pair_eq_singleton_of_mem_facetClosure
    B.affineRoot_mem_or_two_smul_mem ht

end IntegerValuationBuildingData

end Langlands.Geometry.Building
