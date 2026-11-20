import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullback
import Langlands.Geometry.Analytic.SpaceAnalytificationHausdorffReduction
import Langlands.Geometry.Analytic.SpaceAnalytificationRationalPointInjectivity

/-! # Hausdorffness and rational-point injectivity from separatedness -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffineAnalytification

open Set Topology TensorProduct

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B]
  {C : Type z} [CommRing C] [Algebra K C]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] C) (g : B →ₐ[K] C)

/-- A tensor expression gives a continuous upper bound in the two point variables. -/
private theorem exists_continuous_bound_of_tensor (a : A ⊗[K] B) :
    ∃ b : C(Space K P × Space K Q, ℝ), ∀ t : Space K R,
      pointSeminorm K R t (Algebra.TensorProduct.lift f g (fun c d => Commute.all (f c) (g d)) a) ≤
        b (baseMap K P R f t, baseMap K Q R g t) := by
  induction a using TensorProduct.inductionOn with
  | tmul c d =>
      refine ⟨⟨fun x => pointSeminorm K P x.1 c * pointSeminorm K Q x.2 d,
        ((continuous_pointSeminorm_apply K P c).comp continuous_fst).mul
          ((continuous_pointSeminorm_apply K Q d).comp continuous_snd)⟩, fun t => ?_⟩
      change _ ≤ pointSeminorm K P (baseMap K P R f t) c *
        pointSeminorm K Q (baseMap K Q R g t) d
      rw [Algebra.TensorProduct.lift_tmul, map_mul, pointSeminorm_baseMap, pointSeminorm_baseMap]
  | add a a' ha ha' =>
      obtain ⟨b, hb⟩ := ha
      obtain ⟨b', hb'⟩ := ha'
      refine ⟨b + b', fun t => ?_⟩
      rw [map_add]
      exact (map_add_le_add (pointSeminorm K R t) _ _).trans (add_le_add (hb t) (hb' t))

/-- When the two maps generate the coordinate algebra, their joint map to the
ordinary product is closed. -/
theorem isClosedMap_pair_baseMap_of_surjective
    (hsurj : Function.Surjective
      (Algebra.TensorProduct.lift f g (fun a b => Commute.all (f a) (g b)) : A ⊗[K] B →ₐ[K] C)) :
    IsClosedMap (fun t : Space K R => (baseMap K P R f t, baseMap K Q R g t)) := by
  classical
  let F : Space K R → Space K P × Space K Q := fun t => (baseMap K P R f t, baseMap K Q R g t)
  have hF : Continuous F := (baseMap K P R f).continuous.prodMk (baseMap K Q R g).continuous
  have hbounds : ∀ i : Fin R.arity, ∃ b : C(Space K P × Space K Q, ℝ),
      ∀ t : Space K R, coordinateNorm K R i t ≤ b (F t) := by
    intro i
    obtain ⟨a, ha⟩ := hsurj (R.map (MvPolynomial.X i))
    obtain ⟨b, hb⟩ := exists_continuous_bound_of_tensor P Q R f g a
    exact ⟨b, fun t => by simpa only [ha, SeminormComparison.coordinateNorm_eq] using hb t⟩
  choose b hb using hbounds
  intro D hD
  change IsClosed (F '' D)
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨n, hn⟩ := exists_radius_gt K (∑ i, |b i x|)
  let U : Set (Space K P × Space K Q) := ⋂ i, {y | b i y < AnalyticAffineSpace.radius K n}
  have hU : IsOpen U := isOpen_iInter_of_finite fun i => isOpen_lt (b i).continuous continuous_const
  have hxU : x ∈ U := mem_iInter.2 fun i =>
    ((le_abs_self (b i x)).trans (Finset.single_le_sum
      (fun j _ => abs_nonneg (b j x)) (Finset.mem_univ i))).trans_lt hn
  let S : Set (Space K P × Space K Q) := F '' (range (chart K R n) ∩ D)
  have hS : IsClosed S :=
    (((isCompact_range (continuous_chart K R n)).inter_right hD).image hF).isClosed
  have hbound : U ∩ (F '' D) ⊆ S := by
    rintro _ ⟨ht, t, htD, rfl⟩
    exact ⟨t, ⟨(mem_range_chart_iff K R n t).mpr fun i =>
      (hb i t).trans ((mem_iInter.mp ht i : b i (F t) < _).le), htD⟩, rfl⟩
  have hxS : x ∈ S := by
    by_contra hxS
    obtain ⟨y, ⟨hyU, hyS⟩, hyF⟩ := mem_closure_iff.mp hx (U ∩ Sᶜ)
      (hU.inter hS.isOpen_compl) ⟨hxU, hxS⟩
    exact hyS (hbound ⟨hyU, hyF⟩)
  exact image_mono inter_subset_right hxS

/-- When the two maps generate the coordinate algebra, the inverse image of a
compact subset of the product of affine analytifications is compact. -/
theorem isCompact_preimage_pair_baseMap_of_surjective
    (hsurj : Function.Surjective
      (Algebra.TensorProduct.lift f g (fun a b => Commute.all (f a) (g b)) : A ⊗[K] B →ₐ[K] C))
    {L : Set (Space K P × Space K Q)} (hL : IsCompact L) :
    IsCompact ((fun t : Space K R => (baseMap K P R f t, baseMap K Q R g t)) ⁻¹' L) := by
  classical
  let F : Space K R → Space K P × Space K Q := fun t => (baseMap K P R f t, baseMap K Q R g t)
  have hF : Continuous F := (baseMap K P R f).continuous.prodMk (baseMap K Q R g).continuous
  have hbounds (i : Fin R.arity) : ∃ c : ℝ, ∀ t ∈ F ⁻¹' L, coordinateNorm K R i t ≤ c := by
    obtain ⟨a, ha⟩ := hsurj (R.map (MvPolynomial.X i))
    obtain ⟨b, hb⟩ := exists_continuous_bound_of_tensor P Q R f g a
    obtain ⟨c, hc⟩ := (hL.image b.continuous).bddAbove
    exact ⟨c, fun t ht => by
      rw [SeminormComparison.coordinateNorm_eq, ← ha]
      exact (hb t).trans (hc ⟨F t, ht, rfl⟩)⟩
  choose c hc using hbounds
  obtain ⟨n, hn⟩ := exists_radius_gt K (∑ i, |c i|)
  refine (isCompact_range (continuous_chart K R n)).of_isClosed_subset
    (hL.isClosed.preimage hF) fun t ht => (mem_range_chart_iff K R n t).mpr fun i => ?_
  exact ((hc i t ht).trans ((le_abs_self (c i)).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)))).trans hn.le

end Langlands.Analytic.AffineAnalytification

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

set_option backward.isDefEq.respectTransparency false in
/-- A separated algebraic space has Hausdorff analytifications. -/
theorem IsAnalytification.t2Space_of_isSeparated (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) : T2Space (localizedSpaceFunctor.obj Y) := by
  apply hp.t2Space_iff_affineEtaleChartRelationsClosed.mpr
  intro A _ _ P x _ B _ _ Q y _
  obtain ⟨C, _, _, R, f, g, hsurj, hpb⟩ :=
    hasClosedAffinePointPullbacks_of_isSeparated hX A P B Q x y
  exact Eq.mpr
    (congrArg IsClosed (hp.affine_point_relation_eq_range exists_point_of_isPullback P Q R f g x y hpb))
    (AffineAnalytification.isClosedMap_pair_baseMap_of_surjective P Q R f g hsurj).isClosed_range

/-- A separated algebraic space has injective rational-point maps into its analytifications. -/
theorem IsAnalytification.rationalPoint_injective (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) (P₀ : FinitePolynomialPresentation K K) :
    Function.Injective (rationalPoint p P₀) :=
  rationalPoint_injective_of_pointLifting exists_point_of_isPullback hX hp P₀

/-- The Hausdorffness and rational-point injectivity properties of the analytic point family. -/
def SeparatedAnalytificationProperties (p : PointFamily K X Y) : Prop :=
  T2Space (localizedSpaceFunctor.obj Y) ∧
    ∀ P₀ : FinitePolynomialPresentation K K, Function.Injective (rationalPoint p P₀)

/-- Separatedness gives Hausdorffness and injectivity for every analytification. -/
theorem IsAnalytification.separatedAnalytificationProperties (hp : IsAnalytification K X Y p)
    (hX : IsSeparated X) : SeparatedAnalytificationProperties p :=
  ⟨hp.t2Space_of_isSeparated hX, hp.rationalPoint_injective hX⟩

end Langlands.Analytic.SpaceAnalytification
