import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

/-! # The actual rational chart site as a dense full-domain subsite -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

private theorem domain_hom_unique {U V : Domain K A} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Domain.Inclusion U V) inferInstance f g

omit [CompleteSpace K] in
private theorem hom_unique {d e : RationalChart K A} (f g : d ⟶ e) : f = g :=
  @Subsingleton.elim (Restriction d e) inferInstance f g

/-- Pushing forward a rational sieve preserves and reflects actual finite
point coverage. The reverse direction uses unconditional rational refinement. -/
theorem isFiniteCovering_functorPushforward_iff {d : RationalChart K A}
    (S : Sieve d) :
    Domain.IsFiniteCovering (S.functorPushforward (toDomainFunctor K A)) ↔
      IsFiniteCovering S := by
  constructor
  · intro hS
    obtain ⟨I, hI, D, f, hf, hcover⟩ := hS.rationalRefinement
    refine ⟨I, hI, D, fun i => (toDomainFunctor K A).preimage (f i), ?_, hcover⟩
    intro i
    have hmem :
        (S.functorPushforward (toDomainFunctor K A)).functorPullback
          (toDomainFunctor K A) ((toDomainFunctor K A).preimage (f i)) := by
      change (S.functorPushforward (toDomainFunctor K A))
        ((toDomainFunctor K A).map ((toDomainFunctor K A).preimage (f i)))
      have hmap :
          (toDomainFunctor K A).map ((toDomainFunctor K A).preimage (f i)) = f i :=
        (toDomainFunctor K A).map_preimage (f i)
      exact hmap.symm ▸ hf i
    rwa [Sieve.functorPullback_functorPushforward_eq] at hmem
  · rintro ⟨I, hI, D, f, hf, hcover⟩
    exact ⟨I, hI, fun i => (D i).toDomain,
      fun i => (toDomainFunctor K A).map (f i),
      fun i => Sieve.image_mem_functorPushforward (toDomainFunctor K A) S (hf i),
      hcover⟩

/-- Every full domain is covered by actual ambient rational charts. -/
instance : (toDomainFunctor K A).IsCoverDense (Domain.finiteDomainTopology K A) where
  is_cover U := by
    let c := Domain.finiteRationalCoverData U
    refine ⟨ULift.{u} (Fin c.size), inferInstance,
      fun i => (c.chart i.down).toDomain, fun i => c.map i.down,
      fun i => Presieve.in_coverByImage (toDomainFunctor K A) (c.map i.down), ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := c.covers x hx
    exact ⟨ULift.up i, hi⟩

/-- The actual fully faithful rational chart functor is a dense subsite for
the two independently defined finite point-covering topologies. -/
instance : (toDomainFunctor K A).IsDenseSubsite
    (finiteRationalTopology K A) (Domain.finiteDomainTopology K A) where
  functorPushforward_mem_iff := by
    intro d S
    exact isFiniteCovering_functorPushforward_iff S

/-- Restriction of a full-domain covering sieve is exactly rational coverage. -/
theorem functorPullback_mem_finiteRationalTopology_iff {d : RationalChart K A}
    (S : Sieve d.toDomain) :
    S.functorPullback (toDomainFunctor K A) ∈ finiteRationalTopology K A d ↔
      S ∈ Domain.finiteDomainTopology K A d.toDomain := by
  constructor
  · intro hS
    have hpush := (isFiniteCovering_functorPushforward_iff
      (S.functorPullback (toDomainFunctor K A))).2 hS
    apply (Domain.finiteDomainTopology K A).superset_covering _ hpush
    rintro V _ ⟨e, a, b, ha, rfl⟩
    exact S.downward_closed ha b
  · intro hS
    exact (toDomainFunctor K A).cover_lift
      (finiteRationalTopology K A) (Domain.finiteDomainTopology K A) hS

/-- The topology induced on rational charts is the original finite
rational point-covering topology, rather than a newly supplied topology. -/
theorem toDomainFunctor_inducedTopology :
    (toDomainFunctor K A).inducedTopology (Domain.finiteDomainTopology K A) =
      finiteRationalTopology K A := by
  ext d S
  exact (Functor.mem_inducedTopology_iff_of_isCoverDense
    (toDomainFunctor K A) (Domain.finiteDomainTopology K A) S).trans
      (isFiniteCovering_functorPushforward_iff S)

/-- An actual finite rational cover, with its pairwise product-radius
intersections, is small 1-hypercover data in the dense rational subsite. -/
def finiteDomainHypercoverData (U : Domain K A) :
    (toDomainFunctor K A).OneHypercoverDenseData.{0}
      (finiteRationalTopology K A) (Domain.finiteDomainTopology K A) U := by
  let c := Domain.finiteRationalCoverData U
  refine {
    I₀ := Fin c.size
    X := c.chart
    f := c.map
    I₁ := fun _ _ => PUnit
    Y := fun {i j} _ => (c.chart i).inter (c.chart j)
    p₁ := fun {i j} _ => interLeft (c.chart i) (c.chart j)
    p₂ := fun {i j} _ => interRight (c.chart i) (c.chart j)
    w := fun {i j} _ => domain_hom_unique _ _
    mem₀ := ?_
    mem₁₀ := ?_ }
  · exact c.toFiniteCover.ofArrows_mem_finiteDomainTopology
  · intro i j W p₁ p₂ _
    let h : W ⟶ (c.chart i).inter (c.chart j) :=
      restrictionOfSubset _ _ (by
        intro x hx
        rw [locus_inter]
        exact ⟨p₁.subset hx, p₂.subset hx⟩)
    refine ⟨PUnit.{u + 1}, inferInstance, fun _ => W, fun _ => 𝟙 W, ?_,
      fun _ hx => ⟨PUnit.unit, hx⟩⟩
    intro _
    exact ⟨PUnit.unit, h, hom_unique _ _, hom_unique _ _⟩

instance : Functor.IsOneHypercoverDense.{0} (toDomainFunctor K A)
    (finiteRationalTopology K A) (Domain.finiteDomainTopology K A) where
  nonempty_oneHypercoverDenseData U := ⟨finiteDomainHypercoverData U⟩

variable (K A)

/-- Restrict a sheaf by evaluating it on each actual rational quotient and
its actual bounded restriction. No limits in the value category are needed. -/
def domainSheafRestriction (B : Type v) [Category.{w} B] :
    Sheaf (Domain.finiteDomainTopology K A) B ⥤
      Sheaf (finiteRationalTopology K A) B :=
  (toDomainFunctor K A).sheafPushforwardContinuous B
    (finiteRationalTopology K A) (Domain.finiteDomainTopology K A)

instance (B : Type v) [Category.{w} B] : (domainSheafRestriction K A B).Full := by
  dsimp [domainSheafRestriction]
  infer_instance

instance (B : Type v) [Category.{w} B] : (domainSheafRestriction K A B).Faithful := by
  dsimp [domainSheafRestriction]
  infer_instance

@[simp]
theorem domainSheafRestriction_obj_obj (B : Type v) [Category.{w} B]
    (F : Sheaf (Domain.finiteDomainTopology K A) B)
    (d : (RationalChart K A)ᵒᵖ) :
    ((domainSheafRestriction K A B).obj F).obj.obj d =
      F.obj.obj (op d.unop.toDomain) := rfl

/-- Actual finite rational covers and pairwise intersections give comparison
using only small limits in the value category. -/
def domainSheafEquivalence (B : Type v) [Category.{w} B]
    [HasLimitsOfSize.{0, 0} B] :
    Sheaf (finiteRationalTopology K A) B ≌
      Sheaf (Domain.finiteDomainTopology K A) B := by
  letI := Functor.isEquivalence_of_isOneHypercoverDense
    (toDomainFunctor K A) (finiteRationalTopology K A)
    (Domain.finiteDomainTopology K A) B
  exact Functor.IsDenseSubsite.sheafEquiv (finiteRationalTopology K A)
    (Domain.finiteDomainTopology K A) (toDomainFunctor K A) B

@[simp]
theorem domainSheafEquivalence_inverse (B : Type v) [Category.{w} B]
    [HasLimitsOfSize.{0, 0} B] :
    (domainSheafEquivalence K A B).inverse = domainSheafRestriction K A B := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
