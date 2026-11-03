import Langlands.GroupScheme.Absolute.CentralizerProductProperness
import Langlands.GroupScheme.Absolute.ProperSolvableQuotient
import Langlands.GroupScheme.HomogeneousQuotientProof

/-! # Borel maximality of an intersection from a closed product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralizerProduct

section Quotient

variable {k : Type u} [Field k]
variable {M B G : GroupScheme (Spec (CommRingCat.of k))}
variable (j : M ⟶ G) (b : B ⟶ G)

/-- The first intersection projection is the base change of the second subgroup map. -/
theorem intersectionFst_isClosedSubgroup (hb : IsClosedSubgroup b) :
    IsClosedSubgroup (subgroupIntersectionFst j b) := by
  change IsClosedImmersion (subgroupIntersectionFst j b).hom.hom.left
  exact MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme j b).flip hb

/-- Choose the actual smooth homogeneous quotient by the actual intersection. -/
def intersectionQuotient [Smooth M.X.hom] [IsAffineHom M.X.hom]
    (hb : IsClosedSubgroup b) (hsm : Smooth (subgroupIntersection j b).X.hom) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient (subgroupIntersectionFst j b) :=
  Classical.choice (by
    obtain ⟨R, r, hsep, hft, hqc, hrsm, hrsurj, hrqc, hfib⟩ :=
      smoothSubgroupQuotientExistence k M (subgroupIntersection j b)
        (subgroupIntersectionFst j b) (intersectionFst_isClosedSubgroup j b hb) hsm
    exact ⟨⟨R, r, hsep, hft, hqc, hrsm, hrsurj, hrqc, hfib⟩⟩)

end Quotient

section Borel

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {M B G : GroupScheme (Spec (CommRingCat.of k))}
variable [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
variable (j : M ⟶ G) (b : B ⟶ G) [Mono j.hom.hom] [Mono b.hom.hom]
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable [IsProper Q.hom] [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
variable (hb : IsClosedSubgroup b) (hsm : Smooth (subgroupIntersection j b).X.hom)

include hfib hb hsm

omit [ConnectedSpace M.X.left] in
/-- A closed actual product makes the chosen actual intersection quotient proper. -/
theorem intersectionQuotient_isProper
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsProper (intersectionQuotient j b hb hsm).scheme.hom := by
  let R := intersectionQuotient j b hb hsm
  let : Smooth R.projection.left := R.smooth_projection
  let : Surjective R.projection.left := R.surjective_projection
  let : QuasiCompact R.projection.left := R.quasiCompact_projection
  let : QuasiCompact R.scheme.hom := R.quasiCompact
  exact intersection_quotient_isProper_of_product_closed
    j b q hfib R.projection R.fibers hclosed

/-- The proper-solvable-quotient criterion upgrades the actual intersection
to a Borel when its smoothness, connectedness and solvability are supplied. -/
theorem intersection_isBorel_of_product_closed
    (hcriterion : ProperSolvableQuotientBorelStatement.{u})
    (hconn : ConnectedSpace (subgroupIntersection j b).X.left)
    (hsol : IsSolvableGroupScheme (subgroupIntersection j b))
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsBorelSubgroup (subgroupIntersectionFst j b) := by
  let R := intersectionQuotient j b hb hsm
  have hproper : IsProper R.scheme.hom :=
    intersectionQuotient_isProper j b q hfib hb hsm hclosed
  exact hcriterion k M inferInstance (subgroupIntersection j b)
    (subgroupIntersectionFst j b) (intersectionFst_isClosedSubgroup j b hb)
    hsm hconn hsol R.scheme R.projection hproper R.smooth_projection
    R.surjective_projection R.quasiCompact_projection R.fibers

/-- The actual intersection Borel supplies the prescribed all-test containment. -/
theorem exists_isBorel_of_product_closed
    (hcriterion : ProperSolvableQuotientBorelStatement.{u})
    (hconn : ConnectedSpace (subgroupIntersection j b).X.left)
    (hsol : IsSolvableGroupScheme (subgroupIntersection j b))
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ M),
      IsBorelSubgroup c ∧ SubgroupFunctor.range (c ≫ j) ≤ SubgroupFunctor.range b := by
  refine ⟨subgroupIntersection j b, subgroupIntersectionFst j b,
    intersection_isBorel_of_product_closed j b q hfib hb hsm hcriterion hconn hsol hclosed, ?_⟩
  change SubgroupFunctor.range (subgroupIntersectionHom j b) ≤ SubgroupFunctor.range b
  rw [range_subgroupIntersectionHom j b]
  exact fun _ _ hx => hx.2

end Borel

end Langlands.GroupScheme.CentralizerProduct
