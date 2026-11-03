import Langlands.GroupScheme.Absolute.CentralizerProductQuotient
import Langlands.GroupScheme.HomogeneousClosedImmersion
import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Closed immersion and properness of the actual intersection quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralizerProduct

section Actions

variable {S : Scheme.{u}} {M B G : GroupScheme S}
variable (j : M ⟶ G) (b : B ⟶ G) {Q : Over S} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over S) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
variable {R : Over S} (r : M.X ⟶ R)
variable (hrfib : ∀ (T : Over S) (m n : T ⟶ M.X),
  m ≫ r = n ≫ r ↔
    m⁻¹ * n ∈ (SubgroupFunctor.range (subgroupIntersectionFst j b)).carrier T)
variable [Flat r.left] [Surjective r.left] [QuasiCompact r.left]

/-- The actual left action on the quotient by the intersection subgroup. -/
abbrev intersectionQuotientAction : SchemeAction M R :=
  Dynamic.flagQuotientSchemeAction M
    (SubgroupFunctor.range (subgroupIntersectionFst j b)) r hrfib

/-- The identity coset in the actual intersection quotient. -/
def intersectionQuotientBasepoint : 𝟙_ (Over S) ⟶ R :=
  (1 : 𝟙_ (Over S) ⟶ M.X) ≫ r

variable [Mono j.hom.hom] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]

include hfib hrfib

/-- The descended comparison respects the actual quotient actions on every test. -/
theorem intersectionQuotientMap_equivariant
    (T : Over S) (g : T ⟶ M.X) (x : T ⟶ R) :
    (intersectionQuotientAction j b r hrfib).act g x ≫
        intersectionQuotientMap j b q hfib r hrfib =
      ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict j).act
        g (x ≫ intersectionQuotientMap j b q hfib r hrfib) := by
  rw [SchemeAction.restrict_act]
  apply Dynamic.flagQuotient_hom_ext_of_local_lift M r x
  intro V a m ham
  rw [← Category.assoc, SchemeAction.naturality, ham]
  change (Dynamic.flagQuotientSchemeAction M
      (SubgroupFunctor.range (subgroupIntersectionFst j b)) r hrfib).act
      (a ≫ g) (m ≫ r) ≫ intersectionQuotientMap j b q hfib r hrfib = _
  rw [Dynamic.flagQuotientSchemeAction_act_lift, Category.assoc,
    comp_intersectionQuotientMap]
  rw [SchemeAction.naturality, ← Category.assoc a x, ham, Category.assoc,
    comp_intersectionQuotientMap, ← Category.assoc m j.hom.hom q,
    Dynamic.flagQuotientSchemeAction_act_lift]
  rw [← Category.assoc, MonObj.mul_comp, Category.assoc]

end Actions

section ClosedImmersion

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {M B G : GroupScheme (Spec (CommRingCat.of k))}
variable (j : M ⟶ G) (b : B ⟶ G)
variable {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
variable (hfib : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
  g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range b).carrier T)
variable {R : Over (Spec (CommRingCat.of k))} (r : M.X ⟶ R)
variable (hrfib : ∀ (T : Over (Spec (CommRingCat.of k))) (m n : T ⟶ M.X),
  m ≫ r = n ≫ r ↔
    m⁻¹ * n ∈ (SubgroupFunctor.range (subgroupIntersectionFst j b)).carrier T)
variable [Flat r.left] [Surjective r.left] [QuasiCompact r.left]

include hrfib

/-- Surjectivity over an algebraically closed field makes the identity coset
rationally transitive; no pointwise-surjectivity premise is imposed. -/
theorem intersectionQuotientAction_transitive
    [LocallyOfFiniteType M.X.hom] [LocallyOfFiniteType R.hom]
    (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ R) :
    ∃ g : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ M.X,
      (intersectionQuotientAction j b r hrfib).act g
        (intersectionQuotientBasepoint r) = y := by
  obtain ⟨g, hg⟩ := HomogeneousClosedImmersion.exists_rational_lift r y
    (r.left.surjective (y.left (IsLocalRing.closedPoint k)))
  refine ⟨g, ?_⟩
  change (Dynamic.flagQuotientSchemeAction M
    (SubgroupFunctor.range (subgroupIntersectionFst j b)) r hrfib).act g
      (1 ≫ r) = y
  rw [Dynamic.flagQuotientSchemeAction_act_lift, mul_one, hg]

variable [Mono j.hom.hom] [Mono b.hom.hom]
variable [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
variable [Smooth M.X.hom] [Smooth r.left] [QuasiCompact R.hom]
variable [LocallyOfFiniteType Q.hom]

include hfib

/-- Closedness of the actual multiplication image gives a closed immersion of
the actual intersection quotient, with no additional immersion premise. -/
theorem intersectionQuotientMap_isClosedImmersion_of_product_closed
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsClosedImmersion (intersectionQuotientMap j b q hfib r hrfib).left := by
  have hscomp : Smooth (r.left ≫ R.hom) := by rw [Over.w]; infer_instance
  let : Smooth R.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp r.left R.hom
  let : IsReduced R.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k R.left R.hom
  let : Mono (intersectionQuotientMap j b q hfib r hrfib) :=
    intersectionQuotientMap_mono j b q hfib r hrfib
  exact HomogeneousClosedImmersion.isClosedImmersion_of_closed_range
    (intersectionQuotientAction j b r hrfib)
    ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict j)
    (intersectionQuotientMap j b q hfib r hrfib)
    (intersectionQuotientMap_equivariant j b q hfib r hrfib)
    (intersectionQuotientBasepoint r)
    (intersectionQuotientAction_transitive j b r hrfib)
    (intersectionQuotientMap_range_isClosed j b q hfib r hrfib hclosed)

omit [LocallyOfFiniteType Q.hom] in
/-- A closed product inside a group with a proper ambient homogeneous quotient
makes the actual intersection quotient proper. -/
theorem intersection_quotient_isProper_of_product_closed [IsProper Q.hom]
    (hclosed : IsClosed (Set.range (productHom j b).left)) :
    IsProper R.hom := by
  let : IsClosedImmersion (intersectionQuotientMap j b q hfib r hrfib).left :=
    intersectionQuotientMap_isClosedImmersion_of_product_closed j b q hfib r hrfib hclosed
  rw [← Over.w (intersectionQuotientMap j b q hfib r hrfib)]
  infer_instance

end ClosedImmersion

end Langlands.GroupScheme.CentralizerProduct
