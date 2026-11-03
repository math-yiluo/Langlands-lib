import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Fpqc locality of membership in subgroup functors and their normalizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Membership in this subgroup functor can be checked after an fpqc cover
of a test scheme. This is a membership condition, not a point-lifting claim. -/
def HasFpqcMembershipDescent (F : SubgroupFunctor G) : Prop :=
  ∀ {U V : Over S} (q : V ⟶ U),
    ∀ [QuasiCompact q.left] [Flat q.left] [Surjective q.left],
      ∀ {g : U ⟶ G.X}, q ≫ g ∈ F.carrier V → g ∈ F.carrier U

/-- A subgroup represented by a monomorphism has fpqc-local membership. -/
theorem hasFpqcMembershipDescent_range (i : H ⟶ G) [Mono i.hom.hom] :
    HasFpqcMembershipDescent (range i) := by
  intro U V q _ _ _ g hg
  exact mem_range_of_comp_mem_range i q hg

/-- Normalizing a subgroup is fpqc local whenever membership in that
subgroup is fpqc local. The cover is pulled back along each refinement. -/
theorem HasFpqcMembershipDescent.normalizer {F : SubgroupFunctor G}
    (hF : HasFpqcMembershipDescent F) :
    HasFpqcMembershipDescent F.normalizer := by
  intro U V q _ _ _ g hg W a x hx
  let Z : Over S := Over.mk (pullback.fst a.left q.left ≫ W.hom)
  let r : Z ⟶ W := Over.homMk (pullback.fst a.left q.left) rfl
  let b : Z ⟶ V := Over.homMk (pullback.snd a.left q.left) (by
    rw [← Over.w q, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w a]
    rfl)
  have hrq : r ≫ a = b ≫ q := Over.OverMorphism.ext pullback.condition
  have : QuasiCompact r.left := by
    change QuasiCompact (pullback.fst a.left q.left)
    infer_instance
  have : Flat r.left := by
    change Flat (pullback.fst a.left q.left)
    infer_instance
  have : Surjective r.left := by
    change Surjective (pullback.fst a.left q.left)
    infer_instance
  have h := hg Z b (r ≫ x) (F.comp_mem r hx)
  constructor
  · apply hF r
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hrq] using h.1
  · apply hF r
    simpa only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hrq] using h.2

/-- In particular, membership in the actual torus normalizer descends along
fpqc covers without choosing a representative for that normalizer. -/
theorem mem_torusNormalizer_of_comp_mem
    {T : CommGroupScheme S} (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    {U V : Over S} (q : V ⟶ U)
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
    {g : U ⟶ G.X} (hg : q ≫ g ∈ (torusNormalizer i).carrier V) :
    g ∈ (torusNormalizer i).carrier U :=
  HasFpqcMembershipDescent.normalizer (hasFpqcMembershipDescent_range i) q hg

end Langlands.GroupScheme.SubgroupFunctor
