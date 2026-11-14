import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Fpqc inverse images reflect represented subgroup containment -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G Q H : GroupScheme S}
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]

/-- Full inverse image under an fpqc homomorphism reflects containment in
a subgroup represented by a monomorphism. -/
theorem le_range_of_comap_le
    {F : SubgroupFunctor Q} (j : H ⟶ Q) [Mono j.hom.hom]
    (h : F.comap q ≤ (range j).comap q) : F ≤ range j := by
  intro T x hx
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let a : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let z : V ⟶ G.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have haz : a ≫ x = z ≫ q.hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have : Flat a.left := by change Flat (pullback.fst _ _); infer_instance
  have : Surjective a.left := by change Surjective (pullback.fst _ _); infer_instance
  have : QuasiCompact a.left := by change QuasiCompact (pullback.fst _ _); infer_instance
  apply mem_range_of_comp_mem_range j a
  rw [haz]
  exact h V (by
    change z ≫ q.hom.hom ∈ F.carrier V
    rw [← haz]
    exact F.comp_mem a hx)

/-- Full inverse image under an fpqc homomorphism preserves and reflects
containment in a subgroup represented by a monomorphism. -/
theorem comap_le_range_iff
    {F : SubgroupFunctor Q} (j : H ⟶ Q) [Mono j.hom.hom] :
    F.comap q ≤ (range j).comap q ↔ F ≤ range j :=
  ⟨le_range_of_comap_le q j, comap_mono⟩

/-- Full inverse image under an fpqc homomorphism preserves and reflects
containment in an explicitly represented subgroup. -/
theorem comap_le_iff_of_isRepresentedBy
    {F E : SubgroupFunctor Q} {j : H ⟶ Q} (hj : E.IsRepresentedBy j) :
    F.comap q ≤ E.comap q ↔ F ≤ E := by
  let : Mono j.hom.hom := hj.1
  rw [← hj.2]
  exact comap_le_range_iff q j

end Langlands.GroupScheme.SubgroupFunctor
