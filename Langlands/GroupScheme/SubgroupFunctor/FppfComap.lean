import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Fppf inverse images reflect represented subgroup containment -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

/-- Inverse image under an fppf homomorphism reflects containment in
any explicitly represented subgroup functor. -/
def FppfComapReflectionStatement : Prop :=
  ∀ (S : Scheme.{u}) (G Q : GroupScheme S) (q : G ⟶ Q),
    Flat q.hom.hom.left → Surjective q.hom.hom.left →
    LocallyOfFinitePresentation q.hom.hom.left →
    ∀ (F E : SubgroupFunctor Q) (H : GroupScheme S) (j : H ⟶ Q),
      E.IsRepresentedBy j → (F.comap q ≤ E.comap q ↔ F ≤ E)

variable {S : Scheme.{u}} {G Q H K : GroupScheme S}
    (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]

/-- Full inverse image under an fppf homomorphism reflects containment in
a subgroup represented by a monomorphism. -/
theorem le_range_of_comap_le_of_fppf
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
  have : LocallyOfFinitePresentation a.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply mem_range_of_comp_mem_range j a
  rw [haz]
  exact h V (by
    change z ≫ q.hom.hom ∈ F.carrier V
    rw [← haz]
    exact F.comp_mem a hx)

/-- Full inverse image under an fppf homomorphism preserves and reflects
containment in a subgroup represented by a monomorphism. -/
theorem comap_le_range_iff_of_fppf
    {F : SubgroupFunctor Q} (j : H ⟶ Q) [Mono j.hom.hom] :
    F.comap q ≤ (range j).comap q ↔ F ≤ range j :=
  ⟨le_range_of_comap_le_of_fppf q j, comap_mono⟩

/-- Full inverse image under an fppf homomorphism preserves and reflects
containment in an explicitly represented subgroup. -/
theorem comap_le_iff_of_isRepresentedBy_of_fppf
    {F E : SubgroupFunctor Q} {j : H ⟶ Q} (hj : E.IsRepresentedBy j) :
    F.comap q ≤ E.comap q ↔ F ≤ E := by
  let : Mono j.hom.hom := hj.1
  rw [← hj.2]
  exact comap_le_range_iff_of_fppf q j

/-- Two monomorphically represented subgroups of an fppf target are equal
if their full inverse images agree. -/
theorem range_eq_of_comap_eq_of_fppf
    (i : H ⟶ Q) (j : K ⟶ Q) [Mono i.hom.hom] [Mono j.hom.hom]
    (h : (range i).comap q = (range j).comap q) : range i = range j :=
  le_antisymm (le_range_of_comap_le_of_fppf q j h.le)
    (le_range_of_comap_le_of_fppf q i h.ge)

/-- Full inverse image under an fppf homomorphism reflects equality of
explicitly represented subgroup functors. -/
theorem eq_of_isRepresentedBy_comap_eq_of_fppf
    {F E : SubgroupFunctor Q} {i : H ⟶ Q} {j : K ⟶ Q}
    (hi : F.IsRepresentedBy i) (hj : E.IsRepresentedBy j)
    (h : F.comap q = E.comap q) : F = E := by
  let : Mono i.hom.hom := hi.1
  let : Mono j.hom.hom := hj.1
  rw [← hi.2, ← hj.2] at h ⊢
  exact range_eq_of_comap_eq_of_fppf q i j h

/-- The named containment-reflection proposition follows from effective
epimorphism descent of factorization through a monomorphism. -/
theorem fppfComapReflection : FppfComapReflectionStatement.{u} := by
  intro S G Q q hflat hsurj hfp F E H j hj
  exact comap_le_iff_of_isRepresentedBy_of_fppf q hj

end Langlands.GroupScheme.SubgroupFunctor
