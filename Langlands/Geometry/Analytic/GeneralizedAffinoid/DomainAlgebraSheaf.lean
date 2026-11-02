import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraPresheaf
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Category.Ring.Limits

/-! # The actual stored algebra sheaf on all full affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory CategoryTheory.Limits Opposite

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K)

private theorem hom_unique {U V : Domain K A} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

/-- Matching elements on any covering sieve glue uniquely in its target's
actual stored algebra. -/
theorem algebraUnderlying_isSheaf :
    Presieve.IsSheaf (finiteDomainTopology K A)
      (algebraPresheaf K A ⋙ forget (CommAlgCat K)) := by
  intro U S hS x hx
  obtain ⟨c, hc⟩ := (isFiniteCovering_iff_finiteCover S).mp hS
  have hcompat : c.AlgebraCompatible (fun i => x (c.map i) (hc i)) := by
    intro i j W f g
    exact hx f g (hc i) (hc j) (hom_unique K A _ _)
  obtain ⟨a, ha, huniq⟩ := c.algebra_existsUnique _ hcompat
  refine ⟨a, ?_, ?_⟩
  · intro V g hg
    change g.restriction a = x g hg
    obtain ⟨d, hd⟩ := (isFiniteCovering_iff_finiteCover
      ((Sieve.ofArrows c.obj c.map).pullback g)).mp
        (IsFiniteCovering.pullback c.ofArrows_mem_finiteDomainTopology g)
    apply d.algebra_ext_of_restrict_eq
    intro i
    obtain ⟨j, f, _⟩ :=
      (Sieve.mem_ofArrows_iff c.obj c.map (d.map i ≫ g)).mp (hd i)
    calc
      (d.map i).restriction (g.restriction a) =
          f.restriction ((c.map j).restriction a) :=
        congrArg (fun q : Inclusion (d.obj i) U => q.restriction a)
          (hom_unique K A (d.map i ≫ g) (f ≫ c.map j))
      _ = f.restriction (x (c.map j) (hc j)) :=
        congrArg f.restriction (congrFun ha j)
      _ = (d.map i).restriction (x g hg) :=
        (hx (d.map i) f hg (hc j) (hom_unique K A _ _)).symm
  · intro b hb
    apply huniq b
    funext i
    exact hb (c.map i) (hc i)

/-- The actual retained commutative algebra presheaf is a sheaf for the
finite point-covering topology of all full represented domains. -/
theorem algebraPresheaf_isSheaf :
    Presheaf.IsSheaf (finiteDomainTopology K A) (algebraPresheaf K A) := by
  let : PreservesLimits (forget (CommAlgCat K)) := by
    change PreservesLimits ((commAlgCatEquivUnder (CommRingCat.of K)).functor ⋙
      Under.forget (CommRingCat.of K) ⋙ forget CommRingCat)
    infer_instance
  apply (Presheaf.isSheaf_iff_isSheaf_forget (finiteDomainTopology K A)
    (algebraPresheaf K A) (forget (CommAlgCat K))).2
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  exact algebraUnderlying_isSheaf K A

/-- The sheaf retains each original domain algebra and each actual bounded
restriction, with no descent hypothesis. -/
def algebraSheaf : Sheaf (finiteDomainTopology K A) (CommAlgCat K) :=
  ⟨algebraPresheaf K A, algebraPresheaf_isSheaf K A⟩

@[simp]
theorem algebraSheaf_obj (U : Domain K A) :
    (algebraSheaf K A).obj.obj (op U) = CommAlgCat.of K U.algebra := rfl

@[simp]
theorem algebraSheaf_map_apply {U V : Domain K A} (f : U ⟶ V) (a : V.algebra) :
    (algebraSheaf K A).obj.map f.op a = f.restriction a := rfl

/-- Sections on the actual whole domain are the original affinoid algebra. -/
theorem algebraSheaf_whole :
    (algebraSheaf K A).obj.obj (op (whole K A)) = CommAlgCat.of K A := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
