import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Isogenies of split tori on cocharacters, and killed points of a covering square -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field `k`, a finite flat surjective homomorphism `f : A ⟶ T` of split tori is
injective with finite cokernel on actual integral cocharacters, and its rational and real
scalar extensions are bijective. -/
def SplitTorusIsogenyCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (A T : CommGroupScheme (Spec (CommRingCat.of k))) (f : A ⟶ T),
    IsSplitTorus A.toGrp → IsSplitTorus T.toGrp → IsIsogeny (CommGroupScheme.groupHom f) →
      Function.Injective (RealTorusSpace.cocharacterMapInt f) ∧
        Finite (cocharacterLattice T ⧸ LinearMap.range (RealTorusSpace.cocharacterMapInt f)) ∧
        Function.Bijective ((RealTorusSpace.cocharacterMapInt f).baseChange ℚ) ∧
        Function.Bijective (RealTorusSpace.cocharacterMapReal f)

section KilledPoints

variable {S : Scheme.{u}} {C G : GroupScheme S} {A T : CommGroupScheme S}
  {π : C ⟶ G} {a : A.toGrp ⟶ C} {i : T.toGrp ⟶ G} {f : A ⟶ T}

/-- In a commutative square `a ≫ π = f ≫ i` whose torus inclusion `i` is a monomorphism, a
point of `A` on any test scheme is killed by `f` exactly when its image in `C` is killed by
`π`. -/
theorem comp_groupHom_eq_one_iff_of_comp_eq (h : a ≫ π = CommGroupScheme.groupHom f ≫ i)
    [Mono i.hom.hom.left] (U : Over S) (x : U ⟶ A.toGrp.X) :
    x ≫ (CommGroupScheme.groupHom f).hom.hom = 1 ↔ (x ≫ a.hom.hom) ≫ π.hom.hom = 1 := by
  have hsq := congrArg (fun g : A.toGrp ⟶ G => g.hom.hom) h
  change a.hom.hom ≫ π.hom.hom = (CommGroupScheme.groupHom f).hom.hom ≫ i.hom.hom at hsq
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  rw [Category.assoc, hsq, ← Category.assoc]
  constructor
  · intro hx
    rw [hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono i.hom.hom).mp
    rw [hx, MonObj.one_comp]

/-- The same comparison for the actual kernels: on every test scheme, a point of `A` lies in
the range of the kernel of `f` exactly when its image in `C` lies in the range of the kernel
of `π`. -/
theorem mem_range_kernelι_groupHom_iff_of_comp_eq
    (h : a ≫ π = CommGroupScheme.groupHom f ≫ i) [Mono i.hom.hom.left]
    (U : Over S) (x : U ⟶ A.toGrp.X) :
    x ∈ (SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom f))).carrier U ↔
      x ≫ a.hom.hom ∈ (SubgroupFunctor.range (kernelι π)).carrier U := by
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  exact comp_groupHom_eq_one_iff_of_comp_eq h U x

/-- The killed-point comparison when `i` is a closed subgroup, for instance a maximal split
torus. -/
theorem comp_groupHom_eq_one_iff_of_comp_eq_of_isClosedSubgroup
    (h : a ≫ π = CommGroupScheme.groupHom f ≫ i) (hi : IsClosedSubgroup i)
    (U : Over S) (x : U ⟶ A.toGrp.X) :
    x ≫ (CommGroupScheme.groupHom f).hom.hom = 1 ↔ (x ≫ a.hom.hom) ≫ π.hom.hom = 1 := by
  have : IsClosedImmersion i.hom.hom.left := hi
  exact comp_groupHom_eq_one_iff_of_comp_eq h U x

/-- The kernel-range comparison when `i` is a closed subgroup, for instance a maximal split
torus. -/
theorem mem_range_kernelι_groupHom_iff_of_comp_eq_of_isClosedSubgroup
    (h : a ≫ π = CommGroupScheme.groupHom f ≫ i) (hi : IsClosedSubgroup i)
    (U : Over S) (x : U ⟶ A.toGrp.X) :
    x ∈ (SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom f))).carrier U ↔
      x ≫ a.hom.hom ∈ (SubgroupFunctor.range (kernelι π)).carrier U := by
  have : IsClosedImmersion i.hom.hom.left := hi
  exact mem_range_kernelι_groupHom_iff_of_comp_eq h U x

end KilledPoints

end Langlands.GroupScheme
