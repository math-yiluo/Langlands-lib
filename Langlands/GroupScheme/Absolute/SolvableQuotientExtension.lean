import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Solvability through a represented quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SolvableQuotientExtension

variable {S : Scheme.{u}} {N G Q : GroupScheme S} {i : N ⟶ G} {q : G ⟶ Q}

/-- The kernel of the point map embeds in the specified range whenever that range is the
scheme kernel on all tests. -/
def kernelPointsToRange
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (T : Over S) :
    (IsMonHom.monoidHom q.hom.hom T).ker →* (SubgroupFunctor.range i).carrier T where
  toFun x := ⟨x.val, by
    rw [← hker, mem_range_kernelι_iff]
    exact x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kernelPointsToRange_injective
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (T : Over S) :
    Function.Injective (kernelPointsToRange hker T) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : (SubgroupFunctor.range i).carrier T => z.val) h

/-- Equality of the kernel subgroup functor with the range of a group with solvable points
allows solvability to pass from the target to the source on any test scheme. -/
theorem points_of_kernel_range
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (T : Over S) [Group.IsSolvable (T ⟶ N.X)] [Group.IsSolvable (T ⟶ Q.X)] :
    Group.IsSolvable (T ⟶ G.X) := by
  refine Group.isSolvable_of_ker_le_range (IsMonHom.monoidHom i.hom.hom T)
    (IsMonHom.monoidHom q.hom.hom T) fun x hx => ?_
  change x ∈ (SubgroupFunctor.range i).carrier T
  exact (kernelPointsToRange hker T ⟨x, hx⟩).property

/-- A represented fppf quotient with solvable kernel points and solvable target points has
solvable source points. -/
theorem points_of_isFppfQuotient
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (T : Over S) [Group.IsSolvable (T ⟶ N.X)] [Group.IsSolvable (T ⟶ Q.X)] :
    Group.IsSolvable (T ⟶ G.X) :=
  points_of_kernel_range hq.2.2.2 T

end SolvableQuotientExtension

variable {k : Type u} [Field k]
  {N G Q : GroupScheme (Spec (CommRingCat.of k))} {i : N ⟶ G} {q : G ⟶ Q}

/-- An extension of solvable group schemes is solvable whenever its kernel is the given
range on every test scheme. -/
theorem isSolvableGroupScheme_of_kernel_range
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hN : IsSolvableGroupScheme N) (hQ : IsSolvableGroupScheme Q) :
    IsSolvableGroupScheme G := by
  have hpoints (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsSolvableGroupScheme H) :
      Group.IsSolvable (algebraicClosurePoint k ⟶ H.X) := by
    let : Group.IsSolvable
        (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
          ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X) := hH
    let e := baseChangePointsEquiv (toAlgebraicClosure k) H
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have := hpoints N hN
  have := hpoints Q hQ
  exact isSolvableGroupScheme_of_isSolvable_points
    (SolvableQuotientExtension.points_of_kernel_range hker (algebraicClosurePoint k))

/-- A represented fppf extension of solvable group schemes is solvable. -/
theorem isSolvableGroupScheme_of_solvable_fppfQuotient
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : IsSolvableGroupScheme N) (hQ : IsSolvableGroupScheme Q) :
    IsSolvableGroupScheme G :=
  isSolvableGroupScheme_of_kernel_range hq.2.2.2 hN hQ

/-- Solvability of a quotient by an affine unipotent group of finite type implies
solvability of the original group. -/
theorem isSolvableGroupScheme_of_unipotent_fppfQuotient
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    (hN : IsUnipotent N)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hQ : IsSolvableGroupScheme Q) : IsSolvableGroupScheme G :=
  isSolvableGroupScheme_of_solvable_fppfQuotient hq
    (isSolvableGroupScheme_of_isSolvable_points
      (isSolvable_points_of_isUnipotent hN (algebraicClosurePoint k))) hQ

end Langlands.GroupScheme
