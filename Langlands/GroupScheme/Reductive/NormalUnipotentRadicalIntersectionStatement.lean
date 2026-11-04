import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding
import Langlands.GroupScheme.SubgroupFunctor.QuotientNormality
import Langlands.GroupScheme.HomImageEmbedding

/-! # Unipotent radicals of normal connected subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a smooth connected normal subgroup
meets the ambient unipotent radical in its own full unipotent radical.
This declaration is a structural proposition target. -/
def NormalUnipotentRadicalIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace H.X.left],
    ∀ (i : H ⟶ G), IsClosedSubgroup i →
      (SubgroupFunctor.range i).IsNormal →
      ∀ (U V : GroupScheme (Spec (CommRingCat.of k)))
        (r : U ⟶ G) (s : V ⟶ H),
        IsUnipotentRadical r → IsUnipotentRadical s →
          (SubgroupFunctor.range r).comap i = SubgroupFunctor.range s

section SuppliedQuotients

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H U V Q R : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [Smooth H.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [ConnectedSpace G.X.left] [ConnectedSpace H.X.left]
    (hIntersection : NormalUnipotentRadicalIntersectionStatement.{u})
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hnormal : (SubgroupFunctor.range i).IsNormal)
    (r : U ⟶ G) (s : V ⟶ H)
    (hr : IsUnipotentRadical r) (hs : IsUnipotentRadical s)
    (q : G ⟶ Q) (p : H ⟶ R)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range r)
    (hp : SubgroupFunctor.range (kernelι p) = SubgroupFunctor.range s)

include hIntersection hi hnormal hr hs hq hp

/-- The structural radical intersection target identifies the full kernels
in a supplied pair of radical quotient maps. -/
theorem kernel_comap_eq_of_normalUnipotentRadicalIntersectionStatement :
    (SubgroupFunctor.range (kernelι q)).comap i =
      SubgroupFunctor.range (kernelι p) := by
  rw [hq, hp]
  exact hIntersection k G H i hi hnormal U V r s hr hs

variable
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    [Flat p.hom.hom.left] [Surjective p.hom.hom.left]
    [QuasiCompact p.hom.hom.left]
    [Smooth R.X.hom] [ConnectedSpace R.X.left] [IsAffineHom R.X.hom]
    [LocallyOfFiniteType Q.X.hom] [IsAffineHom Q.X.hom]

/-- For supplied fpqc radical quotients with the displayed quotient geometry,
the structural intersection target gives a closed normal quotient inclusion. -/
theorem exists_normal_quotientSubgroupHom_of_normalUnipotentRadicalIntersectionStatement :
    ∃ j : R ⟶ Q, i ≫ q = p ≫ j ∧
      IsClosedSubgroup j ∧ (SubgroupFunctor.range j).IsNormal := by
  have hk := kernel_comap_eq_of_normalUnipotentRadicalIntersectionStatement
    hIntersection i hi hnormal r s hr hs q p hq hp
  let j := SubgroupFunctor.quotientSubgroupHom i q p hk.ge
  have hjmono : Mono j.hom.hom :=
    SubgroupFunctor.quotientSubgroupHom_mono i q p hk.ge hk.le
  let : Mono j.hom.hom := hjmono
  have hsq : i ≫ q = p ≫ j :=
    SubgroupFunctor.quotientSubgroupHom_square i q p hk.ge
  exact ⟨j, hsq, HomImage.isClosedSubgroup_of_mono j,
    SubgroupFunctor.isNormal_range_of_fpqc_square i q p j hsq hnormal⟩

end SuppliedQuotients

end Langlands.GroupScheme
