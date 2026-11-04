import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # The zero adjoint weight of a self-centralizing commutative subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
  {G : GroupScheme (Spec R)}
  [IsAffineHom T.toGrp.X.hom] [IsAffineHom G.X.hom]

/-- The differential of a commutative subgroup takes values in the zero adjoint weight. -/
def zeroWeightMap (i : T.toGrp ⟶ G) :
    Additive (lieKernel T.toGrp R) →ₗ[R] weightSpace i 0 :=
  (targetMapLinear i R).codRestrict (weightSpace i 0) (by
    intro X
    apply mem_weightSpace_zero_of_mem_torusCentralizer i
    exact range_le_torusCentralizer i _ ⟨X.toMul.val, rfl⟩)

@[simp]
theorem zeroWeightMap_coe (i : T.toGrp ⟶ G)
    (X : Additive (lieKernel T.toGrp R)) :
    (zeroWeightMap i X : Additive (lieKernel G R)) = targetMapLinear i R X := rfl

/-- A monomorphic commutative subgroup has injective differential into the zero weight. -/
theorem zeroWeightMap_injective (i : T.toGrp ⟶ G) [Mono i.hom.hom] :
    Function.Injective (zeroWeightMap i) := by
  intro X Y h
  exact targetMapLinear_injective i R (congrArg Subtype.val h)

/-- An all-test self-centralizer equality makes the zero-weight differential surjective. -/
theorem zeroWeightMap_surjective_of_selfCentralizing
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    Function.Surjective (zeroWeightMap i) := by
  intro X
  have hX := mem_torusCentralizer_of_mem_weightSpace_zero i X.val.toMul X.property
  rw [hself] at hX
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hX
  have htker : t ∈ lieKernel T.toGrp R := by
    apply mem_lieKernel_of_comp i t
    rw [ht]
    exact X.val.toMul.property
  refine ⟨Additive.ofMul ⟨t, htker⟩, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  exact Subtype.ext ht

/-- The actual Lie kernel of a self-centralizing monomorphic commutative subgroup
is linearly equivalent to its zero adjoint weight space. -/
def zeroWeightEquivOfSelfCentralizing
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    Additive (lieKernel T.toGrp R) ≃ₗ[R] weightSpace i 0 :=
  LinearEquiv.ofBijective (zeroWeightMap i)
    ⟨zeroWeightMap_injective i, zeroWeightMap_surjective_of_selfCentralizing i hself⟩

@[simp]
theorem zeroWeightEquivOfSelfCentralizing_coe
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (X : Additive (lieKernel T.toGrp R)) :
    (zeroWeightEquivOfSelfCentralizing i hself X : Additive (lieKernel G R)) =
      targetMapLinear i R X := rfl

/-- The zero adjoint weight has the dimension of the self-centralizing subgroup's
actual Lie kernel over any field. -/
theorem finrank_zeroWeight_of_selfCentralizing
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (hself : torusCentralizer i = SubgroupFunctor.range i) :
    Module.finrank k (weightSpace i 0) =
      Module.finrank k (Additive (lieKernel T.toGrp k)) :=
  (zeroWeightEquivOfSelfCentralizing i hself).finrank_eq.symm

end Langlands.GroupScheme.Lie
