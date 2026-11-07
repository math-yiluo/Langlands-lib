import Langlands.GroupScheme.Lie.RootOrbitDescent
import Langlands.GroupScheme.Rational.GenericLieWeights

/-! # Reconstruction of actual root-orbit vectors from their components -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Langlands.LinearAlgebra

open Langlands.GroupScheme

section FiniteComponents

variable {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq J]
    (q : J → Submodule K V) (hq : DirectSum.IsInternal q)
    (f : I → J) (hf : Function.Injective f)

/-- Every weight component projection lands in its original actual submodule. -/
theorem weightComponentProjection_mem (j : J) (x : V) :
    weightComponentProjection q hq j x ∈ q j := by
  let := hq.chooseDecomposition
  exact (DirectSum.component K J (fun j => q j) j
    (DirectSum.decomposeLinearEquiv q x)).property

include hf in
/-- The component of a finite sum of distinct weight vectors is the original
vector in that component. -/
theorem weightComponentProjection_sum (x : Π i : I, q (f i)) (i : I) :
    weightComponentProjection q hq (f i) (∑ j : I, (x j : V)) = x i := by
  rw [map_sum, Finset.sum_eq_single i]
  · exact weightComponentProjection_of_mem q hq (f i) (x i).property
  · intro j _ hji
    exact weightComponentProjection_of_mem_ne q hq (f i) (x j).property
      (fun h => hji (hf h))
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

include hf in
/-- A vector in the span of a finite collection of distinct weight spaces is
the sum of its components in that collection. -/
theorem sum_weightComponentProjection_of_mem {x : V} (hx : x ∈ ⨆ i : I, q (f i)) :
    ∑ i : I, weightComponentProjection q hq (f i) x = x := by
  refine Submodule.iSup_induction (fun i => q (f i))
    (motive := fun x => ∑ i : I, weightComponentProjection q hq (f i) x = x)
    hx ?_ ?_ ?_
  · intro j x hx
    rw [Finset.sum_eq_single j]
    · exact weightComponentProjection_of_mem q hq (f j) hx
    · intro i _ hij
      exact weightComponentProjection_of_mem_ne q hq (f i) hx
        (fun h => hij (hf h).symm)
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · simp only [map_zero, Finset.sum_const_zero]
  · intro x y hx hy
    simp only [map_add, Finset.sum_add_distrib, hx, hy]

/-- Summing a finite collection of distinct components in an internal weight
decomposition gives exactly its actual submodule span. -/
def finiteWeightSumEquiv :
    (Π i : I, q (f i)) ≃ₗ[K] ↥(⨆ i : I, q (f i)) where
  toFun x := ⟨∑ i : I, (x i : V), Submodule.sum_mem _ (fun i _ =>
    Submodule.mem_iSup_of_mem i (x i).property)⟩
  invFun x := fun i => ⟨weightComponentProjection q hq (f i) x.val,
    weightComponentProjection_mem q hq (f i) x.val⟩
  left_inv x := by
    funext i
    apply Subtype.ext
    exact weightComponentProjection_sum q hq f hf x i
  right_inv x := Subtype.ext (sum_weightComponentProjection_of_mem q hq f hf x.property)
  map_add' x y := by
    apply Subtype.ext
    exact Finset.sum_add_distrib
  map_smul' c x := by
    apply Subtype.ext
    exact Finset.smul_sum.symm

@[simp]
theorem finiteWeightSumEquiv_val (x : Π i : I, q (f i)) :
    (finiteWeightSumEquiv q hq f hf x).val = ∑ i : I, (x i : V) := rfl

end FiniteComponents

end Langlands.LinearAlgebra

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "G_L" => CategoryTheory.Functor.obj
  (GroupScheme.baseChange (algebraBaseMap k L)) G
local notation "T_L" => CategoryTheory.Functor.obj
  (CommGroupScheme.baseChange (algebraBaseMap k L)) T
local notation "j_L" => CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k L)) j

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

attribute [local instance] rootsGaloisAction

/-- The actual ambient Lie submodule spanned by one ordinary Galois root orbit. -/
def rootOrbitWeightSpan
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    Submodule L (Additive (lieKernel G_L L)) :=
  ⨆ γ : MulAction.orbit (L ≃ₐ[k] L) β, weightSpace (T := T_L) j_L γ.val.val

variable [FiniteDimensional k L] [LocallyOfFiniteType G.X.hom]

/-- Sum actual Lie-root components across the finite Galois orbit. This is a
linear equivalence onto their literal ambient Lie submodule span. -/
def rootOrbitSumEquiv
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    (Π γ : MulAction.orbit (L ≃ₐ[k] L) β,
      weightSpace (T := T_L) j_L γ.val.val) ≃ₗ[L] rootOrbitWeightSpan k L j β := by
  classical
  let : Fintype (MulAction.orbit (L ≃ₐ[k] L) β) :=
    (Finite.finite_mulAction_orbit (M := L ≃ₐ[k] L) β).fintype
  let : LocallyOfFiniteType (G_L).X.hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
    infer_instance
  apply Langlands.LinearAlgebra.finiteWeightSumEquiv (weightSpace (T := T_L) j_L)
    (isInternal_weightSpace_of_isSplitTorus L G_L T_L hT j_L)
    (fun γ : MulAction.orbit (L ≃ₐ[k] L) β => γ.val.val)
  intro γ δ h
  apply Subtype.ext
  exact Subtype.ext h

end Langlands.GroupScheme
