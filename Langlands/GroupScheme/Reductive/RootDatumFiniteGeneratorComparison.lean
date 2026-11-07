import Langlands.GroupTheory.FiniteGeneratorAction
import Langlands.GroupScheme.Reductive.RootDatumCorootComparison
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Full root-data comparison from common finite generators -/

noncomputable section

universe u v w z

namespace Langlands.LinearAlgebra

variable {M : Type u} [AddCommGroup M]

/-- Integral linear automorphisms preserving a set in both directions. -/
private def integralSetStabilizer (S : Set M) : Subgroup (M ≃ₗ[ℤ] M) where
  carrier := {e | Set.MapsTo e S S ∧ Set.MapsTo e.symm S S}
  one_mem' := ⟨fun _ hx => hx, fun _ hx => hx⟩
  mul_mem' he hf := ⟨he.1.comp hf.1, hf.2.comp he.2⟩
  inv_mem' he := ⟨he.2, he.1⟩

/-- Two involutions preserving one finite additive generating set have a
finite-order product. -/
theorem isOfFinOrder_mul_of_common_generators
    (s t : M ≃ₗ[ℤ] M) (hs : s⁻¹ = s) (ht : t⁻¹ = t)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    (hsS : Set.MapsTo s S S) (htS : Set.MapsTo t S S) :
    IsOfFinOrder (s * t) := by
  let K := integralSetStabilizer S
  have : Finite K :=
    Langlands.GroupTheory.FiniteGeneratorAction.finite_linear_subgroup_of_preserves_generating_set
      K S (fun g => g.property.1) hS hgen
  have hsinv : Set.MapsTo s.symm S S := by
    rw [show s.symm = s from hs]
    exact hsS
  have htinv : Set.MapsTo t.symm S S := by
    rw [show t.symm = t from ht]
    exact htS
  let a : K := ⟨s, hsS, hsinv⟩
  let b : K := ⟨t, htS, htinv⟩
  exact K.subtype.isOfFinOrder (isOfFinOrder_of_finite (a * b))

variable {N : Type v} [AddCommGroup N] {J : Type w} {J' : Type z}
  (P : RootDatum J M N) (Q : RootDatum J' M N)

/-- Equal roots have equal coroots when their two reflections preserve one
common finite additive generating set and the full pairings agree. -/
theorem coroot_eq_of_common_generators
    (hpair : P.toLinearMap = Q.toLinearMap)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    {j : J} {j' : J'} (hroot : P.root j = Q.root j')
    (hPS : Set.MapsTo (P.reflection j) S S)
    (hQS : Set.MapsTo (Q.reflection j') S S) :
    P.coroot j = Q.coroot j' := by
  let f := P.toLinearMap.flip (P.coroot j)
  let g := P.toLinearMap.flip (Q.coroot j')
  have hf : f (P.root j) = 2 := P.root_coroot_two j
  have hg : g (P.root j) = 2 := by
    change P.toLinearMap (P.root j) (Q.coroot j') = 2
    rw [hpair, hroot]
    exact Q.root_coroot_two j'
  have horder : IsOfFinOrder (P.reflection j * Q.reflection j') :=
    isOfFinOrder_mul_of_common_generators
      (P.reflection j) (Q.reflection j') (P.reflection_inv j) (Q.reflection_inv j')
      S hS hgen hPS hQS
  have heq := eq_functional_of_finiteOrder_reflections
    (P.root j) f g (P.reflection j) (Q.reflection j') hf hg
    (fun x => by
      rw [RootPairing.reflection_apply])
    (fun x => by
      rw [RootPairing.reflection_apply]
      change x - Q.toLinearMap x (Q.coroot j') • Q.root j' =
        x - P.toLinearMap x (Q.coroot j') • P.root j
      rw [hpair, hroot]) horder
  apply P.flip.toPerfPair.injective
  exact heq

/-- Equal root ranges give the root-index equivalence independently of coroots. -/
def rootIndexEquivOfRangeEq (hroots : Set.range P.root = Set.range Q.root) : J ≃ J' :=
  (Equiv.ofInjective P.root P.root.injective).trans
    ((Set.equivOfEq hroots).trans (Equiv.ofInjective Q.root Q.root.injective).symm)

@[simp]
theorem rootIndexEquivOfRangeEq_root
    (hroots : Set.range P.root = Set.range Q.root) (j : J) :
    Q.root (rootIndexEquivOfRangeEq P Q hroots j) = P.root j := by
  change Q.root ((Equiv.ofInjective Q.root Q.root.injective).symm _) = _
  exact congrArg Subtype.val ((Equiv.ofInjective Q.root Q.root.injective).apply_symm_apply _)

/-- Full root-data equivalence with both lattice maps the identity, obtained
from equal pairings, equal roots, and common finite additive generators
preserved by both reflection families. -/
def rootDatumEquivOfCommonGenerators
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    (hPS : ∀ j, Set.MapsTo (P.reflection j) S S)
    (hQS : ∀ j, Set.MapsTo (Q.reflection j) S S) : RootPairing.Equiv P Q where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := rootIndexEquivOfRangeEq P Q hroots
  weight_coweight_transpose := by
    ext n m
    change Q.toLinearMap m n = P.toLinearMap m n
    rw [hpair]
  root_weightMap := by
    funext j
    exact (rootIndexEquivOfRangeEq_root P Q hroots j).symm
  coroot_coweightMap := by
    funext j'
    change Q.coroot j' = P.coroot ((rootIndexEquivOfRangeEq P Q hroots).symm j')
    apply (coroot_eq_of_common_generators P Q hpair S hS hgen ?_
      (hPS _) (hQS j')).symm
    simpa using
      (rootIndexEquivOfRangeEq_root P Q hroots
        ((rootIndexEquivOfRangeEq P Q hroots).symm j')).symm
  bijective_weightMap := Function.bijective_id
  bijective_coweightMap := Function.bijective_id

@[simp]
theorem rootDatumEquivOfCommonGenerators_weightMap
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    (hPS : ∀ j, Set.MapsTo (P.reflection j) S S)
    (hQS : ∀ j, Set.MapsTo (Q.reflection j) S S) :
    (rootDatumEquivOfCommonGenerators P Q hpair hroots S hS hgen hPS hQS).toHom.weightMap =
      LinearMap.id := rfl

@[simp]
theorem rootDatumEquivOfCommonGenerators_coweightMap
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    (hPS : ∀ j, Set.MapsTo (P.reflection j) S S)
    (hQS : ∀ j, Set.MapsTo (Q.reflection j) S S) :
    (rootDatumEquivOfCommonGenerators P Q hpair hroots S hS hgen hPS hQS).toHom.coweightMap =
      LinearMap.id := rfl

@[simp]
theorem rootDatumEquivOfCommonGenerators_root
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    (hPS : ∀ j, Set.MapsTo (P.reflection j) S S)
    (hQS : ∀ j, Set.MapsTo (Q.reflection j) S S) (j : J) :
    Q.root
      ((rootDatumEquivOfCommonGenerators P Q hpair hroots S hS hgen hPS hQS).toHom.indexEquiv j) =
      P.root j :=
  rootIndexEquivOfRangeEq_root P Q hroots j

@[simp]
theorem rootDatumEquivOfCommonGenerators_coroot
    (hpair : P.toLinearMap = Q.toLinearMap)
    (hroots : Set.range P.root = Set.range Q.root)
    (S : Set M) (hS : S.Finite) (hgen : AddSubgroup.closure S = ⊤)
    (hPS : ∀ j, Set.MapsTo (P.reflection j) S S)
    (hQS : ∀ j, Set.MapsTo (Q.reflection j) S S) (j : J) :
    Q.coroot
      ((rootDatumEquivOfCommonGenerators P Q hpair hroots S hS hgen hPS hQS).toHom.indexEquiv j) =
      P.coroot j :=
  (coroot_eq_of_common_generators P Q hpair S hS hgen
    (rootIndexEquivOfRangeEq_root P Q hroots j).symm (hPS j) (hQS _)).symm

end Langlands.LinearAlgebra
