/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyCofan
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyMapNaturality
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The source coproduct for localized derived tensor comparison

Source: Stacks Project, Tags 06Y6 and 0DJA(1).
(blueprint: lem-pc-localized-comparison-coproduct-source). -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

/-- The localized comparison of universal models is compatible with a complex coproduct.
Source: Stacks Project, Tag 06Y6 (K-flat calculation and independence of choices),
and Tag 0DJA(1), the tensor-inheritance calculation.

Proof: Restrict M_j to R. Choose K-flat resolutions P_j and take their termwise
coproduct. Exactness of module coproducts makes the sum augmentation a
quasi-isomorphism. Tensor with an acyclic complex commutes with this coproduct,
so the sum resolution is K-flat. Specialize the fixed-second-factor derived
tensor computation to B in degree zero, identified with ordinary R-to-B
extension by the one-term tensor
isomorphism. Its counit is invertible on each P_j and their K-flat sum.
Ordinary extension commutes with sums, so this computes the derived sum.
Use the derived module direct-sum and homology-coproduct lemmas to see that
its degree-i homology is the coproduct of the summand homologies. Uniqueness
of counit-compatible derived functors compares this calculation with all the
supplied models. The model-map construction lifts the induced B-linear maps
of cohomology to E-linear maps: naturality at multiplication by each a in A
and the cohomologyIso_smul equations give compatibility with a tensor 1,
and B-linearity gives compatibility with 1 tensor b. Tensor induction gives
E-linearity. The inverse of the sum comparison is E-linear by the same action
compatibility, hence these maps form an E-module coproduct. Extension from E
to C preserves that coproduct because it is a left adjoint, producing e.
For each j, naturality of the universal counit and the ordinary tensor
associator gives compatibility with comparison. The prescribed pure-tensor
values of ordinaryIso and ordinaryToLocalized identify their naturality
squares. Apply the extension/restriction adjunction to this equation; its
naturality and localized_eq give the displayed equation. No exactness of
extension to C is required: only its preservation of coproducts is used.
Empty families give zero homology and the unique map between zero objects;
zero rings and zero complexes are included by the same construction.
(blueprint: lem-pc-localized-comparison-coproduct-source). -/
theorem exists_localizedComparison_coproduct_source
    (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]
    {I : Type u} (M : I → CochainComplex (ModuleCat.{u} A) ℤ)
    (S : CochainComplex (ModuleCat.{u} A) ℤ) (s : ∀ j, M j ⟶ S)
    (hs : IsColimit (Cofan.mk S s))
    (m : ∀ j, BaseDerivedTensorCohomologyModel R A B (M j) C)
    (mS : BaseDerivedTensorCohomologyModel R A B S C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∃ e : (∐ fun j ↦ (extendScalars (algebraMap (A ⊗[R] B) C)).obj
        ((m j).cohomology i)) ≅
      (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mS.cohomology i),
      ∀ j, Sigma.ι _ j ≫ e.hom ≫ mS.localizedComparison i =
        (m j).localizedComparison i ≫ HomologicalComplex.homologyMap (F.map (s j)) i := by
  classical
  dsimp only
  have hm (j : I) := RingTensorCohomology.exists_baseDerivedTensorCohomologyModelMap
    R A B C (M j) S (s j) (m j) mS i
  choose δ g hδ hg using hm
  obtain ⟨hc⟩ := baseDerivedTensorCohomology_canonical_cofan R A B C M S s hs m mS i
    δ g hδ hg
  let J := extendScalars.{u, u, u} (algebraMap (A ⊗[R] B) C)
  let hc' := isColimitCofanMkObjOfIsColimit J (fun j ↦ (m j).cohomology i) g hc
  let e := (coproductIsCoproduct (fun j ↦ J.obj ((m j).cohomology i))).coconePointUniqueUpToIso
    hc'
  refine ⟨e, ?_⟩
  intro j
  have he : Sigma.ι _ j ≫ e.hom = J.map (g j) :=
    (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc' (Discrete.mk j)
  rw [← Category.assoc, he]
  exact baseDerivedTensorCohomologyMap_localized_naturality R A B C (M j) S (s j)
    (m j) mS i (δ j) (g j) (hδ j) (hg j)

end ModuleCat
