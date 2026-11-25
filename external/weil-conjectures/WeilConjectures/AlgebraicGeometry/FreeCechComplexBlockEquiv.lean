/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible

public import Mathlib.LinearAlgebra.DFinsupp
import WeilConjectures.AlgebraicGeometry.FreeCechTupleDifferential

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Evaluation of the free Čech complex has a degreewise tuple-block basis, and the
basis identifications intertwine its differentials. No exactness assertion is involved.
Source: Stacks Project, Tag 03AT, the decomposition preceding the contracting homotopy;
Tag 03F5, first proof, for coefficients in `O(W)`.
https://stacks.math.columbia.edu/tag/03AT and https://stacks.math.columbia.edu/tag/03F5
(blueprint: lem-weil-pbc-free-cech-block-equiv).
Proof: Evaluation preserves the coproduct of free representable presheaf modules. In
simplicial degree n its basis consists of tuples of indices and maps from W to their
fibre product over U₀. Project such a map onto its n+1 factors. Their common composite
is a map φ : W ⟶ U₀, and the projections give an n+1-tuple of elements of S φ. Conversely,
the limit property of the fibre product gives a unique map from any such compatible
tuple. These operations are inverse. Extend the resulting bijection of bases linearly,
and collect the basis elements with the same φ into a dependent finitely supported
family. Each element has finite support in both φ and the tuples, so this gives an
invertible linear map onto the indicated direct sum. A face map deletes the corresponding
projection, preserves φ, and agrees with `powerSetComplexFace`. Linearity therefore
identifies the alternating sums of face maps, with the same index and sign in each
summand. This proves the displayed commutation identity in every degree. Empty index
families give zero modules on both sides; no choice of a lift of φ is required. -/
theorem freeCechComplex_block_equiv (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) :
    let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex (PresheafOfModules.{u} O)).obj
        ((FormalCoproduct.mk ι fun i ↦ Over.mk (f i)).cech ⋙
          (FormalCoproduct.eval (Over U₀) (PresheafOfModules.{u} O)).obj
            (Over.forget U₀ ⋙ yoneda ⋙ PresheafOfModules.free O))))
    let S := fun φ : W ⟶ U₀ => Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}
    ∃ e : ∀ n : ℕ, K.X n ≃ₗ[O.obj (op W)]
        (Π₀ φ : W ⟶ U₀, Algebra.powerSetComplexObject (O.obj (op W)) (S φ) n),
      ∀ n : ℕ,
        (DFinsupp.mapRange.linearMap
          (fun φ => Algebra.powerSetComplexDifferential (O.obj (op W)) (S φ) n)).comp
            (e (n + 1)).toLinearMap = (e n).toLinearMap.comp (K.d (n + 1) n).hom := by
  classical
  dsimp
  let b := freeCechTupleMap X ι U₀ U f O W
  let e := fun n ↦ LinearEquiv.ofBijective (b n)
    (freeCechTupleMap_bijective X ι U₀ U f O W n)
  refine ⟨fun n ↦ (e n).symm, ?_⟩
  intro n
  have h := freeCechDifferential_compatibility X ι U₀ U f O W n
  dsimp [e, b] at h ⊢
  apply LinearMap.ext
  intro v
  apply (e n).injective
  have hv := LinearMap.congr_fun h ((e (n + 1)).symm v)
  let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
    ((AlgebraicTopology.alternatingFaceMapComplex _).obj
      (freeCechModule X ι U₀ U f O)))
  change (e n) ((DFinsupp.mapRange.linearMap _)
      ((e (n + 1)).symm v)) = (e n) ((e n).symm ((K.d (n + 1) n).hom v))
  rw [LinearEquiv.apply_symm_apply]
  have hv' : (K.d (n + 1) n).hom ((e (n + 1)) ((e (n + 1)).symm v)) =
      (e n) ((DFinsupp.mapRange.linearMap _ ) ((e (n + 1)).symm v)) := hv
  simpa only [LinearEquiv.apply_symm_apply] using hv'.symm

end AlgebraicGeometry
