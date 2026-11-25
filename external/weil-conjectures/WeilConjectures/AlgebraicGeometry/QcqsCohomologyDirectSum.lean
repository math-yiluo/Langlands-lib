/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.QcqsCohomologyFiniteSubsumRepresentatives
import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

/-! # Cohomology commutes with direct sums on qcqs schemes

Source: Stacks Project, Cohomology, Tag 01FF, applied as in Tag 09J7
(blueprint: lem-weil-pbc-qcqs-cohomology-direct-sum).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme


open Classical in
/-- Coproduct projections detect every direct-sum component after an additive functor. -/
private theorem moduleCohomology_directSum_injective (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (_hS : IsColimit (Cofan.mk S ι)) (p : ℕ) :
    Function.Injective
      (DirectSum.toModule ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) I
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj S)
        (fun i ↦ ((RingedSpace.moduleCohomology X.toRingedSpace p).map (ι i)).hom)) := by
  classical
  let H := RingedSpace.moduleCohomology X.toRingedSpace p
  have : H.Additive := by
    dsimp [H, RingedSpace.moduleCohomology]
    infer_instance
  let R := (moduleRings X.toRingedSpace).obj.obj (op ⊤)
  let M := fun i ↦ ↥(H.obj (F i))
  let φ := DirectSum.toModule R I (H.obj S) (fun i ↦ (H.map (ι i)).hom)
  let π (i : I) : S ⟶ F i := Cofan.IsColimit.desc _hS
    (fun j ↦ if h : j = i then eqToHom (congrArg F h) else 0)
  have hπ (i j : I) : ι j ≫ π i =
      (if h : j = i then eqToHom (congrArg F h) else 0) := by
    exact Cofan.IsColimit.fac _hS _ j
  have hcomp (i : I) : (H.map (π i)).hom.comp φ = DirectSum.component R I M i := by
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, φ, DirectSum.toModule_lof]
    change (H.map (ι j) ≫ H.map (π i)).hom x = _
    rw [← H.map_comp, hπ]
    by_cases h : j = i
    · subst j
      simp [M]
    · simp [h, M, DirectSum.component.of]
  intro x y hxy
  apply DirectSum.ext_component R
  intro i
  rw [← hcomp i]
  exact congrArg (H.map (π i)).hom hxy


open Classical in
/-- On a quasi-compact quasi-separated scheme, the canonical linear map from the direct sum
of the cohomology modules to the cohomology of a coproduct is bijective, hence an isomorphism.
Its restriction to summand `i` is the map on cohomology induced by `ι i`.
In particular, take `I = ℕ` and the family of nonnegative graded pieces of a quasi-coherent
 graded module; no quasi-coherence hypothesis is needed for the general assertion.

Source: Stacks Project, Cohomology, Tag 01FF, and its direct-sum application in Tag 09J7
(blueprint: lem-weil-pbc-qcqs-cohomology-direct-sum).

Proof:
1. By lem-weil-pbc-qcqs-scheme-spectral and def-weil-spectral-space, the underlying space
has a basis of compact opens closed under intersection, and the whole space is compact.
Thus lem-weil-pbc-qs-scheme-cohomology-directed-colimit applies at the whole space.
2. Finite partial sums are biproducts in the abelian module-sheaf category. Their inclusions
form a directed system indexed by finite subsets of I; the given coproduct is its colimit
by lem-weil-pbc-scheme-modules-coproduct-finite-subsums, including the empty partial sum.
3. By pqf-def-cohomology and lem-weil-pbc-right-derived-universal-delta-functor, H^p is
additive (def-weil-pbc-delta-functor, def-weil-pbc-additive-functor). Applying it to the
finite biproduct identities identifies each finite partial cohomology sum with H^p of
that finite partial sheaf sum.
4. Every algebraic direct-sum element has finite support (def-weil-pbc-direct-sum-modules).
Functoriality identifies its image under the canonical map with the image of the
corresponding finite partial cohomology class in the cohomology of the full coproduct.
5. Directed-colimit cohomology gives a finite-stage representative of every target class;
step 3 then gives a finite-support preimage, proving surjectivity.
6. A finite-support class mapping to zero becomes zero at a larger finite stage by the
same directed-colimit theorem. Step 3 is injective at that stage, so the original class
was zero. The canonical map is linear and bijective, hence an isomorphism.
7. The graded assertion is the specialization I = ℕ of this same assertion. -/
theorem moduleCohomology_directSum_bijective (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (_hS : IsColimit (Cofan.mk S ι)) (p : ℕ) :
    Function.Bijective
      (DirectSum.toModule ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) I
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj S)
        (fun i ↦ ((RingedSpace.moduleCohomology X.toRingedSpace p).map (ι i)).hom)) := by
  classical
  refine ⟨moduleCohomology_directSum_injective X I F S ι _hS p, ?_⟩
  have : HasFiniteBiproducts (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Abelian.hasFiniteBiproducts
  let H := RingedSpace.moduleCohomology X.toRingedSpace p
  have : H.Additive := by
    dsimp [H, RingedSpace.moduleCohomology]
    infer_instance
  intro x
  obtain ⟨J, y, hy⟩ := moduleCohomology_finiteSubsum_representative X I F S ι _hS p x
  let A := fun j : J ↦ F j
  let R := (moduleRings X.toRingedSpace).obj.obj (op ⊤)
  let M := fun i ↦ ↥(H.obj (F i))
  let κ : (⨁ A) ⟶ S := biproduct.desc (fun j : J ↦ ι j)
  refine ⟨∑ j : J, DirectSum.lof R I M j ((H.map (biproduct.π A j)).hom y), ?_⟩
  rw [map_sum]
  have hκ : ∑ j : J, H.map (biproduct.π A j) ≫ H.map (ι j) = H.map κ := by
    simp only [← H.map_comp, ← H.map_sum]
    congr 1
    calc
      ∑ j : J, biproduct.π A j ≫ ι j =
          ∑ j : J, (biproduct.π A j ≫ biproduct.ι A j) ≫ κ := by
            simp [κ]
      _ = (∑ j : J, biproduct.π A j ≫ biproduct.ι A j) ≫ κ := by
        rw [Preadditive.sum_comp]
      _ = κ := by rw [IsBilimit.total (biproduct.isBilimit A), Category.id_comp]
  have he := congrArg (fun f ↦ f.hom y) hκ
  simpa [R, M, H] using he.trans hy


end AlgebraicGeometry.Scheme
