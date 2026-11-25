/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectTrace

/-!
# Scalar extension of the trace on perfect complexes

This file proves item (3) (scalar extension) of blueprint `proposition-properties-trace`
(subsection `proposition-properties-trace`) for the categorical trace in the derived category, with
the Koszul braiding `DerivedCategory.braidedCategory'` of the derived tensor product: for a ring
homomorphism `φ : R →+* B`, `φ (tr_R (v ∣ P)) = tr_B (v ⊗ B ∣ P ⊗^L B)`.

## Main results

- `ModuleCat.trace_extendScalars_map`: the trace of the base change `B ⊗[R] g` of an
  endomorphism `g` of a finite free `R`-module is `φ (Tr g)`.
- `DerivedCategory.exists_trace_eq_algebraMap_and_trace_extendScalars_eq_algebraMap`, item (3) of
  `proposition-properties-trace`.

## Implementation notes

The complex `P` is a bounded complex of finitely generated free `R`-modules, so `P ⊗^L_R B` is
computed by the termwise scalar extension `B ⊗[R] P`, i.e. by the image of `P` under
`(ModuleCat.extendScalars φ).mapHomologicalComplex _`; this is the model used here. As in
`DerivedCategory.trace_eq_algebraMap_sum_negOnePow_linearMapTrace`, dualizability is rendered by
objects `K` with `[HasRightDual K]` and isomorphisms intertwining the endomorphisms. Both traces
are reduced to alternating sums of traces of components, which are compared degreewise with
`LinearMap.trace_baseChange`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace ModuleCat

variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)

instance free_extendScalars_obj (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.Free B ((extendScalars φ).obj M) := by
  let := φ.toAlgebra
  exact inferInstanceAs (Module.Free B (TensorProduct R B M))

instance finite_extendScalars_obj (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite B ((extendScalars φ).obj M) := by
  let := φ.toAlgebra
  exact inferInstanceAs (Module.Finite B (TensorProduct R B M))

/-- The trace of the scalar extension `B ⊗[R] g` of an endomorphism `g` of a finite free
`R`-module `M` is the image under `φ : R →+* B` of the trace of `g`. -/
theorem trace_extendScalars_map (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M]
    (g : M ⟶ M) :
    LinearMap.trace B _ ((extendScalars φ).map g).hom = φ (LinearMap.trace R M g.hom) := by
  let := φ.toAlgebra
  exact LinearMap.trace_baseChange g.hom B

end ModuleCat

namespace DerivedCategory

variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B)
  [HasDerivedCategory.{u} (ModuleCat.{u} R)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R)]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} B)]

/-- Blueprint `proposition-properties-trace`, item (3) (scalar extension): let `φ : R →+* B` be a
homomorphism of commutative rings, `P` a bounded complex of finitely generated free `R`-modules
and `v` a chain endomorphism of `P`. Since `P` is degreewise free, `P ⊗^L_R B` is represented by
the termwise scalar extension `P_B = B ⊗[R] P`, with endomorphism `v_B = B ⊗[R] v`. Then the
categorical trace `tr_R (v ∣ P) ∈ R` in `D(R)` and the categorical trace `tr_B (v_B ∣ P_B)` in
`D(B)` satisfy `tr_B (v_B ∣ P_B) = φ (tr_R (v ∣ P))`: there is `a : R` with
`tr_R (v ∣ P) = a` and `tr_B (v_B ∣ P_B) = φ a`. -/
theorem exists_trace_eq_algebraMap_and_trace_extendScalars_eq_algebraMap
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (v : P ⟶ P) (s : Finset ℤ)
    (hs : ∀ i ∉ s, IsZero (P.X i))
    (hfree : ∀ i, Module.Free R (P.X i)) (hfin : ∀ i, Module.Finite R (P.X i))
    (K : DerivedCategory (ModuleCat.{u} R)) [HasRightDual K] (w : K ⟶ K)
    (e : K ≅ Q.obj P) (hw : w ≫ e.hom = e.hom ≫ Q.map v)
    (K' : DerivedCategory (ModuleCat.{u} B)) [HasRightDual K'] (w' : K' ⟶ K')
    (e' : K' ≅ Q.obj (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj P))
    (hw' : w' ≫ e'.hom =
      e'.hom ≫ Q.map (((ModuleCat.extendScalars φ).mapHomologicalComplex _).map v)) :
    ∃ a : R,
      (letI := braidedCategory' (ModuleCat.{u} R)
      MonoidalCategory.trace w =
        (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u} R)))) a).asHom) ∧
      (letI := braidedCategory' (ModuleCat.{u} B)
      MonoidalCategory.trace w' =
        (algebraMap B (End (𝟙_ (DerivedCategory (ModuleCat.{u} B)))) (φ a)).asHom) := by
  refine ⟨_, trace_eq_algebraMap_sum_negOnePow_linearMapTrace P v s hs hfree hfin K w e hw, ?_⟩
  rw [trace_eq_algebraMap_sum_negOnePow_linearMapTrace _ _ s
    (fun i hi ↦ (ModuleCat.extendScalars φ).map_isZero (hs i hi))
    (fun i ↦
      have := hfree i
      ModuleCat.free_extendScalars_obj φ (P.X i))
    (fun i ↦
      have := hfin i
      ModuleCat.finite_extendScalars_obj φ (P.X i)) K' w' e' hw', map_sum φ]
  apply congrArg End.asHom
  refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [map_zsmul]
  exact congrArg _ (ModuleCat.trace_extendScalars_map φ (P.X i) (v.f i))

end DerivedCategory
