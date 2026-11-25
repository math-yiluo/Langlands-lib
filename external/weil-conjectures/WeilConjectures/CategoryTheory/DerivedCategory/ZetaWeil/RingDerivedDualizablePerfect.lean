/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingSummand
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingTriangleClosure
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactHomHocolim
import WeilConjectures.CategoryTheory.CompactFactorThroughThick
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Functor.OfSequence

set_option linter.privateModule false

/-!
# Dualizable derived modules over an arbitrary commutative ring

Source: Stacks Project, More on Algebra, Tag 0FNS, `lemma-have-dual-derived`
(blueprint: lem-zl-ring-derived-dualizable-perfect).

The tensor is the existing K-flat derived monoidal tensor, obtained by deriving the
signed direct-sum total tensor `CochainComplex.mapBifunctor` of
`def-pc-tensor-complex-sheaves`. Its unit is canonically the degree-zero complex `A[0]`.
The localization universe is independent of the module universe.
-/

@[expose] public section

universe u w v t

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace DerivedCategory

/- Compactness transfers along a natural additive Hom equivalence preserving coproducts. -/
/- An additive left adjoint preserves compactness when its right adjoint preserves coproducts. -/
/- Compactness is invariant under isomorphism, without restricting the Hom universe. -/
/- A dualizable object is compact when the tensor unit is compact. -/
/- Cancelling unitors converts the displayed identities into the exact-pairing API. -/
/- The natural Hom--homology equivalence identifies the compactness map with a module coproduct. -/
/- Homology detects zero objects, and rank-one maps detect nonzero homology elements. -/
/- Bounded termwise duality descends through the monoidal localization of K-flat complexes. -/
/- Transport a bounded finite-projective model along an isomorphism. -/
private theorem perfect_iso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] {X Y : DerivedCategory (ModuleCat.{u} A)}
    (h : IsPerfectRingComplex X) (e : X ≅ Y) : IsPerfectRingComplex Y := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ eP⟩⟩

/- Shift the model and its two bounds. -/
private theorem perfect_shift {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] {X : DerivedCategory (ModuleCat.{u} A)}
    (h : IsPerfectRingComplex X) (n : ℤ) : IsPerfectRingComplex (X⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  exact ⟨P⟦n⟧, a - n, b - n, inferInstance, inferInstance, fun i ↦ hP (i + n),
    ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩⟩

/- A split inclusion has a split distinguished triangle, so apply the perfect-summand theorem. -/
private theorem perfect_retract {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] {X Y : DerivedCategory (ModuleCat.{u} A)}
    (r : Retract X Y) (h : IsPerfectRingComplex Y) : IsPerfectRingComplex X := by
  obtain ⟨Z, f, g, hT⟩ := distinguished_cocone_triangle r.i
  let T := Triangle.mk r.i f g
  have hz : T.mor₃ = 0 := by
    change g = 0
    have he : g ≫ r.i⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ T hT
    have hir : r.i⟦(1 : ℤ)⟧' ≫ r.r⟦(1 : ℤ)⟧' = 𝟙 (X⟦(1 : ℤ)⟧) := by
      rw [← CategoryTheory.Functor.map_comp, r.retract]
      exact (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (1 : ℤ)).map_id X
    calc
      g = g ≫ (r.i⟦(1 : ℤ)⟧' ≫ r.r⟦(1 : ℤ)⟧') := by rw [hir, Category.comp_id]
      _ = 0 := by rw [← Category.assoc, he, zero_comp]
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT hz
  exact (isPerfectRingComplex_summand X Z (perfect_iso h e)).1

/- The degree-zero rank-one complex is a bounded finite-projective model. -/
/- Perfectness is closed under triangles, shifts and retracts. -/
/- Stacks, Derived Categories, proposition-generator-versus-classical-generator (converse). -/
/- Shrink Hom universes before applying the compact-generator thick-closure argument. -/
end DerivedCategory
