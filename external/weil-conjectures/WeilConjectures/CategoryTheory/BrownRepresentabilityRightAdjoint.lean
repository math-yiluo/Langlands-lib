/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentability
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Brown representability criterion for a right adjoint

Source: Stacks Project, Derived Categories, Tag 0A8G, Proposition `proposition-brown`
(blueprint: lem-pc-brown-representability-right-adjoint).
-/

@[expose] public section

universe w u₁ u₂ v₁ v₂

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- An exact functor from a compactly generated triangulated category that preserves
set-indexed coproducts has a right adjoint. Source: Stacks Project, Tag 0A8G,
Proposition `proposition-brown` (blueprint: lem-pc-brown-representability-right-adjoint).
The indexing universe contains both morphism universes and an arbitrary universe `w`
for the generating set; object universes are independent.

Proof: Replace `C` and `D` by `ULiftHom.{max w v₁ v₂}` models, whose morphism types live
in the coproduct indexing universe, transporting the triangulated structures, coproducts
and compact generation along `ULiftHom.equiv`. The transported functor is triangulated and
preserves coproducts, and the transported source has a family of compact generators
(`IsCompactlyGeneratedTriangulated.exists_compactGenerators`), so it is a left adjoint by
`Functor.isLeftAdjoint_of_compactGenerators`. Being a left adjoint is invariant under
composition with equivalences, so `F` is a left adjoint.
-/
theorem brownRepresentabilityRightAdjoint
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [Preadditive C] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [IsTriangulated D]
    [HasCoproducts.{max w v₁ v₂} C] [HasCoproducts.{max w v₁ v₂} D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    (hC : IsCompactlyGeneratedTriangulated.{max w v₁ v₂} C)
    (hF : ∀ I : Type (max w v₁ v₂), PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  let eC : C ≌ ULiftHom.{max w v₁ v₂} C := ULiftHom.equiv
  let eD : D ≌ ULiftHom.{max w v₁ v₂} D := ULiftHom.equiv
  obtain ⟨zC, sC, pC, aC, tC, iC, cC, hTC⟩ := triangulatedEquivalenceTransfer eC
  obtain ⟨zD, sD, pD, aD, tD, iD, cD, hTD⟩ := triangulatedEquivalenceTransfer eD
  let := zC
  let := sC
  let := pC
  let := aC
  let := tC
  let := iC
  let := cC
  let := zD
  let := sD
  let := pD
  let := aD
  let := tD
  let := iD
  let := cD
  let := eC.commShiftInverse ℤ
  let := eD.commShiftInverse ℤ
  let := hTC.1
  let := hTC.2
  let := hTD.1
  let := hTD.2
  let : HasCoproducts.{max w v₁ v₂} (ULiftHom.{max w v₁ v₂} C) :=
    fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence eC.inverse
  obtain ⟨ι, S, hS⟩ := (compactGenerationEquivalence eC hC).exists_compactGenerators
  let Fs := eC.inverse ⋙ F ⋙ eD.functor
  have : ∀ I : Type (max w v₁ v₂), PreservesColimitsOfShape (Discrete I) Fs := by
    intro I
    let := hF I
    dsimp [Fs]
    infer_instance
  have hAdj : Fs.IsLeftAdjoint := Functor.isLeftAdjoint_of_compactGenerators hS Fs
  have hAdj' : (F ⋙ eD.functor).IsLeftAdjoint :=
    (Functor.isLeftAdjoint_comp_iff_right eC.inverse (F ⋙ eD.functor)).mp hAdj
  exact (Functor.isLeftAdjoint_comp_iff_left F eD.functor).mp hAdj'

end CategoryTheory
