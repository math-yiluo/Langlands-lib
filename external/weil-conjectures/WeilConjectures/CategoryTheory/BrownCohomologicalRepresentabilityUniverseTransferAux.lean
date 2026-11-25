/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentability
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.Algebra.Category.Grp.Ulift

/-! Auxiliary reduction for universe transfer. -/

@[expose] public section

universe w v vH u

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

/-- The universe-transport construction produces a representing object and additive
natural isomorphism in the original category. The proof transports all structures
along `ULiftHom.equiv`, applies the common-universe Brown principle, and descends
along the equivalence and the universe-lift equivalences on additive groups.
Source: Stacks Project, Tag 0A8F, with explicit universe bookkeeping
(blueprint: lem-pc-brown-representability-universe-transfer-aux).

Proof: Construct the category `ULiftHom.{max w v vH} C` and transport zero objects,
shifts, preadditivity, distinguished triangles, coproducts, compact generators, and
weak generation across `ULiftHom.equiv`. Compose `H` with the inverse equivalence and
`AddCommGrpCat.uliftFunctor`; transport homologicality and preservation of all products
using the equivalence and the lift/down additive equivalences. Apply Brown
representability (`brownCohomologicalRepresentability`) in the common universe. Descend the
representing object and its natural bijections along the same equivalences to obtain a
representing-by structure for `H ⋙ forget` in `C`.
-/
theorem brownCohomologicalRepresentabilityUniverseTransfer_aux
    (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [IsTriangulated C] [HasCoproducts.{max w v vH} C]
    (hC : IsCompactlyGeneratedTriangulated.{max w v vH} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{vH}) [H.IsHomological]
    (hH : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) H) :
    ∃ G : C, Nonempty ((H ⋙ forget AddCommGrpCat).RepresentableBy G) := by
  let A := ULiftHom.{max w v vH} C
  let E : C ≌ A := ULiftHom.equiv
  obtain ⟨zA, sA, pA, aA, tA, iA, cE, hE, hEi⟩ := triangulatedEquivalenceTransfer E
  let : HasZeroObject A := zA
  let : HasShift A ℤ := sA
  let : Preadditive A := pA
  let : ∀ n : ℤ, (shiftFunctor A n).Additive := aA
  let : Pretriangulated A := tA
  have : IsTriangulated A := iA
  let : E.functor.CommShift ℤ := cE
  let : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  have : E.functor.IsTriangulated := hE
  have : E.inverse.IsTriangulated := hEi
  have : HasCoproducts.{max w v vH} A :=
    fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence E.inverse
  have hGen := compactGenerationEquivalence E hC
  let L : Aᵒᵖ ⥤ AddCommGrpCat.{vH} := E.inverse.op ⋙ H
  have : L.IsHomological := by
    dsimp [L]
    infer_instance
  let K : Aᵒᵖ ⥤ AddCommGrpCat.{max w v vH} :=
    L ⋙ AddCommGrpCat.uliftFunctor.{max w v vH}
  have : K.IsHomological := ⟨by
    intro T hT
    exact (L.map_distinguished_exact T hT).map AddCommGrpCat.uliftFunctor⟩
  have hK : ∀ I : Type (max w v vH), PreservesLimitsOfShape (Discrete I) K := by
    intro I
    have := hH I
    dsimp [K, L]
    infer_instance
  obtain ⟨G, ⟨e⟩⟩ := brownCohomologicalRepresentability A hGen K hK
  refine ⟨G.objDown, ⟨?_⟩⟩
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro X
    exact (Equiv.ulift.{max w v vH, v}).symm.trans
      (((forget AddCommGrpCat).mapIso
        (e.symm.app (Opposite.op (ULiftHom.objUp X)))).toEquiv.trans
          Equiv.ulift.{max w v vH, vH})
  · intro X X' f g
    have hn := NatTrans.naturality e.inv (E.functor.map f).op
    have hh := ConcreteCategory.congr_hom hn (ULift.up g)
    exact congrArg (fun x : K.obj (Opposite.op (ULiftHom.objUp X)) ↦ x.down) hh

end CategoryTheory
