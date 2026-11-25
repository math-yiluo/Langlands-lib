/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer

/-! The compact derived source component of the derived presentation. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

private theorem derivedModuleHasCoproducts
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)] :
    HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S)) := by
  classical
  let Q := DerivedCategory.Q (C := ModuleCat.{max w vH} S)
  let K {I : Type (max w vH)} (E : I → DerivedCategory (ModuleCat.{max w vH} S)) :=
    fun i ↦ Q.objPreimage (E i)
  let e {I : Type (max w vH)} (E : I → DerivedCategory (ModuleCat.{max w vH} S)) :=
    fun i ↦ Q.objObjPreimageIso (E i)
  let c {I : Type (max w vH)} (E : I → DerivedCategory (ModuleCat.{max w vH} S)) :=
    Cofan.mk (Q.obj (∐ K E)) (fun i ↦ (e E i).inv ≫ Q.map (Sigma.ι (K E) i))
  apply hasCoproducts_of_colimit_cofans (fun E ↦ c E)
  intro I E
  let a : Discrete.functor (fun i ↦ Q.obj (K E i)) ≅ Discrete.functor E :=
    Discrete.natIso (fun i ↦ e E i.as)
  have hc := (derivedModuleDirectSums S I (K E)).some
  refine (IsColimit.precomposeHomEquiv a (c E)) ?_
  apply IsColimit.ofIsoColimit hc
  refine Cocone.ext (Iso.refl _) ?_
  intro i
  simp [a, c, Q]

/-- A compactly generated triangulated model for the derived category of modules.
Source: Stacks Project, Tags 0F5V and 0F5X.

(auxiliary; not a blueprint node)

Proof in words: construct the small-Hom derived category of modules by the
Grothendieck construction.  The rank-one free module in degree zero represents
cohomology, so its shifted Hom groups are the corresponding cohomology groups;
these commute with the displayed coproducts, proving compactness.  The same
calculation shows that vanishing of all shifted Hom groups detects the zero
object.  The coproduct construction is compatible with the triangulated
structure and shifts.  Choose the resulting small-Hom model, lift its object
universe to the displayed universe, and transport its zero object,
preadditive structure, shifts, distinguished triangles, coproducts, and the
compact-generation property along the chosen equivalence.  The equivalence
therefore commutes with integer shifts and its functor is triangulated.
-/
theorem compact_derived_source_core
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    {S : Type w} [rS : Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)] :
    ∃ (B : Type (max uA vA ((max w vH) + 1))) (cB : Category.{max w vH} B),
      letI := cB
      ∃ (zB : HasZeroObject B) (sB : HasShift B ℤ) (pB : Preadditive B),
      letI := zB
      letI := sB
      letI := pB
      ∃ aB : ∀ n : ℤ, (shiftFunctor B n).Additive,
      letI := aB
      ∃ tB : Pretriangulated B,
      letI := tB
      ∃ (iB : IsTriangulated B) (sumsB : HasCoproducts.{max w vH} B),
      letI := iB
      letI := sumsB
      IsCompactlyGeneratedTriangulated.{max w vH} B ∧
      ∃ (e : B ≌ DerivedCategory (ModuleCat.{max w vH} S))
        (se : e.functor.CommShift ℤ),
      letI := se
      e.functor.IsTriangulated := by
  let C := DerivedCategory (ModuleCat.{max w vH} S)
  have : HasCoproducts.{max w vH} C := derivedModuleHasCoproducts
  let B := ULift.{max uA vA} C
  let : Category.{max w vH} B := uliftCategory C
  let E : C ≌ B := ULift.equivalence
  obtain ⟨zB, sB, pB, aB, tB, iB, sE, hE, hEi⟩ := triangulatedEquivalenceTransfer E
  let : HasZeroObject B := zB
  let : HasShift B ℤ := sB
  let : Preadditive B := pB
  let : ∀ n : ℤ, (shiftFunctor B n).Additive := aB
  let : Pretriangulated B := tB
  let : IsTriangulated B := iB
  let : E.functor.CommShift ℤ := sE
  let : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  have : E.functor.IsTriangulated := hE
  have : E.inverse.IsTriangulated := hEi
  have sumsB : HasCoproducts.{max w vH} B :=
    fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence E.inverse
  have hgen := compactGenerationEquivalence E (derivedModuleCompactGeneration (S := S))
  exact ⟨B, inferInstance, zB, sB, pB, aB, tB, iB, sumsB, hgen,
    E.symm, E.commShiftInverse ℤ, hEi⟩

end CategoryTheory
