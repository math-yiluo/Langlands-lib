/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.SingleHomology

/-! Nonzero homology classes give nonzero rank-one derived morphisms.
Source: Stacks Project, Tag 064B.
-/

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- A nonzero homology class yields a nonzero rank-one derived morphism.
Source: Stacks Project, Tag 064B, applied to the projective rank-one single complex.
(auxiliary; not a blueprint node)

Proof in words: choose a complex C and an isomorphism Q(C) ≅ K, and transport x
through the homology isomorphism. Choose a cycle z representing that class.
The linear map ULift S → C.X n sending ULift.up s to s • z defines a chain map
from the rank-one single complex into C[n], since z is a cycle. After localization
and transport along Q(C[n]) ≅ K[n], its degree-zero homology map sends the lifted
unit to x under the canonical homology identifications. A zero derived morphism
induces the zero homology map, contradicting hx. This proves nonvanishing.
-/
theorem derivedModule_nonzero_class_map
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (K : DerivedCategory (ModuleCat.{max w vH} S)) (n : ℤ)
    (x : ((DerivedCategory.homologyFunctor
      (ModuleCat.{max w vH} S) n).obj K)) (hx : x ≠ 0) :
    ∃ f :
      (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S)) ⟶ K⟦n⟧, f ≠ 0 := by
  classical
  -- Transport the class to a complex representing the shifted derived object.
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max w vH} S) 0
  let L := DerivedCategory.Q.objPreimage (K⟦n⟧)
  let e := DerivedCategory.Q.objObjPreimageIso (K⟦n⟧)
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{max w vH} S) n).obj K ≅
      L.homology 0 :=
    ((H.shiftIso n 0 n (add_zero n)).app K).symm ≪≫
      H.mapIso e.symm ≪≫ (DerivedCategory.homologyFunctorFactors _ 0).app L
  let y := eH.hom x
  have hy : y ≠ 0 := by
    intro h
    apply hx
    have := congrArg (fun a ↦ eH.inv a) h
    simpa [y] using this
  -- Lift the class to a cycle and send the lifted unit to that cycle.
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ 0)).1 inferInstance y
  let A := ModuleCat.of S (ULift.{vH} S)
  let g : A ⟶ L.cycles 0 := ModuleCat.ofHom
    (ULift.moduleEquiv.toLinearMap.smulRight z)
  let f : (CochainComplex.singleFunctor (ModuleCat.{max w vH} S) 0).obj A ⟶ L :=
    HomologicalComplex.mkHomFromSingle (g ≫ L.iCycles 0)
      (by rintro k (rfl : 0 + 1 = k); simp)
  refine ⟨DerivedCategory.Q.map f ≫ e.hom, ?_⟩
  intro hf
  have hQ : DerivedCategory.Q.map f = 0 := by
    apply (cancel_mono e.hom).1
    simpa using hf
  -- A zero localized map has zero homology map by naturality of the comparison.
  have hhom : HomologicalComplex.homologyMap f 0 = 0 := by
    apply (cancel_epi ((DerivedCategory.homologyFunctorFactors _ 0).hom.app _)).1
    rw [← DerivedCategory.homologyFunctorFactors_hom_naturality, hQ]
    simp
  let a := HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A
  have hcycles : HomologicalComplex.cyclesMap f 0 = a.hom ≫ g := by
    apply (cancel_mono (L.iCycles 0)).1
    simp only [a, f, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.mkHomFromSingle_f,
      HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
  have hg : g ≫ L.homologyπ 0 = 0 := by
    apply (cancel_epi a.hom).1
    rw [← Category.assoc, ← hcycles, ← HomologicalComplex.homologyπ_naturality, hhom]
    simp
  -- Evaluate at the lifted unit to contradict nonvanishing of the transported class.
  have hzero := congrArg (fun a : A ⟶ L.homology 0 ↦ a (ULift.up (1 : S))) hg
  apply hy
  change (L.homologyπ 0) ((1 : S) • z) = 0 at hzero
  simpa only [one_smul, hz] using hzero

end CategoryTheory
