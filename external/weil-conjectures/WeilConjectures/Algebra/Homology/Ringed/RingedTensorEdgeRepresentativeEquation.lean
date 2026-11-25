/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation

/-! # The canonical edge equation on flat K-flat representatives

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory
namespace SheafOfModules

private abbrev Modules (A : RingedTensorCorner.{u, w}) :=
  SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

private abbrev Complexes (A : RingedTensorCorner.{u, w}) := CochainComplex (Modules A) ℤ

private abbrev Good {A : RingedTensorCorner.{u, w}} (P : Complexes A) : Prop :=
  P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

-- Elaborate the unique representative characterization with both models fixed.
/-- The canonical tensor comparison satisfies its defining representative equation.

Proof: the canonical derived tensor pullback theorem gives a unique natural
comparison characterized by this equation on flat K-flat representatives. Its
chosen comparison is the definition of `e.tensorComparison a b`. Apply its
characterization to P and Q. The preservation proofs supplied by that theorem
and the specified target proofs hp' and hq' are equal by proof irrelevance, so
the resulting equation is exactly the asserted one.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, representative construction
of pullback and tensor product; the canonical comparison's defining property.
(blueprint: lem-weil-pbc-ringed-tensor-edge-representative-equation). -/
theorem ringedTensorEdgeRepresentativeEquation {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (a : RingedTensorModel A) (b : RingedTensorModel B)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose A.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A.ring)) ℤ) (hp : P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat) (hq :
      Q.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (Q.X n).IsFlat)
    (hp' : CochainComplex.IsAcyclicTensorKFlat
      ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) ∧ ∀ n : ℤ,
      (((e.pullback.mapHomologicalComplex (.up ℤ)).obj P).X n).IsFlat)
    (hq' : CochainComplex.IsAcyclicTensorKFlat
      ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q) ∧ ∀ n : ℤ,
      (((e.pullback.mapHomologicalComplex (.up ℤ)).obj Q).X n).IsFlat) :
    e.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      (e.tensorComparison a b).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      B.tensor.map (CategoryTheory.Prod.mkHom (derivedPullbackComplexComparison e.pullback e.left
      e.epsilon P) (derivedPullbackComplexComparison e.pullback e.left e.epsilon Q)) =
    derivedPullbackComplexComparison e.pullback e.left e.epsilon ((Functor.uncurry.obj
      ((@MonoidalCategory.curriedTensor (SheafOfModules.{u} ((sheafCompose A.topology (forget₂
      CommRingCat.{u} RingCat.{u})).obj A.ring)) _ (monoidalCategory
      A.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).obj (P, Q)) ≫
      DerivedCategory.Q.map (e.ordinaryTensor.totalIso A.ring B.ring e.inverseRing e.inverse
      e.algebraic e.ringMap e.pullback e.object_eq e.pushforward e.moduleAdjunction P Q).inv ≫
      b.representative.hom.app
        (⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj P, hp'⟩,
      ⟨(e.pullback.mapHomologicalComplex (.up ℤ)).obj Q, hq'⟩) := by
  have ht := ringedTopoiCanonicalDerivedTensorPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.left e.epsilon e.isLeftDerived
    (fun P : Complexes A ↦ Good P) (fun P : Complexes B ↦ Good P)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) A.tensor B.tensor
    a.representative b.representative e.ordinaryTensor e.pushforward e.moduleAdjunction
  obtain ⟨hp₁, hq₁, hh⟩ := (Classical.choose_spec ht.2.exists) P Q hp hq
  exact hh

end SheafOfModules
