/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulSite
import WeilConjectures.AlgebraicGeometry.Weil.WeilExteriorKoszulTensorComparison
import WeilConjectures.AlgebraicGeometry.Weil.WeilNegativeKoszulTensorDualTransport

/-! # The finite coefficient comparison, before tensoring with an input complex

Source: Stacks Project, algebraization.tex, Tag 0A0E, with Modules on Sites, Tags 03DA and 03EK.
(blueprint: lem-weil-pbc-completed-koszul-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The finite exterior coefficient tower is the dual positive tensor tower.

Source: Stacks Project, More on Algebra, Tag 0664, and algebraization.tex,
Tag 0A0E, proof of lemma-derived-completion-koszul.
(blueprint: lem-weil-pbc-completed-koszul-coefficient-comparison).

Proof: use the increasing-subset bases of the exterior powers of A^(Fin r).
Identify a degree -k basis vector with the dual tensor coordinate, with sign
(-1)^(k*(k-1)/2). Contraction removes the j-th generator with sign (-1)^j;
the differential on the dual adds the degree sign, and the ratio of the two
successive comparison signs gives exactly that sign. This defines inverse
chain maps over A. Apply constant module sheafification, completed scalar
extension, inverse restriction along the coefficient isomorphism, and the
site equivalence. Each operation preserves finite free coordinates. The
transition on a subset is multiplication by the product of its generators
on both sides, so the comparison commutes with consecutive transitions.
The empty subset has sign +1. Both augmentations send 1 to that coordinate;
the transported regular-module unit is precisely the section 1, giving the
last equation. If r=0 the comparison is the unit isomorphism. Zero and unit
generators and the zero ring require no cancellation, and sheafification
also handles the empty site. No tensor with an arbitrary complex occurs. -/
theorem completedKoszulCoefficientComparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) :
    let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
    let H := F.mapHomologicalComplex (.up ℤ)
    let O := completedCechRing X d
    let b := fun i ↦ completedCechScalar X d (a i)
    let K := completedKoszulPowerSheaf X (intrinsicPresentationDatum d) r a
    ∃ e : ∀ m : ℕ, H.obj (K m) ≅ (ringedKoszulDualTower O r b).obj (op m),
      (∀ m, H.map
          (((completedKoszulConstant X (intrinsicPresentationDatum d)).mapHomologicalComplex
            (.up ℤ)).map (completedKoszulTransition (A := A) r a m)) ≫ (e m).hom =
        (e (m + 1)).hom ≫ (ringedKoszulDualTower O r b).map
          (homOfLE (Nat.le_succ m)).op) ∧
      (∀ m, completedCechCoefficientUnit X d ≫
          F.map (completedKoszulSheafUnitZero X (intrinsicPresentationDatum d) r a m) ≫
            (e m).hom.f 0 =
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
          (ringedKoszulDualUnit O r b m).f 0)  := by
  let F := intrinsicPresentationModulesBack X d ⋙ (completedCechModulesEquiv X d).functor
  let G := completedKoszulConstant X (intrinsicPresentationDatum d)
  let L := (G ⋙ F).mapHomologicalComplex (.up ℤ)
  obtain ⟨e, he, heu⟩ := exteriorNegativeKoszulTensorComparison r a
  obtain ⟨t, ht, htu⟩ := negativeKoszulTensorDualTransport X d r a
  refine ⟨fun m ↦ L.mapIso (e m) ≪≫ t m, ?_, ?_⟩
  · intro m
    change L.map (completedKoszulTransition (A := A) r a m) ≫
        (L.map (e m).hom ≫ (t m).hom) =
      (L.map (e (m + 1)).hom ≫ (t (m + 1)).hom) ≫ _
    rw [← Category.assoc, ← Functor.map_comp, he m, Functor.map_comp,
      Category.assoc, ht m, Category.assoc]
  · intro m
    change completedCechCoefficientUnit X d ≫
        F.map (completedKoszulSheafUnitZero X (intrinsicPresentationDatum d) r a m) ≫
          ((G ⋙ F).map ((e m).hom.f 0) ≫ (t m).hom.f 0) = _
    have hu :
        F.map (completedKoszulSheafUnitZero X (intrinsicPresentationDatum d) r a m) =
          F.map (completedKoszulOne X (intrinsicPresentationDatum d)) ≫
            (G ⋙ F).map (finiteKoszulExteriorUnitZero r a m) := by
      simp only [completedKoszulSheafUnitZero, finiteKoszulExteriorUnitZero,
        Functor.comp_map, Functor.map_comp]
      rfl
    rw [hu]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, heu m]
    exact htu m

end AlgebraicGeometry.Scheme
