/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]

private lemma cochain_tensorHom {D : Type u} [CommRing D]
    {K K' L L' : CochainComplex (ModuleCat.{u} D) ℤ} (f : K ⟶ K') (g : L ⟶ L') :
    f ⊗ₘ g = HomologicalComplex.mapBifunctorMap f g
      (curriedTensor (ModuleCat.{u} D)) (.up ℤ) := by
  rfl

private lemma cochain_whiskerLeft {D : Type u} [CommRing D]
    (K : CochainComplex (ModuleCat.{u} D) ℤ)
    {L L' : CochainComplex (ModuleCat.{u} D) ℤ} (g : L ⟶ L') :
    K ◁ g = HomologicalComplex.mapBifunctorMap (𝟙 K) g
      (curriedTensor (ModuleCat.{u} D)) (.up ℤ) := by
  rfl

/-- The ordinary tensor comparison commutes with the canonical first-variable shift maps.
Source: Stacks Project, Tag 0BYJ, and the first-variable tensor shift used in Tag 0DJA(1).

Proof: the scalar-extension shift map is the identity in each degree. On a summand
U^p tensor Q^q, the first-variable tensor shift only reindexes p and has no sign.
The inverse monoidal comparison sends c tensor (u tensor q) to
(c tensor u) tensor (1 tensor q). Both paths send this generator to the same
reindexed tensor, then apply t to its second factor. Tensor induction and the universal
property of the total-complex coproduct give equality in every degree, hence equality
of complex maps. The differentials commute because each constituent is a complex map.
This also works for n=0, zero factors and t=0, and uses no derived model or flatness.
(blueprint: lem-pc-localized-tensor-comparison-shift-square-transport). -/
theorem localizedTensorComparison_shift_transport
    (U Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} C) ℤ) (n : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∀ (t : F.obj Q ⟶ N),
    let eK := F.mapIso (CochainComplex.mapBifunctorShift₁Iso U Q
      (curriedTensor (ModuleCat.{u} A)) (-n)) ≪≫ (F.commShiftIso (-n)).app (U ⊗ Q)
    let eT := tensorIso ((F.commShiftIso (-n)).app U) (Iso.refl N) ≪≫
      CochainComplex.mapBifunctorShift₁Iso (F.obj U) N
        (curriedTensor (ModuleCat.{u} C)) (-n)
    (Functor.Monoidal.μIso F (U⟦-n⟧) Q).inv ≫ (F.obj (U⟦-n⟧) ◁ t) ≫ eT.hom =
      eK.hom ≫ ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t))⟦-n⟧' := by
  set_option backward.defeqAttrib.useBackward true in
    let G := extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))
    let F := G.mapHomologicalComplex (.up ℤ)
    dsimp only
    intro t
    let τ : (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex.flip.obj Q ⋙ F ⟶
        F ⋙ (curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.obj (F.obj Q) :=
      (HomologicalComplex.mapBifunctorComparisonNatTrans
      (c₁ := .up ℤ) (c₂ := .up ℤ)
      (Functor.OplaxMonoidal.δNatTrans G) (.up ℤ)).flipApp Q
    let σ := Functor.whiskerLeft F
      ((curriedTensor (ModuleCat.{u} C)).map₂CochainComplex.flip.map t)
    have h := NatTrans.shift_app_comm (τ ≫ σ) (-n) U
    simp only [τ, σ, F, G, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app,
      Functor.commShiftIso_map₂CochainComplex_flip_hom_app,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, tensorIso_hom, Iso.refl_hom,
      Functor.Monoidal.μIso_inv, Functor.mapCochainComplex_δ,
      Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans, NatTrans.flipApp,
      flipFunctor_map_app_app, Functor.flip_map_app, Functor.flip_obj_map,
      Functor.map₂HomologicalComplex_obj_map, Functor.map₂HomologicalComplex_map_app,
      Functor.flip_obj_obj, Functor.map₂HomologicalComplex_obj_obj,
      cochain_tensorHom, cochain_whiskerLeft, Functor.comp_obj,
      Functor.map₂CochainComplex, CochainComplex.mapBifunctor, Category.assoc] at h ⊢
    convert h.symm using 1

end ModuleCat
