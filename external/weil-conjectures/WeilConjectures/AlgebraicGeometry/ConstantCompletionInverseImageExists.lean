/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.GeometricRingInverseImage
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Constant coefficient completion: InverseImageExists

Existence of algebraic inverse-image data (`inverseImageData_exists`).

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}

open SheafOfModules.GeometricConstruction in
set_option backward.isDefEq.respectTransparency false in
private theorem ringTransport_algebraic
    (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf J' CommRingCat.{u})
    (d : SheafOfModules.RingInverseImage L R S) :
    ∃ a : SheafOfModules.AlgebraicInverseImage L R S,
      a.ringUnderlying = d.ringUnderlying := by
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let e := d.ringUnderlying
  have hadd : L.map (ringAdd R) ≫ e.hom =
      CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ ringAdd S := by
    ext U x
    exact d.ringAdd _ (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) (ringAdd R) (fun _ _ ↦ rfl) U x
  have hmul : L.map (ringMul R) ≫ e.hom =
      CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ ringMul S := by
    ext U x
    exact d.ringMul _ (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) (ringMul R) (fun _ _ ↦ rfl) U x
  have transport (a : rset R ⊗ rset R ⟶ rset R)
      (b : rset S ⊗ rset S ⟶ rset S)
      (h : L.map a ≫ e.hom = CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ b) :
      b ≫ e.inv = (e.inv ⊗ₘ e.inv) ≫ Functor.LaxMonoidal.μ L _ _ ≫ L.map a := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [h]
    simp only [← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
      Functor.Monoidal.μ_δ_assoc]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, e.inv_hom_id,
      id_tensorHom_id, Category.id_comp]
  have ha := transport (ringAdd R) (ringAdd S) hadd
  have hm := ringIso_isMonHom L R S e.symm (transport (ringMul R) (ringMul S) hmul)
  let F := imageFunctor L R S e.inv ha hm
  refine ⟨{
    ringUnderlying := e
    ringAdd := d.ringAdd
    ringMul := d.ringMul
    ringZero := d.ringZero
    ringOne := d.ringOne
    modules := F
    moduleUnderlying := imageFunctorUnderlying L R S e.inv ha hm
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_ }, rfl⟩
  · intro M T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫ addition R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  · intro M T a ht V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        MonObj.one (X := (additiveObject R M).X) := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro M T a b t ht V x
    change (L.map t).hom.app V x = (imageAction L R S e.inv M).hom.app V
      (e.hom.hom.app V ((L.map a).hom.app V x), (L.map b).hom.app V x)
    have he : t = CartesianMonoidalCategory.lift a b ≫ action R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    change (L.map (action R M)).hom.app V
      ((Functor.LaxMonoidal.μ L _ _).hom.app V
        ((L.map a).hom.app V x, (L.map b).hom.app V x)) =
      (L.map (action R M)).hom.app V
        ((Functor.LaxMonoidal.μ L _ _).hom.app V
          (e.inv.hom.app V (e.hom.hom.app V ((L.map a).hom.app V x)),
            (L.map b).hom.app V x))
    rw [show e.inv.hom.app V (e.hom.hom.app V ((L.map a).hom.app V x)) =
      (L.map a).hom.app V x from
        congrArg (fun f ↦ f.hom.app V ((L.map a).hom.app V x)) e.hom_inv_id]

/-- Every geometric inverse image has these algebraic lifts and canonical constant maps.
Source: Stacks 00YV, 03D2, 099L
(auxiliary; not a blueprint node).
Proof: transport algebraic operations through finite products preserved by L. The
existing generalized-section equations define the transported ring and module actions.
Transport morphisms through the same underlying-sheaf isomorphisms. Since L is a left
adjoint and preserves the terminal object, it preserves coproducts of the terminal object
and hence constant sheaves. This gives the comparison naturally in every coefficient
ring, and its maps are the canonical constant-sheaf maps. -/
theorem inverseImageData_exists (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] : Nonempty (InverseImageData L) := by
  classical
  obtain ⟨rings, d, hn, ⟨constants⟩⟩ := coherentRingInverseImage_exists L V adj
  have hd (R : Sheaf J CommRingCat.{u}) := ringTransport_algebraic L R (rings.obj R) (d R)
  choose algebra halgebra using hd
  refine ⟨{
    rings := rings
    algebra := algebra
    constants := constants
    ring_naturality := ?_ }⟩
  intro R S f
  rw [halgebra R, halgebra S]
  exact hn f

end CategoryTheory.ConstantCompletion
