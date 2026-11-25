/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import WeilConjectures.AlgebraicGeometry.CompletedAffinePullbackObjects
import WeilConjectures.AlgebraicGeometry.FormalComparisonFlatTransportSquare
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Transport of comparison data before taking sections

Source: Stacks Project, Tag 088B, completed-base change paragraph.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem transport_comparison_comp
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {A B E : C} {A₀ B₀ E₀ : D}
    (a : A ⟶ B) (k : B ⟶ E) (v : A ⟶ E)
    (a₀ : A₀ ⟶ B₀) (k₀ : B₀ ⟶ E₀) (v₀ : A₀ ⟶ E₀)
    (e : A₀ ⟶ T.obj A) (d : B₀ ⟶ T.obj B) (t : T.obj E ⟶ E₀)
    (ha : a ≫ k = v) (hd : a₀ ≫ d = e ≫ T.map a)
    (hk : d ≫ T.map k ≫ t = k₀) (hv : e ≫ T.map v ≫ t = v₀) :
    a₀ ≫ k₀ = v₀ := by
  calc
    a₀ ≫ k₀ = (a₀ ≫ d) ≫ T.map k ≫ t := by rw [← hk]; simp only [Category.assoc]
    _ = e ≫ T.map (a ≫ k) ≫ t := by rw [hd, T.map_comp]; simp [Category.assoc]
    _ = v₀ := by rw [ha, hv]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The algebraic part of completed affine transport, with its completion comparison.
This statement makes no assertion about section diagrams or their limits.

Source: Stacks Project, Tag 088B, completed-base change paragraph; Tags 02KH and 0887.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-data)

Proof: Restrict to the affine chart and base change along B to its adic completion R.
The extended ideal on Spec R is J₀. Apply formal-system pullback to construct G₀
termwise and coherent pullback to construct F₀ along the first projection. The
composition comparison and completion-pullback comparison give β₀. The completion
map is flat over the Noetherian B. Degree-zero flat base change gives an isomorphism
from p_*F₀ to g*f_*F, and proper coherent direct image proves coherence of p_*F₀.
Complete this isomorphism and compose with completion-pullback to get δ. Define α₀
by pulling back α and composing with δ inverse (and the equality comparison for G₀).
Transport κ using the same base-change isomorphisms for the quotient pushforwards.
Naturality at the quotient projections gives the first displayed equation. The
adjunction-unit compatibility of base change gives the second. For a supplied
adjunction, compare it with the chosen one by uniqueness of left adjoints and
adjust β₀ by that invertible pullback automorphism. This changes neither α₀ nor δ
and makes the equation use the supplied unit. The construction uses no algebraization
or faithfulness of completion. If J is the unit ideal, all formal terms are zero;
if J is zero, the completion map is the identity. The same construction includes
zero rings and empty spectra. -/
theorem formalComparison_completed_affine_data
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n)))
    (U : Y.affineOpens)
    [IsNoetherianRing (AdicCompletion (J.ideal U) Γ(Y, U.1))] :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let S := Spec (CommRingCat.of R)
    let I := (J.ideal U).map (algebraMap B R)
    let J₀ := Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let Z := pullback f g
    let p : Z ⟶ S := pullback.snd f g
    ∃ (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
      (G₀ : CoherentFormalModule S J₀) (F₀ : CoherentModules Z)
      (β₀ : G₀.obj ⋙ Scheme.Modules.tensorPullback p ≅
        formalCompletionSystem (J₀.comap p) F₀.obj)
      (hD : RingedSpace.IsCoherent S.toRingedSpace
        ((Scheme.Modules.pushforward p).obj F₀.obj))
      (κ₀ : formalCompletionSystem J₀ ((Scheme.Modules.pushforward p).obj F₀.obj) ⟶
        formalCompletionSystem (J₀.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p)
      (α₀ : G₀ ⟶ (completion S J₀).obj
        ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩),
      ∃ hG : G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g,
      F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj ∧
      (∀ n : ℕ, formalModuleQuotientπ J₀ (n + 1)
          ((Scheme.Modules.pushforward p).obj F₀.obj) ≫ κ₀.app (op n) =
        (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J₀.comap p) (n + 1) F₀.obj)) ∧
      (∀ n : ℕ, α₀.hom.app (op n) ≫ κ₀.app (op n) =
        adjR.unit.app (G₀.obj.obj (op n)) ≫
          (Scheme.Modules.pushforward p).map (β₀.hom.app (op n))) ∧
      ∃ δ : ((completion S J₀).obj
          ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩).obj ≅
        ((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
            Scheme.Modules.tensorPullback g,
        α₀.hom ≫ δ.hom = eqToHom hG ≫
          Functor.whiskerRight α.hom (Scheme.Modules.tensorPullback g) := by
  classical
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let S := Spec (CommRingCat.of R)
  let I := (J.ideal U).map (algebraMap B R)
  let J₀ := Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
    U.2.isoSpec.inv ≫ U.1.ι
  let Z := pullback f g
  let p : Z ⟶ S := pullback.snd f g
  change ∃ (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
      (G₀ : CoherentFormalModule S J₀) (F₀ : CoherentModules Z)
      (β₀ : G₀.obj ⋙ Scheme.Modules.tensorPullback p ≅
        formalCompletionSystem (J₀.comap p) F₀.obj)
      (hD : RingedSpace.IsCoherent S.toRingedSpace
        ((Scheme.Modules.pushforward p).obj F₀.obj))
      (κ₀ : formalCompletionSystem J₀ ((Scheme.Modules.pushforward p).obj F₀.obj) ⟶
        formalCompletionSystem (J₀.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p)
      (α₀ : G₀ ⟶ (completion S J₀).obj
        ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩),
      ∃ hG : G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g,
      F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj ∧
      (∀ n : ℕ, formalModuleQuotientπ J₀ (n + 1)
          ((Scheme.Modules.pushforward p).obj F₀.obj) ≫ κ₀.app (op n) =
        (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J₀.comap p) (n + 1) F₀.obj)) ∧
      (∀ n : ℕ, α₀.hom.app (op n) ≫ κ₀.app (op n) =
        adjR.unit.app (G₀.obj.obj (op n)) ≫
          (Scheme.Modules.pushforward p).map (β₀.hom.app (op n))) ∧
      ∃ δ : ((completion S J₀).obj
          ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩).obj ≅
        ((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
            Scheme.Modules.tensorPullback g,
        α₀.hom ≫ δ.hom = eqToHom hG ≫
          Functor.whiskerRight α.hom (Scheme.Modules.tensorPullback g)
  obtain ⟨G₀, F₀, hD, hG, hF, hg, hI⟩ :=
    completedAffine_pullback_objects J f G F U
  let : Flat g := hg
  obtain ⟨adjR, β₀, κ₀, δ, t, hκ₀, hsquare, hunit⟩ :=
    formalComparison_flat_transport_square J f g J₀ hI adj G F β h κ hκ
      G₀ F₀ hD hG hF
  let α₀ : G₀ ⟶ (completion S J₀).obj
      ⟨(Scheme.Modules.pushforward (p)).obj F₀.obj, hD⟩ :=
    ⟨(eqToHom hG ≫ Functor.whiskerRight α.hom
      (Scheme.Modules.tensorPullback g)) ≫ δ.inv⟩
  have hδ : α₀.hom ≫ δ.hom = eqToHom hG ≫
      Functor.whiskerRight α.hom (Scheme.Modules.tensorPullback g) := by
    dsimp only [α₀]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨adjR, G₀, F₀, β₀, hD, κ₀, α₀, hG, hF, hκ₀, ?_, δ, hδ⟩
  intro n
  have hs := NatTrans.congr_app hsquare (op n)
  have hd := NatTrans.congr_app hδ (op n)
  exact transport_comparison_comp (Scheme.Modules.tensorPullback g)
    (α.hom.app (op n)) (κ.app (op n))
    (adj.unit.app (G.obj.obj (op n)) ≫
      (Scheme.Modules.pushforward f).map (β.hom.app (op n)))
    (α₀.hom.app (op n)) (κ₀.app (op n))
    (adjR.unit.app (G₀.obj.obj (op n)) ≫
      (Scheme.Modules.pushforward p).map (β₀.hom.app (op n)))
    ((eqToHom hG).app (op n)) (δ.hom.app (op n)) (t.app (op n))
    (hα n) hd hs (hunit n)

end AlgebraicGeometry
