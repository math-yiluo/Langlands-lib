/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.FormalComparisonCompletedAffineTransport
import WeilConjectures.AlgebraicGeometry.FormalComparisonCompleteBaseAlgebraization
import WeilConjectures.AlgebraicGeometry.CompletedAffineComplementBaseChange
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Algebraization of the completed affine comparison as an adjunction

Source: Stacks Project, Tag 088B, completed-base algebraization argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem compose_comparison_squares
    {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {a b : D} {a₀ b₀ a₁ b₁ : C}
    (m : a ⟶ b) (m₀ : a₀ ⟶ b₀) (m₁ : a₁ ⟶ b₁)
    (s : a ⟶ T.obj a₀) (t : b ⟶ T.obj b₀)
    (s₀ : a₀ ⟶ a₁) (t₀ : b₀ ⟶ b₁)
    (ht : m ≫ t = s ≫ T.map m₀) (ha : m₀ ≫ t₀ = s₀ ≫ m₁) :
    m ≫ (t ≫ T.map t₀) = (s ≫ T.map s₀) ≫ T.map m₁ := by
  rw [← Category.assoc, ht, Category.assoc, ← T.map_comp, ha, T.map_comp,
    Category.assoc]

-- The unchanged statement names its existential coherence witness without using it.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The completed affine comparison is the section map of an algebraized adjunction.
This supplies an algebraized source, a proper morphism and an isomorphism on its
pullback, together with the limit comparison square. It asserts no invertibility
of the comparison itself, either globally or on an open.

Source: Stacks Project, Tag 088B, proof, from flat completion base change through
algebraization of the formal pullback isomorphism; Tags 087W, 087X and 0883.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-adjunction-model)

Proof: Restrict the original data to U=Spec B, and form the base change of f along
Spec R -> Spec B -> Y, where R is the J(U)-adic completion. Completion is flat,
Noetherian, and has the same positive ideal-power quotients as B. Flat base change
identifies pushforward, quotient projections and adjunction units. Since the
quotient projections are epimorphisms, hκ specifies their comparison uniquely;
formal functions identifies its inverse limit with an isomorphism. The equation
hα therefore determines the completed comparison on inverse limits. Algebraize
G over R by the affine formal-module equivalence, obtaining A₀, and pull back F
to obtain F₀ on the proper base-changed scheme Z. Pullback commutes with formal
completion. Full faithfulness of completion on the proper scheme Z lifts β and
its inverse to inverse coherent maps, giving b. Proper coherent pushforward
supplies hD. The affine limit cones and formal functions give eA₀ and eD₀;
naturality and hα identify the limit map with the sections of the adjunction unit
followed by p_*b. For an arbitrary supplied adjunction, first absorb the natural
automorphism relating it to the standard adjunction into β; it remains invertible.
The complement of the extended ideal is the inverse image of the original
complement of K, so p is an isomorphism there by stability under base change.
If R is zero, the spectrum is empty and the same constructions apply. -/
theorem formalComparison_completed_affine_adjunction_model
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
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
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens,
      let B := Γ(Y, U.1)
      let R := AdicCompletion (J.ideal U) B
      let L := (K.ideal U).map (algebraMap B R)
      let Q := Scheme.IdealSheafData.ofIdealTop
        (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (CommRingCat.of R))
        (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
        (A₀ : CoherentModules (Spec (CommRingCat.of R))) (F₀ : CoherentModules Z)
        (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F₀.obj)
        (hD : RingedSpace.IsCoherent (Spec (CommRingCat.of R)).toRingedSpace
          ((Scheme.Modules.pushforward p).obj F₀.obj)),
        IsProper p ∧ IsIso (pullback.snd p (Scheme.Opens.ι Q.support.compl)) ∧
        ∃ eA₀ : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A₀.obj),
        ∃ eD₀ : limit (((completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
              SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj
                ((Scheme.Modules.pushforward p).obj F₀.obj)),
          lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD₀.hom =
          eA₀.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
            ((moduleSpecΓFunctor (R := CommRingCat.of R)).map
              (adjR.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map b.hom)) := by
  intro U
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
  let T := ModuleCat.restrictScalars (algebraMap B R)
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (J.ideal U)
  have : IsAdicComplete I R :=
    (IsAdicComplete.map_algebraMap_iff (J.ideal U) R).mpr
      (AdicCompletion.isAdicComplete (IsNoetherian.noetherian (J.ideal U)))
  obtain ⟨adjR, G₀, F₀, β₀, hD, κ₀, α₀, _, _, hκ₀, hα₀, eG, eD, ht⟩ :=
    formalComparison_completed_affine_transport J f adj G F β h κ α hκ hα U
  obtain ⟨A₀, b, eA₀, eD₀, ha⟩ :=
    formalComparison_complete_base_algebraization I J₀ rfl p adjR G₀ F₀ β₀
      hD κ₀ α₀ hκ₀ hα₀
  refine ⟨Z, p, adjR, A₀, F₀, b, hD, inferInstance,
    completedAffine_complement_base_change J K f hV U,
    eG ≪≫ T.mapIso eA₀, eD ≪≫ T.mapIso eD₀, ?_⟩
  exact compose_comparison_squares T _ _ _ _ _ _ _ ht ha

end AlgebraicGeometry
