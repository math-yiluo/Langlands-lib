/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
import WeilConjectures.AlgebraicGeometry.FieldPullbackRankOneTrivial

/-! # A free generator on the descended marked fibre
Source: Stacks Project, Tag 0BF2, fibre triviality before the perfect-complex argument.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- Fibre descent and universal structure pushforward give a generator on the marked fibre.
Source: Stacks Project, Tag 0BF2, the reduction to a trivial bundle on the marked fibre.
(blueprint: lem-sc-picard-h1-base-descent-fibre-generator)

Proof: The immersion k identifies κ(w) with κ(s). Transport hLs across this identification.
The descended module N over Spec κ(s) is finite free. Its rank is one: the fibre
pullback of L is invertible, and the universal structure-pushforward unit implies that
the fibre structure morphism is surjective. A nonzero fibre point therefore detects
the rank of N. Choose a basis of this one-dimensional vector space, pull it back, and
transport it through the descent isomorphism to obtain a global free generator.
This generates locally at every fibre point. If the fibre were empty, its pushforward
could not be the nonzero structure module of Spec κ(s), so this case is excluded by hO.
No H1 injectivity or target-family descent is used. -/
theorem picard_h1_base_descent_fibre_generator {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    ∃ τ : Γ((Modules.tensorPullback
      (pullback.fst f (W.fromSpecResidueField w ≫ k))).obj L, ⊤),
      ∀ y : (pullback f (W.fromSpecResidueField w ≫ k) : Scheme.{v}),
        Modules.GeneratesAt τ y := by
  classical
  subst s
  let gs := S.fromSpecResidueField (k w)
  let gw := W.fromSpecResidueField w ≫ k
  let a : Spec (W.residueField w) ⟶ Spec (S.residueField (k w)) :=
    Spec.map (k.residueFieldMap w)
  have ha : a ≫ gs = gw := by
    exact k.SpecMap_residueFieldMap_fromSpecResidueField w
  let q : pullback f gw ⟶ pullback f gs :=
    pullback.lift (pullback.fst f gw) (pullback.snd f gw ≫ a) (by
      rw [Category.assoc, ha, pullback.condition])
  have hq : q ≫ pullback.fst f gs = pullback.fst f gw := pullback.lift_fst _ _ _
  by_cases hY : Nonempty (pullback f gs : Scheme.{v})
  · let := hY
    obtain ⟨N, hN, ⟨e⟩⟩ := hLs
    let := hN
    let c (A B : Scheme.{v}) (g : A ⟶ B) : Modules.tensorPullback g ≅ Modules.pullback g :=
      (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction g)
    have : ((Modules.tensorPullback (pullback.fst f gs)).obj L).IsInvertible :=
      Modules.IsInvertible.of_iso ((c _ _ _).app L).symm
    have : ((Modules.tensorPullback (pullback.snd f gs)).obj N).IsInvertible :=
      Modules.IsInvertible.of_iso e
    obtain ⟨eN⟩ := Modules.nonempty_iso_unit_of_invertible_field_pullback
      (S.residueField (k w)) (pullback.snd f gs) N
    let es : (Modules.pullback (pullback.fst f gs)).obj L ≅
        SheafOfModules.unit (pullback f gs).ringCatSheaf :=
      ((c _ _ _).app L).symm ≪≫ e ≪≫
        (Modules.tensorPullback (pullback.snd f gs)).mapIso eN ≪≫
        (c _ _ _).app _ ≪≫ Modules.pullbackObjUnitIso _
    let ew : (Modules.tensorPullback (pullback.fst f gw)).obj L ≅
        SheafOfModules.unit (pullback f gw).ringCatSheaf :=
      (c _ _ _).app L ≪≫ (Modules.pullbackCongr hq.symm).app L ≪≫
        (Modules.pullbackComp q (pullback.fst f gs)).symm.app L ≪≫
        (Modules.pullback q).mapIso es ≪≫ Modules.pullbackObjUnitIso q
    refine ⟨ew.inv.app ⊤ (1 : Γ(pullback f gw, ⊤)), fun y ↦ ⟨⊤, trivial, ?_⟩⟩
    simpa using (Modules.isFreeGenerator_one (⊤ : (pullback f gw).Opens)).app_hom ew.symm
  · refine ⟨0, fun y ↦ False.elim (hY ⟨q y⟩)⟩

end AlgebraicGeometry.Scheme
