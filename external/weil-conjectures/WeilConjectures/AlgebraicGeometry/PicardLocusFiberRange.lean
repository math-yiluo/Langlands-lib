/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism

/-!
# Points of the universal Picard pullback locus

Source: Stacks Project, Tag 0BDP, evaluated on residue fields.
(blueprint: lem-sc-picard-locus-fiber-range).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorPullbackIsoPullback {A B : Scheme.{u}} (g : A ⟶ B) :
    Modules.tensorPullback g ≅ Modules.pullback g :=
  (Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction g)

/-- The points of an immersion representing descent of an invertible module are exactly
its trivial-fibre locus, when the family has a section.

Source: Stacks Project, Tag 0BDP and the proof of Tag 0BF4
(blueprint: lem-sc-picard-locus-fiber-range).

Proof: A point s lies in the image of the immersion j precisely when the residue-field
morphism Spec κ(s) → S factors through j: an immersion identifies the residue field at
a point of its domain with that at its image. Evaluate hZ on this morphism. Its right side
says L on the fibre is the pullback of a finite locally free N on Spec κ(s). Pull this
isomorphism back along the base change of the section of f. The result
identifies N with a pullback of the invertible module L, so N is invertible. An invertible
module on the one-point scheme Spec κ(s) is trivial, and so is L on the fibre. Conversely, a
trivial fibre satisfies hZ with N equal to the structure module. To compare the tensor
pullback in hZ with Modules.pullback, use uniqueness of left adjoints to Modules.pushforward;
transport the structure module along that natural isomorphism. These arguments prove
both inclusions in the asserted equality. No flatness or properness is needed here. -/
theorem range_eq_setOf_nonempty_pullback_fiber_iso_unit
    {P S T : Scheme.{u}} (f : P ⟶ S) (σ : S ⟶ P) (hσ : σ ≫ f = 𝟙 S)
    (L : P.Modules) [L.IsInvertible] (j : T ⟶ S) [IsImmersion j]
    (hZ : ∀ {B : Scheme.{u}} (g : B ⟶ S),
      (∃ h : B ⟶ T, h ≫ j = g) ↔
        ∃ (N : B.Modules) (_ : N.IsFiniteLocallyFree),
          Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj L ≅
            (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    Set.range j = {s : S | Nonempty ((Modules.pullback (f.fiberι s)).obj L ≅
      SheafOfModules.unit _)} := by
  ext s
  let g := S.fromSpecResidueField s
  let q := pullback.fst f g
  let p := pullback.snd f g
  constructor
  · intro hs
    have hgs : g (IsLocalRing.closedPoint (S.residueField s)) = s :=
      Scheme.fromSpecResidueField_apply s _
    obtain ⟨h, hh⟩ := exists_comp_eq_of_mem_range j g (hgs.symm ▸ hs)
    obtain ⟨N, hN, ⟨e⟩⟩ := (hZ g).mp ⟨h, hh⟩
    let d : (Modules.pullback q).obj L ≅ (Modules.pullback p).obj N :=
      (tensorPullbackIsoPullback q).symm.app L ≪≫ e ≪≫
        (tensorPullbackIsoPullback p).app N
    let r : Spec (S.residueField s) ⟶ pullback f g :=
      pullback.lift (g ≫ σ) (𝟙 _) (by simp [hσ])
    have hr : r ≫ p = 𝟙 _ := pullback.lift_snd _ _ _
    let d' : (Modules.pullback (r ≫ q)).obj L ≅ N :=
      (Modules.pullbackComp r q).symm.app L ≪≫ (Modules.pullback r).mapIso d ≪≫
        (Modules.pullbackComp r p).app N ≪≫ (Modules.pullbackCongr hr).app N ≪≫
        (Modules.pullbackId _).app N
    have : N.IsInvertible := Modules.IsInvertible.of_iso d'
    obtain ⟨eN⟩ := Modules.IsInvertible.nonempty_iso_unit
      (IsLocalRing.closedPoint (S.residueField s)) N
    exact ⟨d ≪≫ (Modules.pullback p).mapIso eN ≪≫ Modules.pullbackObjUnitIso p⟩
  · rintro ⟨e⟩
    have : SheafOfModules.IsInvertible.{u, u, u}
        (SheafOfModules.unit (Spec (S.residueField s)).ringCatSheaf) :=
      SheafOfModules.instIsInvertibleUnit.{u, u, u}
    have hunit := SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u}
      (SheafOfModules.unit (Spec (S.residueField s)).ringCatSheaf)
    obtain ⟨h, hh⟩ := (hZ g).mpr ⟨SheafOfModules.unit _, hunit,
      ⟨(tensorPullbackIsoPullback q).app L ≪≫ e ≪≫
        (Modules.pullbackObjUnitIso p).symm ≪≫
        (tensorPullbackIsoPullback p).symm.app _⟩⟩
    refine ⟨h (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
    have he := congrArg (fun k : Spec (S.residueField s) ⟶ S ↦
      k (IsLocalRing.closedPoint (S.residueField s))) hh
    simpa [g, Hom.comp_apply] using he

end AlgebraicGeometry.Scheme
