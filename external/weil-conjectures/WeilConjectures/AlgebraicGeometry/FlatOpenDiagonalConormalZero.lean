/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.UniversalThickeningFlatBaseChange
import WeilConjectures.AlgebraicGeometry.OpenIsoConormalZero

/-!
# Vanishing of the conormal sheaf for a flat morphism with open diagonal

Source: Stacks Project, Tag 04FF, the conormal calculation.
(blueprint: lem-weil-pbc-flat-open-diagonal-conormal-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The conormal sheaf of any universal first order thickening vanishes when the
morphism is flat and its diagonal is an open immersion. No finite type assumption
is needed in this calculation.
Source: Stacks Project, Tag 04FF, proof, using Tags 04F9 and 04FA.
(blueprint: lem-weil-pbc-flat-open-diagonal-conormal-zero).
Proof: write p and q for the projections from X ×[S] X. The open diagonal makes f
formally unramified, and base change makes q formally unramified. Flat base change
of a universal thickening identifies p* C_f with C_q (04F9). On the open image D
of the diagonal, q is an isomorphism. Open restriction (04FA) identifies C_q|D
with the conormal of this isomorphism. The identity thickening of D is universal:
its lift of a test map is the composite with the inverse isomorphism. Uniqueness
of universal thickenings identifies its zero ideal with the ideal of any other
choice, so C_q|D is zero. Pull back the base-change identification along the
diagonal. Pullback along an open immersion is restriction, and Δ ≫ p = id_X;
composition and identity isomorphisms for tensor pullback therefore identify C_f
with the pullback of the zero module. Pullback preserves zero objects because it
is a left adjoint, so C_f is zero. -/
theorem flat_openDiagonal_conormal_isZero {X S X' : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsOpenImmersion (pullback.diagonal f)]
    (i : X ⟶ X') (s : X' ⟶ S) (H : IsUniversalFirstOrderThickening f i s) :
    IsZero (formallyUnramifiedConormal f i s H) := by
  classical
  let iZ : pullback f f ⟶ pullback f s :=
    pullback.lift (pullback.fst f f) (pullback.snd f f ≫ i) (by
      rw [Category.assoc, H.2.1, pullback.condition])
  have hfst : iZ ≫ pullback.fst f s = pullback.fst f f :=
    pullback.lift_fst _ _ _
  have hsnd : iZ ≫ pullback.snd f s = pullback.snd f f ≫ i :=
    pullback.lift_snd _ _ _
  obtain ⟨hu, HZ, _, hc⟩ :=
    universalFirstOrderThickening_flat_base_change f f i s H iZ hfst hsnd
  let := hu
  let := HZ.1.1
  let := H.1.1
  let c := Classical.choose ((Classical.choose_spec
    (Scheme.Modules.closedImmersion_conormal_functorial iZ i
      (pullback.snd f s) (pullback.snd f f) hsnd).2).2)
  have : IsIso c := hc c rfl
  have hd : pullback.diagonal f ≫ pullback.fst f f = 𝟙 X := by simp
  have : IsIso (pullback.diagonal f ≫ pullback.fst f f) := by rw [hd]; infer_instance
  have hz := open_iso_conormal_isZero (pullback.fst f f) iZ
    (pullback.fst f s) HZ (pullback.diagonal f)
  have hp := hz.of_iso
    ((Scheme.Modules.tensorPullback (pullback.diagonal f)).mapIso (asIso c))
  obtain ⟨ecomp⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (pullback.diagonal f) (pullback.snd f f)
  have hzcomp := hp.of_iso (ecomp.app (formallyUnramifiedConormal f i s H))
  have hd' : pullback.diagonal f ≫ pullback.snd f f = 𝟙 X := by simp
  rw [hd'] at hzcomp
  obtain ⟨eid⟩ := Scheme.Modules.nonempty_tensorPullbackId X
  exact hzcomp.of_iso (eid.app (formallyUnramifiedConormal f i s H)).symm

end AlgebraicGeometry
