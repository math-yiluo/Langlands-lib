/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.FieldPullbackRankOneTrivial

/-! # Triviality of descended Picard coefficients on the source fibre -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A fibrewise descended invertible coefficient is trivial when the structure unit
is universally invertible.
Source: Stacks Project, Tag 0BF2, reduction to the structure coefficient; Tag 0BDP.
(blueprint: lem-sc-picard-descended-fibre-coefficient-trivial)

Proof: Apply the structure unit at Spec kappa(s). If the source fibre were empty,
its structure module and its pushforward would be zero. The invertible unit would
then identify the nonzero structure module on Spec kappa(s) with zero, a
contradiction. Thus the fibre is nonempty. Write the supplied descent as an
isomorphism between L_s and the pullback of the finite locally free N. Tensor
pullback preserves invertibility, so this pullback of N is invertible. Apply
nonempty_iso_unit_of_invertible_field_pullback to obtain N isomorphic to the
structure module of the field spectrum. Pull back this isomorphism and compose
with the descent isomorphism and the pullback-unit isomorphism. This constructs
a trivialization of L_s, with no choice of a witness from mere existence used
as data of a definition. -/
theorem picard_descended_fibre_coefficient_trivial
    {X S : Scheme.{v}} (f : X ⟶ S)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (s : S)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf) := by
  classical
  let g := pullback.snd f (S.fromSpecResidueField s)
  let h := pullback.fst f (S.fromSpecResidueField s)
  let tensorIso (A B : Scheme.{v}) (q : A ⟶ B) :
      Modules.tensorPullback q ≅ Modules.pullback q :=
    (Modules.nonempty_tensorPullbackAdjunction q).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction q)
  have hnonempty : Nonempty (pullback f (S.fromSpecResidueField s) : Scheme.{v}) := by
    by_contra hn
    have : IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{v}) :=
      not_nonempty_iff.mp hn
    let M := (Modules.tensorPullback g).obj
      (SheafOfModules.unit (Spec (S.residueField s)).ringCatSheaf)
    have hz : IsZero M := Modules.isZero_of_isEmpty M
    have hzpush := (Modules.pushforward g).map_isZero hz
    have hu := hO (S.fromSpecResidueField s)
    let η := (Classical.choose (Modules.exists_tensorPullbackAdjunction g)).unit.app
      (SheafOfModules.unit (Spec (S.residueField s)).ringCatSheaf)
    have : IsIso η := hu
    exact Modules.not_isZero_unit (Spec (S.residueField s)) (hzpush.of_iso (asIso η))
  have : Nonempty (pullback f (S.fromSpecResidueField s) : Scheme.{v}) := hnonempty
  obtain ⟨N, hN, ⟨e⟩⟩ := hLs
  have : N.IsFiniteLocallyFree := hN
  have hinv : ((Modules.tensorPullback h).obj L).IsInvertible :=
    Modules.IsInvertible.of_iso ((tensorIso _ _ h).app L).symm
  have : ((Modules.tensorPullback g).obj N).IsInvertible :=
    Modules.IsInvertible.of_iso e
  obtain ⟨eN⟩ := Modules.nonempty_iso_unit_of_invertible_field_pullback
    (S.residueField s) g N
  exact ⟨e ≪≫ (Modules.tensorPullback g).mapIso eN ≪≫
    (tensorIso _ _ g).app _ ≪≫ Modules.pullbackObjUnitIso g⟩

end AlgebraicGeometry.Scheme
