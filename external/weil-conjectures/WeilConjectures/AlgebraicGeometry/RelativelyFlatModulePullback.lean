/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks
import WeilConjectures.AlgebraicGeometry.PullbackStalkRelativeFlatExtension

/-! # Relative flatness of a module after base change

Source: Stacks Project, Tag 0A1H, affine reduction; Tag 051D, base change of flat modules.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Tensor pullback in a scheme base change preserves flatness over the base.
Source: Stacks Project, Tag 0A1H, affine reduction; Tag 051D, base change of flat modules.
Proof: since F is quasi-coherent, the affine-section condition IsFlatOver is
equivalent to relative stalk flatness (Stacks Tag 01U4). Fix a point z of X ×_S T,
with images x in X, t in T and s in S.
Choose affine neighbourhoods on which the square is described by rings A over R
and B over R. The local ring of the fibre product is a localization of A tensor_R B.
The tensor-pullback stalk is the corresponding localization of F_x tensor_R B,
with the further localizations identifying the given stalk actions. Since F_x is flat
over O_{S,s}, scalar extension gives a flat module over the corresponding localization
of B. Localization in the source ring is a filtered colimit of copies of this flat
module, hence preserves flatness over the localized base ring O_{T,t}.
The tensor-pullback stalk isomorphism transports this flatness to the recorded module.
Ordinary pullback preserves quasi-coherence. On affine opens V of T and W of the
fibre product mapping into V, its sections form a module N over the coordinate
ring of W. The stalk calculations give flatness of every localization N_q over
the corresponding localized base ring. By the affine local criterion of Tag 01U4,
N is flat over the coordinate ring of V. This is precisely the conclusion IsFlatOver.
The assertion is vacuous on an empty fibre product.
No finite presentation, proper support, or flatness of the base-change morphism is used.
Quasi-coherence is needed to recover the affine-section condition from stalks.
(blueprint: lem-pc-relatively-flat-module-pullback). -/
theorem relativelyFlat_module_pullback
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (hflat : F.IsFlatOver f) :
    (Scheme.Modules.tensorPullbackObj (pullback.fst f p) F).IsFlatOver
      (pullback.snd f p) := by
  let a := pullback.fst f p
  let b := pullback.snd f p
  let e := (Scheme.Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction a)
  have : (Scheme.Modules.tensorPullbackObj a F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f p).ringCatSheaf).prop_of_iso
      (e.app F).symm
      (inferInstanceAs (((Scheme.Modules.pullback a).obj F).IsQuasicoherent))
  apply relative_flat_of_stalks b
  intro z
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace (a z)).obj F
  have hM : Module.Flat (S.presheaf.stalk (f (a z)))
      ((ModuleCat.restrictScalars (f.stalkMap (a z)).hom).obj M) := by
    let := (f.stalkMap (a z)).hom.toAlgebra
    exact relative_flat_module_stalk f F hflat (a z) rfl
  have hE := pullback_stalk_relative_flat_extension f p z M hM
  obtain ⟨d, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso a z
  let k := (ModuleCat.restrictScalars (b.stalkMap z).hom).mapIso (d.app F)
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hE k.toLinearEquiv

end AlgebraicGeometry
