/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Pulling back local quotient-module frames -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- Compare the tensor formula with the canonical left adjoint, then restrict it.
private noncomputable def tensorPullbackRestrictIso {X Y : Scheme.{u}}
    (p : X ⟶ Y) (W : Y.Opens) :
    Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.restrictFunctor (p ⁻¹ᵁ W).ι ≅
      Scheme.Modules.restrictFunctor W.ι ⋙ Scheme.Modules.pullback (p ∣_ W) := by
  let a := (Scheme.Modules.nonempty_tensorPullbackAdjunction p).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  exact Functor.isoWhiskerRight a _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback _) ≪≫
    Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι p W).symm ≪≫
    (Scheme.Modules.pullbackComp _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback W.ι).symm _

/-- Tensor pullback carries a local quotient-module frame to a structure-module frame.
Source: Stacks Project, Tags 08KS and 0095; closed-immersion counit and tensor pullback.
(blueprint: lem-u1-closed-immersion-quotient-frame-pullback).

Proof: The tensor formula and canonical scheme pullback are left adjoints to
pushforward, so the uniqueness of left adjoints identifies them. Compose the
canonical pullback composition and open-restriction isomorphisms to compare
restriction after tensor pullback with pullback after restriction. The counit
for the closed immersion is invertible by
closedImmersion_pushforward_fullyFaithful, so tensor pullback carries B to the
structure module. The tensor functor is a left adjoint and preserves coproducts:
apply PreservesCoproduct.iso and the coproduct of these counit isomorphisms to
identify its value on the J-indexed coproduct with the free sheaf on J.
Transport the supplied over-site isomorphism to the restricted scheme by
overEquiv, pull it back, and use the preceding restriction comparison in both
directions. Restrict the global free frame, then transport back through
overIsoFreeEquiv. Empty indexing types and empty opens satisfy the same
categorical identities; no finiteness, affineness, or derived object is used. -/
theorem closedImmersion_quotient_frame_pullback
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.Opens) (J : Type u) (G : Y.Modules)
    (e : G.over U ≅
      (∐ fun _ : J ↦ (Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf)).over U) :
    Nonempty (((Scheme.Modules.tensorPullback i).obj G).over (i ⁻¹ᵁ U) ≅
      SheafOfModules.free J) := by
  classical
  let T := Scheme.Modules.tensorPullback i
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let P : Y.Modules := ∐ fun _ : J ↦ B
  let a : T ⊣ Scheme.Modules.pushforward i :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction i)
  let := a.leftAdjoint_preservesColimits
  have hc : IsIso (a.counit.app (SheafOfModules.unit Z.ringCatSheaf)) :=
    (closedImmersion_pushforward_fullyFaithful i).1 _
  let b : T.obj B ≅ SheafOfModules.unit Z.ringCatSheaf :=
    asIso (a.counit.app (SheafOfModules.unit Z.ringCatSheaf))
  let c : T.obj P ≅ SheafOfModules.free J :=
    PreservesCoproduct.iso T (fun _ : J ↦ B) ≪≫ Sigma.mapIso (fun _ : J ↦ b)
  let r : G.restrict U.ι ≅ P.restrict U.ι :=
    ((Scheme.Modules.overFunctorEquiv U).app G).symm ≪≫
      (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
      (Scheme.Modules.overFunctorEquiv U).app P
  let d := tensorPullbackRestrictIso i U
  let q : (T.obj G).restrict (i ⁻¹ᵁ U).ι ≅ SheafOfModules.free J :=
    d.app G ≪≫ (Scheme.Modules.pullback (i ∣_ U)).mapIso r ≪≫
      (d.app P).symm ≪≫
      (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U).ι).mapIso c ≪≫
      Scheme.Modules.restrictFreeIso (i ⁻¹ᵁ U).ι J
  exact ⟨(Scheme.Modules.overIsoFreeEquiv (T.obj G) (i ⁻¹ᵁ U) J).symm q⟩

end AlgebraicGeometry
