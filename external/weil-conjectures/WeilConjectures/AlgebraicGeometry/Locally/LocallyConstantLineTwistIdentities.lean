/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwist
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DisjointOpenProductRestriction
import WeilConjectures.AlgebraicGeometry.SixFunctors.DisjointOpenIsoGluing
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-!
# Restriction, tensor and pullback for glued integer powers

## References

* EGA II, Remark 4.2.7
* Stacks, Tags 00AL and 00AM
* Tags 01CD and 01CR
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

private theorem degree_disjoint {X : Scheme.{u}} (d : LocallyConstant X ℤ)
    (i j : ℤ) (x : X) (hi : x ∈ lineDegreeOpen d i)
    (hj : x ∈ lineDegreeOpen d j) : i = j :=
  hi.symm.trans hj

/-- On an open where the degree is constantly `m`, the locally constant line twist restricts
to the `m`-th integer line power: the projection from the defining product to its `m`-th
factor, via `disjointOpenProductRestrictIso`. -/
noncomputable def locallyConstantLineTwistRestrictIso {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (d : LocallyConstant X ℤ) (m : ℤ) (U : X.Opens)
    (hU : ∀ x : X, x ∈ U → d x = m) :
    (tensorPullback U.ι).obj (locallyConstantLineTwist A hA d) ≅
      (tensorPullback U.ι).obj (integerLinePower A hA m) :=
  disjointOpenProductRestrictIso (lineDegreeOpen d) (fun _ _ _ hi hj ↦ hi.symm.trans hj)
    (integerLinePower A hA) m U (fun x hx ↦ hU x hx)

private noncomputable def pullback_unit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (tensorPullback f).obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules :=
  ((tensorPullbackSectionAdjunction f).leftAdjointUniq
    (pullbackPushforwardAdjunction f)).app _ ≪≫ pullbackObjUnitIso f

private theorem power_pullback {X Y : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (f : Y ⟶ X)
    (hAf : ((tensorPullback f).obj A).IsInvertible) (m : ℤ) :
    Nonempty ((tensorPullback f).obj (integerLinePower A hA m) ≅
      integerLinePower ((tensorPullback f).obj A) hAf m) := by
  classical
  let F := tensorPullback f
  let e := lineTensorInverse A hA
  let e' := lineTensorInverse (F.obj A) hAf
  obtain ⟨t, _⟩ := module_pullback_tensor f
  let dualIso : F.obj e.obj ≅ e'.obj :=
    e'.fullyFaithfulTensorLeft.preimageIso
      ((t A e.obj).symm ≪≫ F.mapIso e.rightIso ≪≫ pullback_unit f ≪≫ e'.rightIso.symm)
  have natPower (B : X.Modules) (B' : Y.Modules) (hB : F.obj B ≅ B') (n : ℕ) :
      Nonempty (F.obj (tensorPowNat B n) ≅ tensorPowNat B' n) := by
    induction n with
    | zero => exact ⟨pullback_unit f⟩
    | succ n ih => exact ⟨t B _ ≪≫ (hB ⊗ᵢ ih.some)⟩
  cases m with
  | ofNat n => exact natPower A (F.obj A) (Iso.refl _) n
  | negSucc n => exact natPower e.obj e'.obj dualIso (n + 1)

private theorem restriction_of_eq {X Y : Scheme.{u}} {g h : Y ⟶ X}
    (e : g = h) (M : X.Modules) :
    Nonempty ((tensorPullback g).obj M ≅ (tensorPullback h).obj M) := by
  subst h
  exact ⟨Iso.refl _⟩

/-- The tensor and pullback calculus of the concrete disjoint-stratum model of integer line
powers (the restriction identity is `locallyConstantLineTwistRestrictIso`).
These statements hold for any invertible module, independently of projective geometry. -/
theorem locallyConstantLineTwist_identities {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) :
    (∀ d e : LocallyConstant X ℤ,
      Nonempty (locallyConstantLineTwist A hA d ⊗ locallyConstantLineTwist A hA e ≅
        locallyConstantLineTwist A hA (d + e))) ∧
    (∀ (Y : Scheme.{u}) (f : Y ⟶ X)
      (hAf : ((tensorPullback f).obj A).IsInvertible) (d : LocallyConstant X ℤ),
      Nonempty ((tensorPullback f).obj (locallyConstantLineTwist A hA d) ≅
        locallyConstantLineTwist ((tensorPullback f).obj A) hAf (d.comap f.base.hom))) := by
  classical
  refine ⟨?_, ?_⟩
  · intro d e
    let U : ℤ × ℤ → X.Opens := fun p ↦ lineDegreeOpen d p.1 ⊓ lineDegreeOpen e p.2
    apply disjointOpen_nonempty_iso U
      (fun x ↦ ⟨(d x, e x), rfl, rfl⟩)
      (fun i j x hi hj ↦ Prod.ext (hi.1.symm.trans hj.1) (hi.2.symm.trans hj.2))
    intro p
    let P := tensorPullback (U p).ι
    obtain ⟨td, _⟩ := module_pullback_tensor (U p).ι
    let ed := locallyConstantLineTwistRestrictIso A hA d p.1 (U p) (fun _ hx ↦ hx.1)
    let ee := locallyConstantLineTwistRestrictIso A hA e p.2 (U p) (fun _ hx ↦ hx.2)
    let es := locallyConstantLineTwistRestrictIso A hA (d + e) (p.1 + p.2) (U p) (by
      intro x hx
      change d x + e x = p.1 + p.2
      rw [hx.1, hx.2])
    exact ⟨td _ _ ≪≫ (ed ⊗ᵢ ee) ≪≫ (td _ _).symm ≪≫
      P.mapIso ((lineTensorInverse A hA).addIso' p.1 p.2) ≪≫ es.symm⟩
  · intro Y f hAf d
    let d' := d.comap f.base.hom
    apply disjointOpen_nonempty_iso (lineDegreeOpen d')
      (fun y ↦ ⟨d' y, rfl⟩) (degree_disjoint d')
    intro m
    let V := lineDegreeOpen d' m
    let W := lineDegreeOpen d m
    let g : (V : Scheme.{u}) ⟶ W := f ∣_ W
    have hg : g ≫ W.ι = V.ι ≫ f := morphismRestrict_ι f W
    let P := tensorPullback V.ι
    let ed := locallyConstantLineTwistRestrictIso A hA d m W (fun _ hx ↦ hx)
    obtain ⟨ef⟩ := power_pullback A hA f hAf m
    let es := locallyConstantLineTwistRestrictIso ((tensorPullback f).obj A) hAf d' m V
      (fun _ hx ↦ hx)
    exact ⟨(tensorPullbackSectionComp V.ι f).symm.app _ ≪≫
      (restriction_of_eq hg.symm _).some ≪≫
      (tensorPullbackSectionComp g W.ι).app _ ≪≫
      (tensorPullback g).mapIso ed ≪≫
      (tensorPullbackSectionComp g W.ι).symm.app _ ≪≫
      (restriction_of_eq hg _).some ≪≫
      (tensorPullbackSectionComp V.ι f).app _ ≪≫ P.mapIso ef ≪≫ es.symm⟩

end AlgebraicGeometry.Scheme.Modules
