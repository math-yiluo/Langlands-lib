/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Cover.Directed
import WeilConjectures.AlgebraicGeometry.FpqcAffineModelTransitionCartesian
import WeilConjectures.AlgebraicGeometry.FpqcAffineModelTransitionReconstruction
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-!
# Transition maps between effective affine models

Source: Stacks Project, Descent, Tag 02W3, general-base proof (nested affine opens).
(blueprint: lem-galois-fpqc-affine-model-transitions)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Two effective affine models admit a Cartesian transition over an inclusion.
Source: Stacks Project, Descent, Tag 02W3, general-base proof; Tag 02W0.
(blueprint: lem-galois-fpqc-affine-model-transitions)

Proof: Restrict the model over B to U for an inclusion U into B. Its pullback
along X_U -> U and the U-model both identify with V_U. The compatibility with D
identifies their transports, so fpqc full faithfulness descends the comparison
isomorphism and its inverse. Compose with the projection to the B-model to get t.
The comparison isomorphism makes its square Cartesian. The equation with r is the
reconstruction equation of the descended morphism.
Base changes of the singleton fpqc covering are fpqc. This works also when U,
X_U or V_U is empty, and does not assume intersections of affine opens are affine. -/
theorem fpqc_affine_model_transition
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V)
    (E : ∀ U : S.affineOpens,
      Over.DescentDatum (pullback.snd f U.1.ι)
        (Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))))
    (hcompat : ∀ U : S.affineOpens,
        ∀ {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
          (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
          (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
          (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
            (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
              ← Category.assoc, hab])
            (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
              (by simpa [Category.assoc, pullback.condition] using
                  congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left =
            ((E U).transport a b hab x).left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
    (W : ∀ U : S.affineOpens, Over U.1.toScheme)
    (r : ∀ U : S.affineOpens,
      pullback V.hom (pullback.fst f U.1.ι) ⟶ (W U).left)
    (hp : ∀ U, IsPullback (r U) (pullback.snd V.hom (pullback.fst f U.1.ι))
      (W U).hom (pullback.snd f U.1.ι))
    (hinv : ∀ (U : S.affineOpens) {T : Scheme.{u}}
      (a b : T ⟶ pullback f U.1.ι)
      (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
      (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
      ((E U).transport a b hab x).left ≫ r U = x.left ≫ r U)
    {U B : S.affineOpens} (i : U ⟶ B) :
    ∃ t : (W U).left ⟶ (W B).left,
      IsPullback t (W U).hom (W B).hom (S.directedAffineCover.trans i) ∧
      Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫ r B =
        r U ≫ t := by
  have hq : Presieve.singleton (pullback.snd f U.1.ι) ∈
      Scheme.fpqcPrecoverage U.1.toScheme := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hf ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ f) hf U.1.ι
      (fun _ ↦ pullback.snd f U.1.ι) (fun _ ↦ pullback.fst f U.1.ι)
      (fun _ ↦ (IsPullback.of_hasPullback f U.1.ι).flip)
  have hrU : Presieve.singleton (r U) ∈ Scheme.fpqcPrecoverage (W U).left := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hq ⊢
    exact Precoverage.mem_coverings_of_isPullback
      (fun _ : PUnit.{1} ↦ pullback.snd f U.1.ι) hq (W U).hom
      (fun _ ↦ r U) (fun _ ↦ pullback.snd V.hom (pullback.fst f U.1.ι))
      (fun _ ↦ hp U)
  have : EffectiveEpi (r U) := by
    rw [← Sieve.effectiveEpimorphic_singleton,
      Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
    intro Z
    exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hrU)
  let c : pullback V.hom (pullback.fst f U.1.ι) ⟶
      pullback V.hom (pullback.fst f B.1.ι) :=
    Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i
  have he : ∀ {T : Scheme.{u}}
      (g h : T ⟶ pullback V.hom (pullback.fst f U.1.ι)),
      g ≫ r U = h ≫ r U → g ≫ (c ≫ r B) = h ≫ (c ≫ r B) := by
    intro T g h hgh
    exact fpqc_affine_model_transition_reconstruction f D E hcompat W r hp hinv i g h hgh
  let t : (W U).left ⟶ (W B).left := EffectiveEpi.desc (r U) (c ≫ r B) he
  have hrt : r U ≫ t = c ≫ r B := EffectiveEpi.fac _ _ he
  have ht : t ≫ (W B).hom = (W U).hom ≫ S.directedAffineCover.trans i := by
    apply (cancel_epi (r U)).mp
    rw [← Category.assoc, hrt, Category.assoc, (hp B).w]
    have hc : c ≫ pullback.snd V.hom (pullback.fst f B.1.ι) ≫
        pullback.snd f B.1.ι =
        pullback.snd V.hom (pullback.fst f U.1.ι) ≫ pullback.snd f U.1.ι ≫
          S.directedAffineCover.trans i := by
      dsimp [c, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
      simp
    simpa only [Category.assoc, ← (hp U).w_assoc] using hc
  exact ⟨t, fpqc_affine_model_transition_cartesian f hf W r hp i t ht hrt.symm,
    hrt.symm⟩

end AlgebraicGeometry
