/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Cover.Directed

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem transport_left_congr
    {X S T : Scheme.{u}} {f : X ⟶ S} {V : Over X} (D : Over.DescentDatum f V)
    {a b a' b' : T ⟶ X} {hab : a ≫ f = b ≫ f} {hab' : a' ≫ f = b' ≫ f}
    (x : Over.mk a ⟶ V) (y : Over.mk a' ⟶ V)
    (ha : a = a') (hb : b = b') (hxy : x.left = y.left) :
    (D.transport a b hab x).left = (D.transport a' b' hab' y).left := by
  subst a'
  subst b'
  have h : x = y := by ext; exact hxy
  subst y
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The map from the U-model's fpqc pullback to the B-model is constant on
pairs of points with the same image in the U-model.
Source: Stacks Project, Descent, Tag 02W3 (nested affine models), using Tag 02W0.
(blueprint: lem-galois-fpqc-affine-model-transition-reconstruction)

Proof: For two points g and h of V_U with equal composites to W_U, the Cartesian
square hp U gives equal composites to U. Let a and b be their images in X_U.
Transport g along E U from a to b. Invariance says its image in W_U is still that
of g, hence that of h, and its image in X_U is b. The universal property of hp U
therefore identifies the transported point with h. Write j : X_U -> X_B and
c : V_U -> V_B for the restriction maps. The two points a j and b j have the
same image in B. Compatibility hcompat U and hcompat B identifies the images
in V of their respective transports under E U and E B. Projection V_B -> V
is a monomorphism (a base change of the open immersion B -> S), so this equality
in V identifies c after E U-transport with E B-transport after c. Invariance
hinv B now identifies the images of g c and h c in W_B. This proof uses only
universal properties and monomorphisms, so includes empty opens and objects. -/
theorem fpqc_affine_model_transition_reconstruction
    {X S : Scheme.{u}} (f : X ⟶ S)
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
    {U B : S.affineOpens} (i : U ⟶ B)
    {T : Scheme.{u}}
    (g h : T ⟶ pullback V.hom (pullback.fst f U.1.ι))
    (hgh : g ≫ r U = h ≫ r U) :
    g ≫ Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫ r B =
      h ≫ Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫ r B := by
  let j : pullback f U.1.ι ⟶ pullback f B.1.ι :=
    Scheme.Cover.trans (S.directedAffineCover.pullback₁ f) i
  let c : pullback V.hom (pullback.fst f U.1.ι) ⟶
      pullback V.hom (pullback.fst f B.1.ι) :=
    Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i
  have cj : c ≫ pullback.snd V.hom (pullback.fst f B.1.ι) =
      pullback.snd V.hom (pullback.fst f U.1.ι) ≫ j := by
    dsimp [c, j, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp
  have cv : c ≫ pullback.fst V.hom (pullback.fst f B.1.ι) =
      pullback.fst V.hom (pullback.fst f U.1.ι) := by
    dsimp [c, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp
  have jf : j ≫ pullback.fst f B.1.ι = pullback.fst f U.1.ι := by
    dsimp [j, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp
  have js : j ≫ pullback.snd f B.1.ι =
      pullback.snd f U.1.ι ≫ S.directedAffineCover.trans i := by
    dsimp [j, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp
  let a := g ≫ pullback.snd V.hom (pullback.fst f U.1.ι)
  let b := h ≫ pullback.snd V.hom (pullback.fst f U.1.ι)
  have hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι := by
    simpa only [a, b, Category.assoc, (hp U).w] using
      congrArg (fun k ↦ k ≫ (W U).hom) hgh
  let x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι)) :=
    Over.homMk g
  have eh : ((E U).transport a b hab x).left = h := by
    apply (hp U).hom_ext
    · exact (hinv U a b hab x).trans hgh
    · exact Over.w _
  have habB : (a ≫ j) ≫ pullback.snd f B.1.ι =
      (b ≫ j) ≫ pullback.snd f B.1.ι := by
    simpa only [Category.assoc, js] using
      congrArg (fun k ↦ k ≫ S.directedAffineCover.trans i) hab
  let y : Over.mk (a ≫ j) ⟶ Over.mk (pullback.snd V.hom (pullback.fst f B.1.ι)) :=
    Over.homMk (g ≫ c) (by simp [Category.assoc, cj, a])
  have ey : ((E B).transport (a ≫ j) (b ≫ j) habB y).left = h ≫ c := by
    apply (cancel_mono (pullback.fst V.hom (pullback.fst f B.1.ι))).mp
    have hu := hcompat U a b hab x
    have hb := hcompat B (a ≫ j) (b ≫ j) habB y
    have hd :
        (D.transport ((a ≫ j) ≫ pullback.fst f B.1.ι)
          ((b ≫ j) ≫ pullback.fst f B.1.ι)
          (by simp only [Category.assoc, pullback.condition];
              rw [← Category.assoc, ← Category.assoc, habB]
              simp only [Category.assoc])
          (Over.homMk (y.left ≫ pullback.fst V.hom (pullback.fst f B.1.ι))
            (by simpa [Category.assoc, pullback.condition] using
              congrArg (fun z ↦ z ≫ pullback.fst f B.1.ι) (Over.w y)))).left =
        (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
          (by simp only [Category.assoc, pullback.condition];
              rw [← Category.assoc, ← Category.assoc, hab])
          (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
            (by simpa [Category.assoc, pullback.condition] using
              congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left := by
      apply transport_left_congr
      · simp only [Category.assoc, jf]
      · simp only [Category.assoc, jf]
      · simp only [x, y, Over.homMk_left, Category.assoc, cv]
    simpa only [eh, Category.assoc, cv] using hb.symm.trans (hd.trans hu)
  have hi := hinv B (a ≫ j) (b ≫ j) habB y
  simpa [ey, y, c, Category.assoc] using hi.symm

end AlgebraicGeometry
