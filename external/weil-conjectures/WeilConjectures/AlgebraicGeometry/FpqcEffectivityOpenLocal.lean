/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Cover.Directed
import WeilConjectures.AlgebraicGeometry.FpqcAffineModelsGlue

/-! Effectivity is local on an affine open cover of the base. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem transport_left_congr {X S T : Scheme.{u}} {f : X ⟶ S}
    {V : Over X} (D : Over.DescentDatum f V) (a b a' b' : T ⟶ X)
    (h : a ≫ f = b ≫ f) (h' : a' ≫ f = b' ≫ f)
    (x x' : T ⟶ V.left) (hx : x ≫ V.hom = a) (hx' : x' ≫ V.hom = a')
    (ha : a = a') (hb : b = b') (he : x = x') :
    (D.transport a b h (Over.homMk x hx)).left =
      (D.transport a' b' h' (Over.homMk x' hx')).left := by
  cases ha
  cases hb
  cases he
  rfl

/-- Effectivity follows from effective, transport-compatible affine-open restrictions.
Source: Stacks Project, Descent, Tag 02W3, final paragraph of the general-base proof.
(blueprint: lem-galois-fpqc-effectivity-open-local)

First glue the models to obtain a global pullback projection q which is invariant
for test schemes mapping into an affine open of S. For arbitrary test points
f₁ and f₂ with the same image in S, cover their source T by the inverse images
of the affine opens of S. On each member, lift f₁, f₂ and the given point of V
to the chosen pullbacks. Local invariance of q gives the desired equality there.
Naturality of D identifies this transported lifted point with the restriction
of the original transported point. The morphism extensionality theorem for the
open cover of T proves the equality globally. This supplies global transport
invariance while retaining the pullback square, and hence proves effectivity. -/
theorem fpqc_isEffective_of_affine_open_restrictions
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X} (D : Over.DescentDatum f V)
    (hlocal : ∀ U : S.affineOpens,
      ∃ E : Over.DescentDatum (pullback.snd f U.1.ι)
          (Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
        E.IsEffective ∧
        ∀ {T : Scheme.{u}} (a b : T ⟶ pullback f U.1.ι)
          (hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι)
          (x : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι))),
          (D.transport (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
            (by simp only [Category.assoc, pullback.condition]; rw [← Category.assoc,
              ← Category.assoc, hab])
            (Over.homMk (x.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
              (by simpa [Category.assoc, pullback.condition] using
                  congrArg (fun z ↦ z ≫ pullback.fst f U.1.ι) (Over.w x)))).left =
            (E.transport a b hab x).left ≫ pullback.fst V.hom (pullback.fst f U.1.ι)) :
    D.IsEffective := by
  obtain ⟨W, q, hp, hq⟩ := fpqc_affine_effective_models_glue f hf D hlocal
  refine ⟨W, q, hp, ?_⟩
  intro T f₁ f₂ h x
  let 𝒰 : T.OpenCover := S.directedAffineCover.pullback₁ (f₁ ≫ f)
  apply Scheme.Cover.hom_ext 𝒰
  intro U
  change S.affineOpens at U
  dsimp only [𝒰, Scheme.directedAffineCover] at *
  let a : pullback (f₁ ≫ f) U.1.ι ⟶ pullback f U.1.ι :=
    pullback.lift (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₁) (pullback.snd (f₁ ≫ f) U.1.ι) (by
      exact pullback.condition (f := f₁ ≫ f) (g := U.1.ι))
  let b : pullback (f₁ ≫ f) U.1.ι ⟶ pullback f U.1.ι :=
    pullback.lift (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₂) (pullback.snd (f₁ ≫ f) U.1.ι) (by
      rw [Category.assoc, ← h]
      exact pullback.condition (f := f₁ ≫ f) (g := U.1.ι))
  have hab : a ≫ pullback.snd f U.1.ι = b ≫ pullback.snd f U.1.ι := by
    simp [a, b]
  let y : Over.mk a ⟶ Over.mk (pullback.snd V.hom (pullback.fst f U.1.ι)) :=
    Over.homMk (pullback.lift (pullback.fst (f₁ ≫ f) U.1.ι ≫ x.left) a (by
      simp [a, Category.assoc, Over.w x])) (by simp)
  have ha : a ≫ pullback.fst f U.1.ι = pullback.fst (f₁ ≫ f) U.1.ι ≫ f₁ := by
    exact pullback.lift_fst _ _ _
  have hb : b ≫ pullback.fst f U.1.ι = pullback.fst (f₁ ≫ f) U.1.ι ≫ f₂ := by
    exact pullback.lift_fst _ _ _
  have hy : y.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι) =
      pullback.fst (f₁ ≫ f) U.1.ι ≫ x.left := by
    exact pullback.lift_fst _ _ _
  have hh := hq U a b hab y
  have hn := congrArg (fun z ↦ z.left ≫ q)
    (D.transport_homMk_comp (pullback.fst (f₁ ≫ f) U.1.ι) f₁ f₂ h x)
  have hh' : (D.transport (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₁)
      (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₂)
      (by rw [Category.assoc, Category.assoc, h])
      ((Over.homMk (pullback.fst (f₁ ≫ f) U.1.ι) :
        Over.mk (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₁) ⟶ Over.mk f₁) ≫ x)).left ≫ q =
      pullback.fst (f₁ ≫ f) U.1.ι ≫ x.left ≫ q := by
    have hc := transport_left_congr D
      (a ≫ pullback.fst f U.1.ι) (b ≫ pullback.fst f U.1.ι)
      (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₁) (pullback.fst (f₁ ≫ f) U.1.ι ≫ f₂)
      (by simp only [Category.assoc, pullback.condition]
          rw [← Category.assoc, ← Category.assoc, hab])
      (by rw [Category.assoc, Category.assoc, h])
      (y.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι))
      (pullback.fst (f₁ ≫ f) U.1.ι ≫ x.left)
      (by rw [hy, ha]; simp [Category.assoc, Over.w x])
      (by simp [Category.assoc, Over.w x]) ha hb hy
    calc
      _ = (D.transport (a ≫ pullback.fst f U.1.ι)
          (b ≫ pullback.fst f U.1.ι) _ (Over.homMk
            (y.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι)))).left ≫ q := by
        rw [hc]
        rfl
      _ = y.left ≫ pullback.fst V.hom (pullback.fst f U.1.ι) ≫ q := hh
      _ = pullback.fst (f₁ ≫ f) U.1.ι ≫ x.left ≫ q := by rw [← Category.assoc, hy, Category.assoc]
  change pullback.fst (f₁ ≫ f) U.1.ι ≫ (D.transport f₁ f₂ h x).left ≫ q =
    pullback.fst (f₁ ≫ f) U.1.ι ≫ x.left ≫ q
  simpa only [Over.comp_left, Over.homMk_left, Category.assoc] using hn.symm.trans hh'

end AlgebraicGeometry
