/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Base change of the spectrum of a polynomial quotient

For a scheme `S` and a polynomial `P` over `Γ(S, ⊤)`, the `S`-scheme
`adjoinRootCover S P` is the base change along `S.toSpecΓ` of `Spec Γ(S)[T]/(P)`. Its
morphisms from an `S`-scheme `Z` are the roots of `P` in `Γ(Z, ⊤)`: this is the universal
property used for the Artin–Schreier cover (blueprint: lemma-artin-schreier-character-sheaf, step
(2); lem-weil-pbc-morphism-into-affine-scheme).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (P : Polynomial Γ(S, ⊤))

/-- The base change along `S.toSpecΓ` of the spectrum of `Γ(S)[T]/(P)`, as an `S`-scheme. -/
def adjoinRootCover : Over S :=
  Over.mk (pullback.fst S.toSpecΓ
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))))

/-- The projection of `adjoinRootCover S P` to `Spec Γ(S)[T]/(P)`. -/
def adjoinRootCoverSnd : (adjoinRootCover S P).left ⟶ Spec (.of (AdjoinRoot P)) :=
  pullback.snd S.toSpecΓ (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P))))

/-- The ring map `Γ(S)[T]/(P) → Γ(adjoinRootCover S P, ⊤)` on global sections. -/
def adjoinRootCoverRingHom : AdjoinRoot P →+* Γ((adjoinRootCover S P).left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (AdjoinRoot P))).inv ≫ (adjoinRootCoverSnd S P).appTop).hom

/-- The class of `T` on `adjoinRootCover S P`. -/
def adjoinRootCoverRoot : Γ((adjoinRootCover S P).left, ⊤) :=
  adjoinRootCoverRingHom S P (AdjoinRoot.root P)

/-- On the image of `Γ(S)`, the ring map on global sections is the structure map. -/
lemma adjoinRootCoverRingHom_of (r : Γ(S, ⊤)) :
    adjoinRootCoverRingHom S P (AdjoinRoot.of P r) = (adjoinRootCover S P).hom.appTop r := by
  have h := congr_arg (fun g ↦ ((Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ g.appTop) r)
    (pullback.condition (f := S.toSpecΓ)
      (g := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))))
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h
  have e := (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (AdjoinRoot P)))) r).symm
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at e
  exact (h.trans (congr_arg _ e)).symm

lemma adjoinRootCoverRingHom_comp_of :
    (adjoinRootCoverRingHom S P).comp (AdjoinRoot.of P) = (adjoinRootCover S P).hom.appTop.hom :=
  RingHom.ext (adjoinRootCoverRingHom_of S P)

/-- The class of `T` is a root of `P`. -/
lemma eval₂_adjoinRootCoverRoot :
    P.eval₂ (adjoinRootCover S P).hom.appTop.hom (adjoinRootCoverRoot S P) = 0 := by
  rw [← adjoinRootCoverRingHom_comp_of, adjoinRootCoverRoot, ← Polynomial.hom_eval₂,
    AdjoinRoot.eval₂_root, map_zero]

variable {S P}

/-- Two morphisms into `adjoinRootCover S P` over `S` agree if they pull back the class of `T`
to the same function. -/
lemma adjoinRootCover_hom_ext {Z : Scheme.{u}} {s s' : Z ⟶ (adjoinRootCover S P).left}
    (h : s ≫ (adjoinRootCover S P).hom = s' ≫ (adjoinRootCover S P).hom)
    (hT : s.appTop (adjoinRootCoverRoot S P) = s'.appTop (adjoinRootCoverRoot S P)) :
    s = s' := by
  refine pullback.hom_ext h (ext_to_Spec ?_)
  have key : s.appTop.hom.comp (adjoinRootCoverRingHom S P) =
      s'.appTop.hom.comp (adjoinRootCoverRingHom S P) := by
    refine AdjoinRoot.ringHom_ext ?_ hT
    rw [RingHom.comp_assoc, RingHom.comp_assoc, adjoinRootCoverRingHom_comp_of,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h]
  exact CommRingCat.hom_ext key

/-- The morphism into `adjoinRootCover S P` over `g : Z ⟶ S` determined by a root `t` of `P`
in `Γ(Z, ⊤)`. -/
def adjoinRootCoverLift {Z : Scheme.{u}} (g : Z ⟶ S) (t : Γ(Z, ⊤))
    (ht : P.eval₂ g.appTop.hom t = 0) : Z ⟶ (adjoinRootCover S P).left :=
  pullback.lift g (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (AdjoinRoot.lift g.appTop.hom t ht)))
    (by
      rw [Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
      congr 2
      ext r
      simp)

@[reassoc (attr := simp)]
lemma adjoinRootCoverLift_hom {Z : Scheme.{u}} (g : Z ⟶ S) (t : Γ(Z, ⊤))
    (ht : P.eval₂ g.appTop.hom t = 0) :
    adjoinRootCoverLift g t ht ≫ (adjoinRootCover S P).hom = g :=
  pullback.lift_fst _ _ _

@[simp]
lemma adjoinRootCoverLift_appTop_root {Z : Scheme.{u}} (g : Z ⟶ S) (t : Γ(Z, ⊤))
    (ht : P.eval₂ g.appTop.hom t = 0) :
    (adjoinRootCoverLift g t ht).appTop (adjoinRootCoverRoot S P) = t := by
  have h : adjoinRootCoverLift g t ht ≫ adjoinRootCoverSnd S P =
      Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (AdjoinRoot.lift g.appTop.hom t ht)) :=
    pullback.lift_snd _ _ _
  rw [adjoinRootCoverRoot, adjoinRootCoverRingHom, CommRingCat.hom_comp, RingHom.comp_apply,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop,
    ← CommRingCat.comp_apply, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp

/-- Morphisms `Z ⟶ adjoinRootCover S P` over `g : Z ⟶ S` are the roots of `P` in `Γ(Z, ⊤)`. -/
lemma exists_adjoinRootCover_lift {Z : Scheme.{u}} (g : Z ⟶ S) (t : Γ(Z, ⊤))
    (ht : P.eval₂ g.appTop.hom t = 0) :
    ∃ s : Z ⟶ (adjoinRootCover S P).left, s ≫ (adjoinRootCover S P).hom = g ∧
      s.appTop (adjoinRootCoverRoot S P) = t :=
  ⟨adjoinRootCoverLift g t ht, adjoinRootCoverLift_hom g t ht,
    adjoinRootCoverLift_appTop_root g t ht⟩

/-- The class of `T` pulled back along a morphism over `S` is a root of `P`. -/
lemma eval₂_appTop_adjoinRootCoverRoot {Z : Scheme.{u}} (s : Z ⟶ (adjoinRootCover S P).left) :
    P.eval₂ (s ≫ (adjoinRootCover S P).hom).appTop.hom (s.appTop (adjoinRootCoverRoot S P)) =
      0 := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← Polynomial.hom_eval₂,
    eval₂_adjoinRootCoverRoot, map_zero]

end AlgebraicGeometry
