/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
/-! Pro-etale covering refinements across a surjective closed immersion. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open AffineProEt
set_option backward.isDefEq.respectTransparency false in
private theorem quotient_cover_lift (A : Type u) [CommRing A] (I : Ideal A)
    (hi : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    (C : Cover.{u} proetalePrecoverage (Spec (.of (A ⧸ I)))) :
    ∃ B : Cover.{u} proetalePrecoverage (Spec (.of A)), ∀ b,
      ∃ (a : C.I₀) (r : pullback (B.f b)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶ C.X a),
        r ≫ C.f a = pullback.snd _ _ := by
  classical
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let := hi
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let O : Z.AffineProEt := .ofEtale (𝟙 Z)
  have hweak (a : C.I₀) : WeaklyEtale (C.f a) :=
    ((ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mp C.mem₀.2).2 a
  let V : C.I₀ → Z.ProEt := fun a ↦ ProEt.mk (C.f a)
  let f : ∀ a, V a ⟶ (AffineProEt.toProEt Z).obj O := fun a ↦
    MorphismProperty.Over.homMk (C.f a) (by exact Category.comp_id _)
  have hf : Presieve.ofArrows V f ∈ ProEt.precoverage Z _ := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact C.mem₀
  let T : Sieve ((AffineProEt.toProEt Z).obj O) := Sieve.ofArrows V f
  have hT : T ∈ ProEt.topology Z _ :=
    Precoverage.generate_mem_toGrothendieck hf
  have hT' : T.functorPullback (AffineProEt.toProEt Z) ∈ AffineProEt.topology Z O :=
    Functor.mem_restrictedTopology_iff.mpr
      (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨T, hT⟩)
  obtain ⟨κ, hκ, W, g, hg, hcover⟩ :=
    exists_finite_jointly_surjective_of_mem_topology hT'
  let := hκ
  have hh (b : κ) : ∃ (a : C.I₀) (r : (W b).left ⟶ C.X a),
      r ≫ C.f a = (W b).hom := by
    obtain ⟨a, r, hr⟩ := Sieve.ofArrows.exists (hg b)
    exact ⟨a, r.left, MorphismProperty.Over.w r⟩
  choose a r hr using hh
  let L : κ → X.AffineProEt := fun b ↦ (closedSiteLift A I).obj (W b)
  obtain ⟨_, _, _, _, _, _, _, hL⟩ := affine_closed_site_functor_properties A I
  have hc (x : X) : ∃ b, x ∈ Set.range (L b).hom := by
    obtain ⟨z, rfl⟩ := i.surjective x
    obtain ⟨b, w, hw⟩ := hcover z
    refine ⟨b, closedSiteLiftInclusion A I (W b) w, ?_⟩
    have h := (hL (W b)).2.1.w
    have hg' : (g b).left = (W b).hom :=
      (Category.comp_id (g b).left).symm.trans (MorphismProperty.Over.w (g b))
    have hw' : (W b).hom w = z := by rw [← hg']; exact hw
    change (closedSiteLiftInclusion A I (W b) ≫ (L b).hom) w = i z
    exact (congrArg (fun q : (W b).left ⟶ X ↦ q w) h).trans
      (congrArg (fun z : Z ↦ i z) hw')
  let D : PreZeroHypercover X := ⟨κ, fun b ↦ (L b).left, fun b ↦ (L b).hom⟩
  have : ∀ b, QuasiCompact (D.f b) := fun b ↦ inferInstance
  have hD : QuasiCompactCover D :=
    ⟨fun {W} hW ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun b ↦ (D.f b).isSpectralMap) (fun x _ ↦ hc x) W.2 hW.isCompact⟩
  have hmem : D.presieve₀ ∈ proetalePrecoverage X := by
    refine ⟨presieve₀_mem_qcPrecoverage_iff.mpr hD, ?_⟩
    exact (ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mpr
      ⟨hc, fun b ↦ proAffineEtale_le_weaklyEtale _ (L b).prop⟩
  let B : Cover.{u} proetalePrecoverage X := ⟨D, hmem⟩
  refine ⟨B, fun b ↦ ?_⟩
  let e := (hL (W b)).2.1.isoPullback
  refine ⟨a b, e.inv ≫ r b, ?_⟩
  rw [Category.assoc, hr]
  exact (hL (W b)).2.1.isoPullback_inv_snd
set_option backward.isDefEq.respectTransparency false in
private theorem affine_cover_lift {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (C : Cover.{u} proetalePrecoverage Z) :
    ∃ B : Cover.{u} proetalePrecoverage X, ∀ b,
      ∃ (a : C.I₀) (r : pullback (B.f b) i ⟶ C.X a),
        r ≫ C.f a = pullback.snd _ _ := by
  classical
  let e := X.isoSpec
  have : IsClosedImmersion (i ≫ e.hom) := inferInstance
  obtain ⟨I, eZ, he⟩ := IsClosedImmersion.Spec_iff.mp this
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : Surjective (eZ.hom ≫ q) := by rw [← he]; infer_instance
  have : Surjective q := Surjective.of_comp eZ.hom q
  let C0 := C.pullback₁ eZ.inv
  obtain ⟨B0, hB0⟩ := quotient_cover_lift Γ(X, ⊤) I inferInstance C0
  let B := B0.pushforward e.inv (Precoverage.mem_coverings_of_isIso _)
  refine ⟨B, fun b ↦ ?_⟩
  obtain ⟨a, r, hr⟩ := hB0 b
  let t : pullback (B.f b) i ⟶ pullback (B0.f b) q :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ eZ.hom) (by
      rw [Category.assoc, ← he]
      change pullback.fst (B.f b) i ≫ B0.f b =
        pullback.snd (B.f b) i ≫ i ≫ e.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
      change _ = pullback.fst (B.f b) i ≫ (B0.f b ≫ e.inv) ≫ e.hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  refine ⟨a, t ≫ r ≫ pullback.snd eZ.inv (C.f a), ?_⟩
  calc
    (t ≫ r ≫ pullback.snd eZ.inv (C.f a)) ≫ C.f a =
        t ≫ (r ≫ C0.f a) ≫ eZ.inv := by
      simp only [Category.assoc, ← pullback.condition]
      rfl
    _ = t ≫ pullback.snd (B0.f b) q ≫ eZ.inv := by rw [hr]
    _ = pullback.snd (B.f b) i := by simp [t]
set_option backward.isDefEq.respectTransparency false in
/-- A pro-etale cover of a surjective closed subscheme has a covering refinement
obtained by base change from the ambient scheme.

Source: Stacks Project Tag 09AB, affine ind-etale basis argument, and Tag 09BK.
Proof: for an affine quotient A/I, refine the given cover by a finite jointly
surjective family from the affine ind-etale basis. Apply the closed-site lift to
each member. Its closed fibre is the original member, so surjectivity of the
closed immersion makes the lifted family jointly surjective. Finitely many affine
members give a quasi-compact pro-etale cover. The cartesian closed-fibre squares
supply its refinement maps. Identify any affine closed immersion with an affine
quotient using its ideal and the canonical affine isomorphisms. Finally apply
this construction on an affine open cover of the target and bind the resulting
covers. All constructions allow an empty family when the target is empty.
(auxiliary; not a blueprint node)
-/
theorem exists_cover_refinement_surjective_closed {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [Surjective i]
    (C : Cover.{u} proetalePrecoverage Z) :
    ∃ B : Cover.{u} proetalePrecoverage X, ∀ b,
      ∃ (a : C.I₀) (W : Scheme.{u}) (q : W ⟶ B.X b) (p : W ⟶ Z)
        (r : W ⟶ C.X a), IsPullback q p (B.f b) i ∧ r ≫ C.f a = p := by
  classical
  let A := X.affineCover
  let p (a : A.I₀) := pullback.snd i (A.f a)
  let v (a : A.I₀) := pullback.fst i (A.f a)
  have hB (a : A.I₀) := affine_cover_lift (p a) (C.pullback₁ (v a))
  choose B hB using hB
  let A' := A.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage
  let E := A'.bind B
  refine ⟨E, fun b ↦ ?_⟩
  obtain ⟨a, r, hr⟩ := hB b.1 b.2
  let s : pullback (E.f b) i ⟶ pullback i (A.f b.1) :=
    pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ (B b.1).f b.2) (by
      rw [Category.assoc]
      exact (pullback.condition (f := E.f b) (g := i)).symm)
  let t : pullback (E.f b) i ⟶ pullback ((B b.1).f b.2) (p b.1) :=
    pullback.lift (pullback.fst _ _) s (by simp [s, p])
  refine ⟨a, pullback (E.f b) i, pullback.fst _ _, pullback.snd _ _,
    t ≫ r ≫ pullback.snd (v b.1) (C.f a), IsPullback.of_hasPullback _ _, ?_⟩
  calc
    (t ≫ r ≫ pullback.snd (v b.1) (C.f a)) ≫ C.f a =
        t ≫ (r ≫ (C.pullback₁ (v b.1)).f a) ≫ v b.1 := by
      simp only [Category.assoc, ← pullback.condition]
      rfl
    _ = t ≫ pullback.snd ((B b.1).f b.2) (p b.1) ≫ v b.1 := by rw [hr]
    _ = pullback.snd (E.f b) i := by simp [t, s, v]
end AlgebraicGeometry.Scheme
