/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift

import WeilConjectures.AlgebraicGeometry.ProEtale.Replete

/-!
# Affine coordinates for pro-étale specialization

Weak contractibility and the closed-fibre specialization condition at an affine pro-étale
object transfer to its affine coordinate ring.

## References

* Stacks Project, Tag 09AC (first reduction)
* Stacks Project, Tag 01IH (closed immersions into affine schemes)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
-- A section of a surjective affine cover is obtained by lifting the Yoneda identity.
private theorem split_affine_proetale_cover {X : Scheme.{u}} (V W : X.ProEt)
    [IsAffine V.left] [IsAffine W.left]
    (hV : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (q : W ⟶ V) [Surjective q.left] : ∃ s : V ⟶ W, s ≫ q = 𝟙 V := by
  let J := ProEt.topology X
  let H := J.uliftYoneda.{u + 1}
  have hcover : Sieve.generate (Presieve.singleton q) ∈ J V := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_singleton]
    change Presieve.singleton q.left ∈ proetalePrecoverage V.left
    exact Hom.singleton_mem_propQCPrecoverage (inferInstance : WeaklyEtale q.left)
  have hepi : Epi (H.map q) := by
    constructor
    intro T a b hab
    apply J.uliftYonedaEquiv.injective
    have hsep := ((isSheaf_iff_isSheaf_of_type J T.obj).mp T.property).isSheafFor
      (Presieve.singleton q) hcover |>.isSeparatedFor
    apply hsep.ext
    rintro Y f ⟨⟩
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv hab
  obtain ⟨s, hs⟩ := hV _ _ (H.map q) hepi (ULift.up (𝟙 V))
  exact ⟨s.down, congrArg ULift.down hs⟩

set_option backward.isDefEq.respectTransparency false in
-- Use the kernel quotient map explicitly; no arbitrary quotient presentation is chosen.
private theorem quotient_specialization {T Y : Scheme.{u}} [IsAffine Y]
    (f : T ⟶ Y) [IsClosedImmersion f]
    (hspec : ∀ x : Y, ∃ z : T, Specializes x (f z)) :
    ∀ x : Spec Γ(Y, ⊤), ∃ z : ↥(pullback (𝟙 (Spec Γ(Y, ⊤)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))))),
      Specializes x ((pullback.fst (𝟙 (Spec Γ(Y, ⊤)))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))))) z) := by
  have hsurj : Function.Surjective f.appTop :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine f).2
  let e := f.appTop.hom.quotientKerEquivOfSurjective hsurj
  let g : T ⟶ Spec (.of (Γ(Y, ⊤) ⧸ RingHom.ker f.appTop.hom)) :=
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
  have he : CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom)) ≫
    CommRingCat.ofHom e.toRingHom = f.appTop := by
    ext a
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj a
  have hg : g ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))) = f ≫ Y.isoSpec.hom := by
    change (T.toSpecΓ ≫ Spec.map _) ≫ Spec.map _ = f ≫ Y.toSpecΓ
    rw [Category.assoc, ← Spec.map_comp, he]
    exact (Scheme.toSpecΓ_naturality f).symm
  intro x
  obtain ⟨z, hz⟩ := hspec (Y.isoSpec.inv x)
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f.appTop.hom)))
  let l : Spec (.of (Γ(Y, ⊤) ⧸ RingHom.ker f.appTop.hom)) ⟶
    pullback (𝟙 (Spec Γ(Y, ⊤))) j := pullback.lift j (𝟙 _) (by simp)
  refine ⟨l (g z), ?_⟩
  have hz' := hz.map Y.isoSpec.hom.continuous
  have hx : Y.isoSpec.hom (Y.isoSpec.inv x) = x :=
    congrArg (fun k : Spec Γ(Y, ⊤) ⟶ Spec Γ(Y, ⊤) ↦ k x)
    Y.isoSpec.inv_hom_id
  have hgz : Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (RingHom.ker f.appTop.hom))) (g z) =
    Y.isoSpec.hom (f z) := congrArg (fun k : T ⟶ _ ↦ k z) hg
  rw [hx] at hz'
  have hlhom : l ≫ pullback.fst (𝟙 _) j = j := pullback.lift_fst _ _ _
  have hl : (pullback.fst (𝟙 _) j) (l (g z)) = j (g z) :=
    congrArg (fun k : Spec (.of (Γ(Y, ⊤) ⧸ RingHom.ker f.appTop.hom)) ⟶
      Spec Γ(Y, ⊤) ↦ k (g z)) hlhom
  change Specializes (x : Spec Γ(Y, ⊤)) ((pullback.fst (𝟙 _) j) (l (g z)))
  rw [hl, hgz]
  exact hz'

set_option backward.isDefEq.respectTransparency false in
/-- Affine coordinates transport projectivity of evaluation and the closed-fibre
specialization condition, where the ideal `I` is the kernel of the global-sections map of the
closed base change. -/
theorem specialization_affine_coordinates
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
    (hweak : ∀ (P Q : Sheaf (ProEt.topology X) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    (hspec : ∀ x : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes x ((pullback.fst V.hom i) z)) :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) ∧
    (∀ x : B.left, ∃ z : ↥(pullback B.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))),
      Specializes x ((pullback.fst B.hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) z)) := by
  dsimp only
  constructor
  · let B := AffineProEt.ofEtale (𝟙 (Spec Γ(V.left, ⊤)))
    intro P Q φ hφ y
    have hlocal : Sheaf.IsLocallySurjective φ :=
      (Sheaf.isLocallySurjective_iff_epi φ).mpr hφ
    obtain ⟨W, q, hq, z, hz⟩ :=
      (AffineProEt.isLocallySurjective_iff_of_isSheaf φ.hom P.property Q.property).mp hlocal B y
    let w : W.left ⟶ V.left := W.hom ≫ V.left.isoSpec.inv
    have hW : WeaklyEtale W.hom := proAffineEtale_le_weaklyEtale _ W.prop
    have hw : WeaklyEtale w := by dsimp [w]; infer_instance
    let W' : X.ProEt := ProEt.mk (w ≫ V.hom)
    let q' : W' ⟶ V := MorphismProperty.Over.homMk w rfl
    have hqleft : q.left = W.hom := by
      have h := MorphismProperty.Over.w q
      change q.left ≫ 𝟙 _ = W.hom at h
      simpa only [Category.comp_id] using h
    have hW' : IsAffine W'.left := inferInstanceAs (IsAffine W.left)
    have hq' : Surjective q'.left := by
      change Surjective (W.hom ≫ V.left.isoSpec.inv)
      rw [← hqleft]
      infer_instance
    obtain ⟨s, hs⟩ := split_affine_proetale_cover V W' hweak q'
    have hsleft : s.left ≫ w = 𝟙 V.left :=
      congrArg (fun k : V ⟶ V ↦ k.left) hs
    let t : B ⟶ W := MorphismProperty.Over.homMk (V.left.isoSpec.inv ≫ s.left) (by
      apply (cancel_mono V.left.isoSpec.inv).mp
      change (V.left.isoSpec.inv ≫ s.left) ≫ W.hom ≫ V.left.isoSpec.inv =
        (𝟙 _) ≫ V.left.isoSpec.inv
      change V.left.isoSpec.inv ≫ (s.left ≫ w) = (𝟙 _) ≫ V.left.isoSpec.inv
      rw [hsleft, Category.comp_id, Category.id_comp])
    have ht : t ≫ q = 𝟙 B := by
      apply MorphismProperty.Over.Hom.ext
      change (V.left.isoSpec.inv ≫ s.left) ≫ q.left = 𝟙 _
      rw [hqleft]
      exact MorphismProperty.Over.w t
    refine ⟨P.obj.map t.op z, ?_⟩
    rw [NatTrans.naturality_apply, hz, ← Functor.map_comp_apply, ← op_comp, ht]
    exact Q.obj.map_id_apply _ y
  · exact quotient_specialization (Y := V.left) (pullback.fst V.hom i) hspec

end AlgebraicGeometry.Scheme
