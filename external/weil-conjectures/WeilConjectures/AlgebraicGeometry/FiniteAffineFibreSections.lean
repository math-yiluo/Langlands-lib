/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections

/-!
# Sections of the fibres of a morphism of affine schemes

For a ring map `A → B` and a point `p` of `Spec A`, the global sections of the fibre of
`Spec B ⟶ Spec A` over `p` are both `(f_* 𝒪_{Spec B})_p ⊗_{𝒪_{Spec A, p}} κ(p)` and
`B ⊗_A κ(p)` (blueprint: lem-pc-finite-affine-fibre-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

/-- For an algebra `B` over `A` and `p ∈ Spec A`, write `f : Spec B ⟶ Spec A`. The stalk of
the direct image of the structure sheaf, after tensoring with the residue field at `p`, has the
same sections as the scheme-theoretic fibre `f⁻¹(p)`, and so has `B ⊗_A κ(p)`. Both
identifications agree on elements of `B` and of the residue field.
Source: Stacks Project, Morphisms, Tag 02KB, affine calculation in the proof of the lemma
(blueprint: lem-pc-finite-affine-fibre-sections)

Proof steps from the source: (1) identify the structure sheaf on `Spec B` with `˜B`,
push it forward along `Spec.map (algebraMap A B)`, and identify its stalk at `p` with
the localization of `B` at the prime of `p`; (2) use `κ(p) = A_p / m_p A_p` to
identify the stalk tensor with `B ⊗[A] κ(p)`; (3) apply the affine fibre-product
calculation to identify the fibre with `Spec (B ⊗[A] κ(p))` and its global sections
with that tensor product. The displayed equations record these identifications on the
generators from `B` and `κ(p)` (using `lem-weil-pbc-spec-tilde-free-module`,
`lem-weil-pbc-pushforward-tilde-spec`, `lem-weil-pbc-spec-tilde-stalk-localization`,
and `lem-weil-pbc-fibre-product-affine-spectra`). -/
theorem Spec.exists_ringEquiv_stalk_tensorProduct_fiber (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] (p : Spec (CommRingCat.of A)) :
    letI φ := CommRingCat.ofHom (algebraMap A B)
    letI f := Spec.map φ
    letI R := (Spec (CommRingCat.of A)).presheaf.stalk p
    letI P := (Spec.topMap φ _* (Spec.structureSheaf (CommRingCat.of B)).1).stalk p
    letI K := (Spec (CommRingCat.of A)).residueField p
    letI : Algebra R P :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat p).map
        (Spec.sheafedSpaceMap φ).hom.c).hom.toAlgebra
    letI : Algebra R K := ((Spec (CommRingCat.of A)).residue p).hom.toAlgebra
    letI : Algebra A K :=
      (StructureSheaf.toStalk (CommRingCat.of A) p ≫
        (Spec (CommRingCat.of A)).residue p).hom.toAlgebra
    ∃ (e : P ⊗[R] K ≃+* Γ(f.fiber p, ⊤)) (g : B ⊗[A] K ≃+* Γ(f.fiber p, ⊤)),
      (∀ b : B, e ((StructureSheaf.toPushforwardStalk φ p).hom b ⊗ₜ 1) = g (b ⊗ₜ 1)) ∧
      (∀ k : K, e (1 ⊗ₜ k) = g (1 ⊗ₜ k)) ∧
      (∀ b : B,
        g (b ⊗ₜ 1) =
          (f.fiberι p).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)) ∧
      (∀ k : K,
        g (1 ⊗ₜ k) =
          (f.fiberToSpecResidueField p).appTop.hom ((Scheme.ΓSpecIso K).inv.hom k)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let K := (Spec (CommRingCat.of A)).residueField p
  let : Algebra A K := (StructureSheaf.toStalk (CommRingCat.of A) p ≫
    (Spec (CommRingCat.of A)).residue p).hom.toAlgebra
  have hp : p ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) := trivial
  have hι : (f.fiberι p).appLE (f ⁻¹ᵁ ⊤) ⊤ (f.preimage_fiberι_preimage p ⊤ hp).ge =
      (f.fiberι p).appTop :=
    (f.fiberι p).appLE_eq_app
  have P := (f.isPushout_app_evaluation_fiber (isAffineOpen_top _) p hp).of_iso
    (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl K) (Iso.refl _)
    (f' := CommRingCat.ofHom (algebraMap A B)) (g' := CommRingCat.ofHom (algebraMap A K))
    (inl' := (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (f.fiberι p).appTop)
    (inr' := (Scheme.ΓSpecIso K).inv ≫ (f.fiberToSpecResidueField p).appTop)
    (Scheme.ΓSpecIso_naturality _) ?_ (hι.trans (Iso.hom_inv_id_assoc _ _).symm)
    (Category.id_comp _).symm
  · have T := CommRingCat.isPushout_tensorProduct A B K
    let e' := T.isoPushout ≪≫ P.isoPushout.symm
    have hl : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e'.hom =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (f.fiberι p).appTop := by
      simp only [e', Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inl_isoPushout_hom]
      rw [Iso.comp_inv_eq, IsPushout.inl_isoPushout_hom]
    have hr : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e'.hom =
        (Scheme.ΓSpecIso K).inv ≫ (f.fiberToSpecResidueField p).appTop := by
      simp only [e', Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inr_isoPushout_hom]
      rw [Iso.comp_inv_eq, IsPushout.inr_isoPushout_hom]
    obtain ⟨e, he⟩ :=
      f.exists_ringEquiv_stalk_pushforward_tensorProduct_fiber (isAffineOpen_top _) p hp
    refine ⟨e, e'.commRingCatIsoToRingEquiv, fun b ↦ ?_, fun k ↦ ?_,
      fun b ↦ congr($(hl).hom b), fun k ↦ congr($(hr).hom k)⟩
    · refine (he ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) 1).trans ?_
      rw [map_one, mul_one]
      exact congr($(hι).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b)).trans
        congr($(hl).hom b).symm
    · have := he 1 k
      rw [map_one, map_one, one_mul] at this
      exact this.trans congr($(hr).hom k).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Iso.inv_comp_eq]
    rfl

end AlgebraicGeometry
