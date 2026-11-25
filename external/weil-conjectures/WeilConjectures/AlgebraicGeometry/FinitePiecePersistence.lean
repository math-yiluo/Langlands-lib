/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField

/-!
# Persistence of a finite open piece under residue-field-preserving base change

Source: Stacks Project, More on Morphisms, Tag 02LK, final assertion
(blueprint: lem-weil-pbc-elementary-etale-finite-piece-persistence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem pullback_fst_residue_iso {A B C : Scheme.{u}}
    (a : A ⟶ C) (b : B ⟶ C) (z : ↑(pullback a b))
    (hb : IsIso (b.residueFieldMap (pullback.snd a b z))) :
    IsIso ((pullback.fst a b).residueFieldMap z) := by
  let T := Scheme.Pullback.Triplet.ofPoint z
  have : IsIso ((C.residueFieldCongr T.hy).inv ≫ b.residueFieldMap T.y) := by
    dsimp [T, Scheme.Pullback.Triplet.ofPoint]
    infer_instance
  have hinl : IsIso T.tensorInl := (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  let e := (asIso T.tensorInl).commRingCatIsoToRingEquiv
  have hf : IsField T.tensor := e.symm.toMulEquiv.isField (Field.toIsField _)
  let : Field T.tensor := hf.toField
  let p := RingHom.ker (Scheme.Pullback.ofPointTensor z).hom
  have hp : p = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp
    (RingHom.injective (Scheme.Pullback.ofPointTensor z).hom)
  have hfq : IsField (T.tensor ⧸ p) := by
    rw [hp]
    exact (RingEquiv.quotientBot T.tensor).toMulEquiv.isField (Field.toIsField _)
  obtain ⟨e', _, hl, _⟩ :=
    (Scheme.Pullback.exists_residueField_equiv_ofPointTensor a b z).2 hfq
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨RingHom.injective _, ?_⟩
  change Function.Surjective ((pullback.fst a b).residueFieldMap z).hom
  rw [← hl]
  exact e'.surjective.comp
    (Ideal.Quotient.mk_surjective.comp
      ((ConcreteCategory.isIso_iff_bijective T.tensorInl).mp hinl).2)

private theorem pullback_point_unique {A B C : Scheme.{u}}
    (a : A ⟶ C) (b : B ⟶ C) (z w : ↑(pullback a b))
    (hx : pullback.fst a b z = pullback.fst a b w)
    (hy : pullback.snd a b z = pullback.snd a b w)
    (hb : IsIso (b.residueFieldMap (pullback.snd a b w))) : z = w := by
  let T := Scheme.Pullback.Triplet.ofPoint w
  have : IsIso ((C.residueFieldCongr T.hy).inv ≫ b.residueFieldMap T.y) := by
    dsimp [T, Scheme.Pullback.Triplet.ofPoint]
    infer_instance
  have : IsIso T.tensorInl := (IsPushout.of_hasPushout _ _).isIso_inl_of_isIso
  apply Scheme.Pullback.carrierEquiv.injective
  apply Scheme.Pullback.carrierEquiv_eq_iff.mpr
  refine ⟨Scheme.Pullback.Triplet.ext hx hy, ?_⟩
  apply (asIso (Spec.map T.tensorInl)).hom.homeomorph.injective
  exact Subsingleton.elim _ _

/-- A finite open piece with a unique point above `u` and unchanged residue field at `x`
persists under any base change preserving the residue field at `u`.
Source: Stacks Project, Tag 02LK, final assertion; the generalization to arbitrary `ψ`
uses no étaleness (blueprint: lem-weil-pbc-elementary-etale-finite-piece-persistence).

Proof:
1. The square with projections `π` and `pullback.snd f (ψ ≫ φ)` is cartesian by
`lem-weil-pbc-cartesian-square-pasting`, using the two specified fibre products
(`def-pc-fibre-product`).
2. By `lem-weil-pbc-open-fibre-product`, the inverse-image open is the base change
of `V` over `U`. Finiteness follows from `lem-weil-pbc-finite-morphism-permanence`.
3. Every point of this open above `u'` maps to `v`, by uniqueness above `u`.
By `lem-weil-pbc-fibre-product-points`, these points correspond to the spectrum of
κ(v) ⊗[κ(u)] κ(u'). The residue-field isomorphism for `ψ` identifies this tensor
product with κ(v), a field, so there is exactly one such point.
4. By `lem-weil-pbc-fibre-product-point-residue-field`, its residue field is the same
field κ(v), compatibly with `π`. Compose its residue-field isomorphism with the
one for `V.ι ≫ pullback.fst f φ` to obtain the asserted isomorphism at `x`.
Residue-field maps here are those of `def-weil-residue-field`. -/
theorem finitePiece_persistence_of_isIso_residueFieldMap
    {X S U U' : Scheme.{u}} (f : X ⟶ S) (φ : U ⟶ S)
    (u₀ : U) (x : X) (hx : f x = φ u₀)
    (V : (pullback f φ).Opens) (v : V.toScheme)
    (hfinite : IsFinite (V.ι ≫ pullback.snd f φ))
    (hv : (V.ι ≫ pullback.snd f φ) v = u₀)
    (hunique : ∀ w : V.toScheme, (V.ι ≫ pullback.snd f φ) w = u₀ → w = v)
    (hvx : (V.ι ≫ pullback.fst f φ) v = x)
    (hresidue : IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v))
    (ψ : U' ⟶ U) (u₁ : U') (hu : ψ u₁ = u₀)
    (hbase : IsIso (ψ.residueFieldMap u₁))
    (π : pullback f (ψ ≫ φ) ⟶ pullback f φ)
    (hπp : π ≫ pullback.fst f φ = pullback.fst f (ψ ≫ φ))
    (hπq : π ≫ pullback.snd f φ = pullback.snd f (ψ ≫ φ) ≫ ψ) :
    let V' := π ⁻¹ᵁ V
    IsFinite (V'.ι ≫ pullback.snd f (ψ ≫ φ)) ∧
      ∃ v' : V'.toScheme,
        (V'.ι ≫ pullback.snd f (ψ ≫ φ)) v' = u₁ ∧
        (∀ w : V'.toScheme, (V'.ι ≫ pullback.snd f (ψ ≫ φ)) w = u₁ → w = v') ∧
        (V'.ι ≫ pullback.fst f (ψ ≫ φ)) v' = x ∧
        IsIso ((V'.ι ≫ pullback.fst f (ψ ≫ φ)).residueFieldMap v') ∧
        π (V'.ι v') = V.ι v := by
  classical
  have _hcompat := hx
  let V' := π ⁻¹ᵁ V
  let r : V'.toScheme ⟶ V.toScheme := π ∣_ V
  let q := V.ι ≫ pullback.snd f φ
  let q' := V'.ι ≫ pullback.snd f (ψ ≫ φ)
  have hsq : IsPullback π (pullback.snd f (ψ ≫ φ)) (pullback.snd f φ) ψ := by
    apply (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback f φ) hπq).mp
    simpa only [hπp] using IsPullback.of_hasPullback f (ψ ≫ φ)
  have hr : IsPullback r q' q ψ :=
    (isPullback_morphismRestrict π V).paste_vert hsq
  refine ⟨MorphismProperty.of_isPullback hr hfinite, ?_⟩
  obtain ⟨z, hzv, hzu⟩ := Scheme.exists_preimage_of_isPullback hr v u₁
    (hv.trans hu.symm)
  have hru : IsIso (ψ.residueFieldMap (q' z)) := by
    rw [hzu]
    exact hbase
  have hzres : IsIso (r.residueFieldMap z) := by
    have : IsIso ((pullback.fst q ψ).residueFieldMap (hr.isoPullback.hom z)) := by
      apply pullback_fst_residue_iso
      have hpoint : pullback.snd q ψ (hr.isoPullback.hom z) = q' z :=
        congrArg (fun k ↦ k z) hr.isoPullback_hom_snd
      rw [hpoint]
      exact hru
    rw [← hr.isoPullback_hom_fst, Scheme.residueFieldMap_comp]
    infer_instance
  refine ⟨z, hzu, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hwv : r w = v := hunique (r w) (by
      rw [← Scheme.Hom.comp_apply, hr.w, Scheme.Hom.comp_apply, hw, hu])
    apply hr.isoPullback.hom.homeomorph.injective
    apply pullback_point_unique q ψ
    · change pullback.fst q ψ (hr.isoPullback.hom w) =
        pullback.fst q ψ (hr.isoPullback.hom z)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hr.isoPullback_hom_fst]
      exact hwv.trans hzv.symm
    · change pullback.snd q ψ (hr.isoPullback.hom w) =
        pullback.snd q ψ (hr.isoPullback.hom z)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hr.isoPullback_hom_snd]
      exact hw.trans hzu.symm
    · change IsIso (ψ.residueFieldMap (pullback.snd q ψ (hr.isoPullback.hom z)))
      have hpoint : pullback.snd q ψ (hr.isoPullback.hom z) = q' z :=
        congrArg (fun k ↦ k z) hr.isoPullback_hom_snd
      rw [hpoint]
      exact hru
  · have hmap : V'.ι ≫ pullback.fst f (ψ ≫ φ) = r ≫ V.ι ≫ pullback.fst f φ := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hπp]
    rw [hmap, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hzv]
    exact hvx
  · have hmap : V'.ι ≫ pullback.fst f (ψ ≫ φ) = r ≫ (V.ι ≫ pullback.fst f φ) := by
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hπp]
    rw [hmap, Scheme.residueFieldMap_comp]
    have : IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap (r z)) := by
      rw [hzv]
      exact hresidue
    infer_instance
  · rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hzv]

end AlgebraicGeometry
