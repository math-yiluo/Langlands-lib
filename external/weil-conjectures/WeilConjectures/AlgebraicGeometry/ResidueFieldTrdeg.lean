/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import WeilConjectures.RingTheory.TrdegAlgebraicAdjoin

/-!
# Transcendence degrees of residue field extensions

For a morphism of schemes `f : X ⟶ Y` and a point `x : X`, `f.trdegAt x` is the transcendence
degree of the residue field extension `κ(x) / κ(f x)`.

* `AlgebraicGeometry.Scheme.Hom.trdegAt_comp`: it is additive along compositions.
* `AlgebraicGeometry.Scheme.Hom.trdegAt_eq_zero_of_isPreimmersion`: it vanishes for
  preimmersions (e.g. open immersions).
* `AlgebraicGeometry.Scheme.Pullback.trdegAt_snd_le`: for a point `t` of `X ×_S Y`,
  `trdeg_{κ(y)} κ(t) ≤ trdeg_{κ(s)} κ(x)`, where `x`, `y`, `s` are the images of `t`. Indeed
  `κ(t)` is the fraction field of the image of `κ(x) ⊗_{κ(s)} κ(y)`, which is generated over
  `κ(y)` by the image of `κ(x)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Algebra

/-- An algebra whose structure map is surjective has transcendence degree zero. -/
theorem trdeg_eq_zero_of_surjective {K A : Type*} [CommRing K] [Nontrivial K] [CommRing A]
    [Algebra K A]
    (h : Function.Surjective (algebraMap K A)) : trdeg K A = 0 := by
  have : Algebra.IsAlgebraic K A := ⟨fun z ↦ by
    obtain ⟨a, rfl⟩ := h z
    exact isAlgebraic_algebraMap a⟩
  exact trdeg_eq_zero

/-- The transcendence degree is invariant under a bijective change of the base field. -/
theorem trdeg_eq_of_bijective_algebraMap {K K' A : Type u} [Field K] [Field K'] [CommRing A]
    [IsDomain A] [Algebra K K'] [Algebra K A] [Algebra K' A] [IsScalarTower K K' A]
    (h : Function.Bijective (algebraMap K K')) : trdeg K A = trdeg K' A := by
  rw [← trdeg_add_eq K K' (A := A), trdeg_eq_zero_of_surjective h.2, zero_add]

end Algebra

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- The transcendence degree `trdeg_{κ(f x)} κ(x)` of the residue field extension of a morphism of
schemes `f` at a point `x`. -/
noncomputable def Hom.trdegAt (f : X ⟶ Y) (x : X) : Cardinal.{u} :=
  let := (f.residueFieldMap x).hom.toAlgebra
  Algebra.trdeg (Y.residueField (f x)) (X.residueField x)

lemma Hom.trdegAt_congr {f g : X ⟶ Y} (h : f = g) (x : X) : f.trdegAt x = g.trdegAt x := by
  subst h
  rfl

/-- The transcendence degree of residue field extensions is additive along compositions. -/
lemma Hom.trdegAt_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).trdegAt x = g.trdegAt (f x) + f.trdegAt x := by
  let := (g.residueFieldMap (f x)).hom.toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  have : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
      residueFieldMap_comp, CommRingCat.hom_comp])
  unfold Hom.trdegAt
  exact (trdeg_add_eq (Z.residueField (g (f x))) (Y.residueField (f x))
    (A := X.residueField x)).symm

lemma Hom.trdegAt_le_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    g.trdegAt (f x) ≤ (f ≫ g).trdegAt x := by
  rw [trdegAt_comp]
  exact self_le_add_right _ _

lemma Hom.trdegAt_eq_zero_of_surjective (f : X ⟶ Y) (x : X)
    (h : Function.Surjective (f.residueFieldMap x)) : f.trdegAt x = 0 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  exact Algebra.trdeg_eq_zero_of_surjective h

/-- The residue field maps of a preimmersion are surjective. -/
lemma Hom.surjective_residueFieldMap (f : X ⟶ Y) [IsPreimmersion f] (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨w, rfl⟩ := X.residue_surjective x z
  obtain ⟨v, rfl⟩ := f.stalkMap_surjective x w
  refine ⟨Y.residue _ v, ?_⟩
  rw [← CommRingCat.comp_apply, residue_residueFieldMap, CommRingCat.comp_apply]

lemma Hom.trdegAt_eq_zero_of_isPreimmersion (f : X ⟶ Y) [IsPreimmersion f] (x : X) :
    f.trdegAt x = 0 :=
  f.trdegAt_eq_zero_of_surjective x (f.surjective_residueFieldMap x)

lemma Hom.trdegAt_comp_of_isPreimmersion (f : X ⟶ Y) [IsPreimmersion f] (g : Y ⟶ Z) (x : X) :
    (f ≫ g).trdegAt x = g.trdegAt (f x) := by
  rw [trdegAt_comp, trdegAt_eq_zero_of_isPreimmersion f, add_zero]

/-- On an affine open `V ∋ y`, the residue field `κ(y)` is the field of fractions of the image of
`Γ(X, V)`. -/
lemma _root_.AlgebraicGeometry.IsAffineOpen.exists_mul_evaluation_eq {V : X.Opens}
    (hV : IsAffineOpen V) (y : X) (hy : y ∈ V) (z : X.residueField y) :
    ∃ a b : Γ(X, V), X.evaluation V y hy b ≠ 0 ∧
      z * X.evaluation V y hy b = X.evaluation V y hy a := by
  let := X.presheaf.algebra_section_stalk ⟨y, hy⟩
  have := hV.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨w, rfl⟩ := X.residue_surjective y z
  obtain ⟨⟨a, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl w
  refine ⟨a, s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk y) s) := IsLocalization.map_units _ s
    exact (hu.map (X.residue y).hom).ne_zero
  · rw [← germ_residue, CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec _ a s

namespace Pullback

variable {S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue field `κ(t)` of a point `t` of `X ×_S Y` over `(x, y, s)` is the field of
fractions of the image of `κ(x) ⊗_{κ(s)} κ(y)`. -/
lemma exists_mul_ofPointTensor_eq (t : ↑(pullback f g)) (z : (pullback f g).residueField t) :
    ∃ a b : (Triplet.ofPoint t).tensor, ofPointTensor t b ≠ 0 ∧
      z * ofPointTensor t b = ofPointTensor t a := by
  suffices H : ∀ (T : Triplet f g) (p : Spec T.tensor)
      (z : (pullback f g).residueField (T.SpecTensorTo p)),
      ∃ a b : (Triplet.ofPoint (T.SpecTensorTo p)).tensor,
        ofPointTensor (T.SpecTensorTo p) b ≠ 0 ∧
        z * ofPointTensor (T.SpecTensorTo p) b = ofPointTensor (T.SpecTensorTo p) a by
    have := H (Triplet.ofPoint t) (SpecOfPoint t)
    rw [SpecTensorTo_SpecOfPoint] at this
    exact this z
  intro T p z
  have key := T.Spec_ofPointTensor_SpecTensorTo p
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj, Scheme.Spec.algebraMap_residueFieldIso_inv]
    at key
  set ρ := T.SpecTensorTo.residueFieldMap p
  set c := (Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom
  have hp : p ∈ (⊤ : (Spec T.tensor).Opens) := trivial
  have hc (r : Γ(Spec T.tensor, ⊤)) : ρ (ofPointTensor (T.SpecTensorTo p)
      (c ((Scheme.ΓSpecIso T.tensor).hom r))) = (Spec T.tensor).evaluation ⊤ p hp r := by
    have := congr(($key).hom ((Scheme.ΓSpecIso T.tensor).hom r))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this, ← CommRingCat.comp_apply (Scheme.ΓSpecIso T.tensor).hom, Iso.hom_inv_id,
      CommRingCat.id_apply]
    rfl
  obtain ⟨a, b, hb, hab⟩ :=
    (isAffineOpen_top (Spec T.tensor)).exists_mul_evaluation_eq p hp (ρ z)
  refine ⟨c ((Scheme.ΓSpecIso T.tensor).hom a), c ((Scheme.ΓSpecIso T.tensor).hom b), ?_, ?_⟩
  · intro h
    apply hb
    rw [← hc, h, map_zero]
  · apply ρ.hom.injective
    rw [map_mul, hc, hc, hab]

/-- **Transcendence degree in fibre products**: for a point `t` of `X ×_S Y` with images `x`, `y`
and `s`, `trdeg_{κ(y)} κ(t) ≤ trdeg_{κ(s)} κ(x)`. -/
theorem trdegAt_snd_le (t : ↑(pullback f g)) :
    (pullback.snd f g).trdegAt t ≤ f.trdegAt (pullback.fst f g t) := by
  have hy : g (pullback.snd f g t) = f (pullback.fst f g t) := (Triplet.ofPoint t).hy
  have hsq₀ := residueFieldCongr_inv_residueFieldMap_ofPoint t
  have hsq : f.residueFieldMap (pullback.fst f g t) ≫ (pullback.fst f g).residueFieldMap t =
      ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap _) ≫
        (pullback.snd f g).residueFieldMap t := by
    exact hsq₀
  let : Algebra (S.residueField (f (pullback.fst f g t)))
      (X.residueField (pullback.fst f g t)) := (f.residueFieldMap _).hom.toAlgebra
  let : Algebra (Y.residueField (pullback.snd f g t)) ((pullback f g).residueField t) :=
    ((pullback.snd f g).residueFieldMap t).hom.toAlgebra
  let : Algebra (S.residueField (f (pullback.fst f g t)))
      (Y.residueField (pullback.snd f g t)) :=
    ((S.residueFieldCongr hy).inv ≫ g.residueFieldMap _).hom.toAlgebra
  let : Algebra (S.residueField (f (pullback.fst f g t))) ((pullback f g).residueField t) :=
    (((S.residueFieldCongr hy).inv ≫ g.residueFieldMap _) ≫
      (pullback.snd f g).residueFieldMap t).hom.toAlgebra
  have : IsScalarTower (S.residueField (f (pullback.fst f g t)))
      (Y.residueField (pullback.snd f g t)) ((pullback f g).residueField t) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let f₁ : X.residueField (pullback.fst f g t) →ₐ[S.residueField (f (pullback.fst f g t))]
      (pullback f g).residueField t :=
    { ((pullback.fst f g).residueFieldMap t).hom with
      commutes' r := by
        have := congr(($hsq).hom r)
        simpa [RingHom.algebraMap_toAlgebra] using this }
  set A := Algebra.adjoin (Y.residueField (pullback.snd f g t)) (Set.range f₁)
  have hpush (r : (Triplet.ofPoint t).tensor) : ofPointTensor t r ∈ A := by
    let i₁ : X.residueField (pullback.fst f g t) ⟶ CommRingCat.of A :=
      CommRingCat.ofHom (((pullback.fst f g).residueFieldMap t).hom.codRestrict A
        fun a ↦ Algebra.subset_adjoin ⟨a, rfl⟩)
    let i₂ : Y.residueField (pullback.snd f g t) ⟶ CommRingCat.of A :=
      CommRingCat.ofHom (algebraMap (Y.residueField (pullback.snd f g t)) A)
    have hd : ((S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫
        f.residueFieldMap (Triplet.ofPoint t).x) ≫ i₁ =
        ((S.residueFieldCongr (Triplet.ofPoint t).hy).inv ≫
          g.residueFieldMap (Triplet.ofPoint t).y) ≫ i₂ := by
      ext a
      simpa [i₁, i₂, RingHom.algebraMap_toAlgebra] using congr(($hsq₀).hom a)
    have hψ : pushout.desc i₁ i₂ hd ≫ CommRingCat.ofHom A.val.toRingHom = ofPointTensor t := by
      refine pushout.hom_ext ?_ ?_
      · rw [pushout.inl_desc_assoc, ofPointTensor, pushout.inl_desc]
        rfl
      · rw [pushout.inr_desc_assoc, ofPointTensor, pushout.inr_desc]
        rfl
    rw [← hψ]
    exact (pushout.desc i₁ i₂ hd r).2
  unfold Hom.trdegAt
  refine Algebra.trdeg_le_of_isAlgebraic_adjoin_range f₁ f₁.toRingHom.injective ⟨fun z ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := exists_mul_ofPointTensor_eq t z
  have hz : z = ofPointTensor t a * (ofPointTensor t b)⁻¹ := by
    rw [← hab, mul_inv_cancel_right₀ hb]
  rw [hz]
  exact (isAlgebraic_algebraMap (⟨_, hpush a⟩ : A)).mul
    (isAlgebraic_algebraMap (⟨_, hpush b⟩ : A)).inv

end Pullback

end AlgebraicGeometry.Scheme
