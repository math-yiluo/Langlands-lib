import Langlands.AlgebraicGeometry.Picard.LocalEquationCartier
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Relative effective Cartier divisors are local on an open cover

If an ideal sheaf pulls back to relative effective Cartier ideals on the members of an open
cover (relative to flat maps of the bases), with local regular generators, then it is relative
effective Cartier. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativeEffectiveLocal

variable {X : Scheme.{u}}

/-- A principal ideal of a pulled-back ideal sheaf on an affine open of an open subscheme is the
transport of a principal ideal of the original ideal sheaf. -/
lemma ideal_image_eq_span (I : X.IdealSheafData) {Z : Scheme.{u}} (h : Z ⟶ X) [IsOpenImmersion h]
    (U' : Z.affineOpens) (a : Γ(Z, U'.1)) (ha : (I.comap h).ideal U' = Ideal.span {a}) :
    I.ideal ⟨h ''ᵁ U'.1, U'.2.image_of_isOpenImmersion h⟩ = Ideal.span {(h.appIso U'.1).inv a} := by
  have hc := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I h U'
  rw [ha] at hc
  rw [← Ideal.map_comap_of_surjective (h.appIso U'.1).inv.hom
    (ConcreteCategory.bijective_of_isIso (h.appIso U'.1).inv).2
    (I.ideal ⟨h ''ᵁ U'.1, U'.2.image_of_isOpenImmersion h⟩), ← hc, Ideal.map_span,
    Set.image_singleton]

/-- **Relative effective Cartier divisors are local on an open cover.** -/
theorem isRelativeEffectiveCartierIdeal_of_cover {S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) {ι : Type*} {Z S' : ι → Scheme.{u}} (h : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (h i)] (g : ∀ i, Z i ⟶ S' i) (j : ∀ i, S' i ⟶ S) [∀ i, Flat (j i)]
    (hcomm : ∀ i, h i ≫ f = g i ≫ j i) (hcov : ∀ x, ∃ i, x ∈ Set.range (h i))
    (hI : ∀ i, IsRelativeEffectiveCartierIdeal (g i) (I.comap (h i)))
    (hgen : ∀ i (z : Z i), ∃ U' : (Z i).affineOpens, z ∈ U'.1 ∧ ∃ a : Γ(Z i, U'.1),
      (I.comap (h i)).ideal U' = Ideal.span {a} ∧ IsSMulRegular Γ(Z i, U'.1) a) :
    IsRelativeEffectiveCartierIdeal f I := by
  constructor
  · apply LocalEquationCartier.isEffectiveCartierIdeal_of_local
    intro x
    obtain ⟨i, z, rfl⟩ := hcov x
    obtain ⟨U', hzU, a, ha, hreg⟩ := hgen i z
    refine ⟨⟨_, U'.2.image_of_isOpenImmersion (h i)⟩, ⟨z, hzU, rfl⟩,
      ((h i).appIso U'.1).inv a, ideal_image_eq_span I (h i) U' a ha, ?_⟩
    intro c d hcd
    have hinj := (ConcreteCategory.bijective_of_isIso ((h i).appIso U'.1).hom).1
    have hinv : ∀ y, ((h i).appIso U'.1).hom (((h i).appIso U'.1).inv y) = y := fun y => by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    apply hinj
    apply hreg
    change ((h i).appIso U'.1).inv a * c = ((h i).appIso U'.1).inv a * d at hcd
    have := congrArg ((h i).appIso U'.1).hom hcd
    rw [map_mul, map_mul, hinv] at this
    exact this
  · let 𝒱 : I.subscheme.OpenCover :=
      Scheme.Cover.mkOfCovers ι (fun i => (I.comap (h i)).subscheme)
        (fun i => (I.comapIso (h i)).hom ≫ pullback.snd (h i) I.subschemeι) (fun w => by
          obtain ⟨i, z, hz⟩ := hcov (I.subschemeι w)
          obtain ⟨t, -, ht⟩ := Scheme.Pullback.exists_preimage_pullback z w hz
          refine ⟨i, (I.comapIso (h i)).inv t, ?_⟩
          rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, ht]) (fun i => inferInstance)
    refine IsZariskiLocalAtSource.of_openCover 𝒱 fun i => ?_
    change Flat (((I.comapIso (h i)).hom ≫ pullback.snd (h i) I.subschemeι) ≫ I.subschemeι ≫ f)
    rw [Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
      Category.assoc, hcomm, ← Category.assoc, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    have : Flat ((I.comap (h i)).subschemeι ≫ g i) := (hI i).2
    infer_instance

end Langlands.AlgebraicGeometry.Picard.RelativeEffectiveLocal
