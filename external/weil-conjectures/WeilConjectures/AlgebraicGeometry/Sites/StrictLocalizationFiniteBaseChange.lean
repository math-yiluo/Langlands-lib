/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
public import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselianFiniteAlgebraFactor

/-!
# Strict localization and finite base change

Let `g: S' ⟶ S` be a finite morphism, `s': Spec Ω ⟶ S'` a geometric point and `s = s' ≫ g`.
The morphism `S'_(s') ⟶ S_(s) ×_S S'` with components `strictLocalizationMap g s'` and
`strictLocalizationToBase s'` is an open and closed immersion: `S'_(s')` is the connected
component of `S_(s) ×_S S'` through the point `(s, s')`.

Indeed, `S_(s) ×_S S' = Spec B` with `B` finite over the strictly henselian local ring
`𝒪^{sh}_{S,s}`, hence `B` is a finite product of strictly henselian local rings
(`IsStrictlyHenselianLocalRing.exists_isIdempotentElem_quotient`). The factor `Spec B₀`
through the point `(s, s')` is an open and closed subscheme, and it is a strictly henselian
local scheme over `S'` with a geometric point over `s'`. By the universal property of the
strict localization (`exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing`,
`hom_strictLocalization_ext`) it is identified with `S'_(s')`.

## Main definitions

- `AlgebraicGeometry.Scheme.strictLocalizationToPullback g s'`:
  the morphism `S'_(s') ⟶ S_(s' ≫ g) ×_S S'`.

## Main results

- `AlgebraicGeometry.Scheme.isOpenImmersion_strictLocalizationToPullback`,
  `AlgebraicGeometry.Scheme.isClosedImmersion_strictLocalizationToPullback`: for `g` finite,
  it is an open and closed immersion.

## References

- Stacks Project, Lemma 10.153.4, <https://stacks.math.columbia.edu/tag/04GH>
- Stacks Project, Lemma 59.55.3, <https://stacks.math.columbia.edu/tag/0BSL>
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- Let `f : A ⟶ B` be an integral homomorphism of local rings and `ψ : B ⟶ K` a homomorphism to
a field such that `ψ ∘ f` is local. Then `ψ` is local: its kernel is a prime lying over the
maximal ideal of `A`, hence maximal. -/
lemma IsLocalHom.of_comp_of_isIntegral {A B K : Type*} [CommRing A] [CommRing B] [Field K]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : f.IsIntegral) (ψ : B →+* K)
    [IsLocalHom (ψ.comp f)] : IsLocalHom ψ := by
  have hker : (RingHom.ker ψ).comap f = IsLocalRing.maximalIdeal A := by
    rw [RingHom.comap_ker]
    ext a
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    refine ⟨fun ha hu ↦ ?_, fun ha ↦ ?_⟩
    · exact (hu.map (ψ.comp f)).ne_zero ha
    · by_contra h
      exact ha (isUnit_of_map_unit (ψ.comp f) a (isUnit_iff_ne_zero.2 h))
  have : (RingHom.ker ψ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap f hf _ (hker ▸ inferInstance)
  have hm : RingHom.ker ψ = IsLocalRing.maximalIdeal B := IsLocalRing.eq_maximalIdeal this
  refine ⟨fun a ha ↦ ?_⟩
  by_contra h
  have : a ∈ RingHom.ker ψ := hm ▸ h
  exact ha.ne_zero this

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (g : S' ⟶ S)
  (s' : Spec (.of Ω) ⟶ S')

/-- The morphism `S'_(s') ⟶ S_(s' ≫ g) ×_S S'` with components `strictLocalizationMap g s'` and
the structure morphism `S'_(s') ⟶ S'`. -/
noncomputable def strictLocalizationToPullback :
    strictLocalization s' ⟶ pullback (strictLocalizationToBase (s' ≫ g)) g :=
  pullback.lift (strictLocalizationMap g s') (strictLocalizationToBase s')
    (strictLocalizationMap_comp_strictLocalizationToBase g s')

@[reassoc (attr := simp)]
lemma strictLocalizationToPullback_fst :
    strictLocalizationToPullback g s' ≫ pullback.fst _ _ = strictLocalizationMap g s' :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma strictLocalizationToPullback_snd :
    strictLocalizationToPullback g s' ≫ pullback.snd _ _ = strictLocalizationToBase s' :=
  pullback.lift_snd _ _ _

/-- Let `ι₀ : Spec B₀ ⟶ S_(s' ≫ g) ×_S S'` be an open immersion from a strictly henselian local
scheme, through which the point `(s' ≫ g, s')` factors via a geometric point `p₀` over the closed
point. Then `strictLocalizationToPullback g s'` factors as an isomorphism followed by `ι₀`. -/
theorem exists_isIso_comp_eq_strictLocalizationToPullback (B₀ : Type u) [CommRing B₀]
    [IsStrictlyHenselianLocalRing B₀]
    (ι₀ : Spec (.of B₀) ⟶ pullback (strictLocalizationToBase (s' ≫ g)) g) [IsOpenImmersion ι₀]
    (p₀ : Spec (.of Ω) ⟶ Spec (.of B₀))
    (hp₀ : p₀ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint B₀)
    (hp : p₀ ≫ ι₀ = Spec.map (strictHenselizationEval s') ≫ strictLocalizationToPullback g s') :
    ∃ j₀ : strictLocalization s' ⟶ Spec (.of B₀),
      IsIso j₀ ∧ j₀ ≫ ι₀ = strictLocalizationToPullback g s' := by
  have hmem : strictLocalizationToPullback g s'
      (IsLocalRing.closedPoint (strictHenselization s')) ∈ ι₀.opensRange := by
    rw [← spec_map_strictHenselizationEval_apply s' (IsLocalRing.closedPoint Ω),
      ← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hrange : Set.range (strictLocalizationToPullback g s') ⊆ Set.range ι₀ := by
    rintro _ ⟨x, rfl⟩
    have h := preimage_eq_top_of_closedPoint_mem (strictLocalizationToPullback g s') hmem
    have hx : x ∈ (strictLocalizationToPullback g s') ⁻¹ᵁ ι₀.opensRange := by
      rw [h]
      trivial
    exact hx
  let j₀ := IsOpenImmersion.lift ι₀ (strictLocalizationToPullback g s') hrange
  have hj₀ : j₀ ≫ ι₀ = strictLocalizationToPullback g s' := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, hk, hpk⟩ := exists_hom_strictLocalization_of_isStrictlyHenselianLocalRing s'
    (ι₀ ≫ pullback.snd _ _) p₀ hp₀ (by
      rw [reassoc_of% hp, strictLocalizationToPullback_snd,
        spec_map_strictHenselizationEval_comp_strictLocalizationToBase])
  have hpj₀ : Spec.map (strictHenselizationEval s') ≫ j₀ = p₀ := by
    rw [← cancel_mono ι₀, Category.assoc, hj₀, hp]
  have h₁ : j₀ ≫ k = 𝟙 _ := by
    refine hom_strictLocalization_ext s' ?_ (Spec.map (strictHenselizationEval s'))
      (IsLocalRing.closedPoint Ω) (spec_map_strictHenselizationEval_apply s' _) ?_
    · rw [Category.assoc, hk, reassoc_of% hj₀, strictLocalizationToPullback_snd,
        Category.id_comp]
    · rw [reassoc_of% hpj₀, hpk, Category.comp_id]
  have h₂ : k ≫ j₀ = 𝟙 _ := by
    rw [← cancel_mono ι₀, Category.assoc, hj₀, Category.id_comp]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, strictLocalizationToPullback_fst]
      refine hom_strictLocalization_ext (s' ≫ g) ?_ p₀ (IsLocalRing.closedPoint Ω) hp₀ ?_
      · rw [Category.assoc, strictLocalizationMap_comp_strictLocalizationToBase, reassoc_of% hk,
          Category.assoc, pullback.condition]
      · rw [reassoc_of% hpk, spec_map_strictHenselizationEval_comp_strictLocalizationMap,
          reassoc_of% hp, strictLocalizationToPullback_fst,
          spec_map_strictHenselizationEval_comp_strictLocalizationMap]
    · rw [Category.assoc, strictLocalizationToPullback_snd, hk]
  exact ⟨j₀, ⟨k, h₁, h₂⟩, hj₀⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Strict localization and finite base change.** For `g: S' ⟶ S` finite, the morphism
`S'_(s') ⟶ S_(s' ≫ g) ×_S S'` is an open and closed immersion. -/
theorem isOpenImmersion_and_isClosedImmersion_strictLocalizationToPullback [IsFinite g] :
    IsOpenImmersion (strictLocalizationToPullback g s') ∧
      IsClosedImmersion (strictLocalizationToPullback g s') := by
  let P := pullback (strictLocalizationToBase (s' ≫ g)) g
  have : IsAffine P := isAffine_of_isAffineHom (pullback.fst (strictLocalizationToBase (s' ≫ g)) g)
  let φ : strictHenselization (s' ≫ g) ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ pullback.fst _ _)
  have hφ : Spec.map φ = P.isoSpec.inv ≫ pullback.fst _ _ := Spec.map_preimage _
  have hφf : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  algebraize [φ.hom]
  let ψ : Γ(P, ⊤) ⟶ CommRingCat.of Ω := Spec.preimage
    (Spec.map (strictHenselizationEval s') ≫ strictLocalizationToPullback g s' ≫ P.isoSpec.hom)
  have hψ : Spec.map ψ =
      Spec.map (strictHenselizationEval s') ≫ strictLocalizationToPullback g s' ≫
        P.isoSpec.hom :=
    Spec.map_preimage _
  have := isStrictlyHenselianLocalRing_strictHenselization (s' ≫ g)
  obtain ⟨e, he, heq, hsh⟩ := IsStrictlyHenselianLocalRing.exists_isIdempotentElem_quotient
    (strictHenselization (s' ≫ g)) Γ(P, ⊤) (RingHom.ker ψ.hom)
  let I := Ideal.span {1 - e}
  let π : Γ(P, ⊤) ⟶ CommRingCat.of (Γ(P, ⊤) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  let ι₀ : Spec (.of (Γ(P, ⊤) ⧸ I)) ⟶ P := Spec.map π ≫ P.isoSpec.inv
  have : IsLocalization.Away e (Γ(P, ⊤) ⧸ I) := IsLocalization.Away.quotient_of_isIdempotentElem he
  have : IsOpenImmersion (Spec.map π) := IsOpenImmersion.of_isLocalization (S := Γ(P, ⊤) ⧸ I) e
  have : IsClosedImmersion (Spec.map π) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : I ≤ RingHom.ker ψ.hom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact heq
  let ψ₀ : CommRingCat.of (Γ(P, ⊤) ⧸ I) ⟶ CommRingCat.of Ω :=
    CommRingCat.ofHom (Ideal.Quotient.lift I ψ.hom hle)
  have hψψ₀ : π ≫ ψ₀ = ψ := by
    ext
    rfl
  have hp : Spec.map ψ₀ ≫ ι₀ =
      Spec.map (strictHenselizationEval s') ≫ strictLocalizationToPullback g s' := by
    rw [← Spec.map_comp_assoc, hψψ₀, hψ, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hφψ : φ ≫ ψ = strictHenselizationEval (s' ≫ g) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hφ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      strictLocalizationToPullback_fst, spec_map_strictHenselizationEval_comp_strictLocalizationMap]
  have hint : (algebraMap (strictHenselization (s' ≫ g)) (Γ(P, ⊤) ⧸ I)).IsIntegral :=
    RingHom.IsIntegral.trans _ _ hφf.to_isIntegral
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  have : IsLocalHom (ψ₀.hom.comp (algebraMap (strictHenselization (s' ≫ g)) (Γ(P, ⊤) ⧸ I))) := by
    have h : ψ₀.hom.comp (algebraMap (strictHenselization (s' ≫ g)) (Γ(P, ⊤) ⧸ I)) =
        (strictHenselizationEval (s' ≫ g)).hom := by
      rw [← hφψ]
      rfl
    rw [h]
    infer_instance
  have : IsLocalHom ψ₀.hom := IsLocalHom.of_comp_of_isIntegral _ hint ψ₀.hom
  have hp₀ : Spec.map ψ₀ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint (Γ(P, ⊤) ⧸ I) :=
    IsLocalRing.comap_closedPoint ψ₀.hom
  obtain ⟨j₀, hiso, hj₀⟩ :=
    exists_isIso_comp_eq_strictLocalizationToPullback g s' _ ι₀ (Spec.map ψ₀) hp₀ hp
  rw [← hj₀]
  exact ⟨inferInstance, inferInstance⟩

/-- **Strict localization and finite base change**: `S'_(s') ⟶ S_(s' ≫ g) ×_S S'` is an open
immersion for `g` finite. -/
instance isOpenImmersion_strictLocalizationToPullback [IsFinite g] :
    IsOpenImmersion (strictLocalizationToPullback g s') :=
  (isOpenImmersion_and_isClosedImmersion_strictLocalizationToPullback g s').1

/-- **Strict localization and finite base change**: `S'_(s') ⟶ S_(s' ≫ g) ×_S S'` is a closed
immersion for `g` finite. -/
instance isClosedImmersion_strictLocalizationToPullback [IsFinite g] :
    IsClosedImmersion (strictLocalizationToPullback g s') :=
  (isOpenImmersion_and_isClosedImmersion_strictLocalizationToPullback g s').2

end AlgebraicGeometry.Scheme
