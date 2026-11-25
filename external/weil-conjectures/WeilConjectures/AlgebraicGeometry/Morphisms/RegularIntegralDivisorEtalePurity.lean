/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import WeilConjectures.AlgebraicGeometry.Morphisms.RegularIntegralDivisorBoundary
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularCodimensionTwoEtaleExtension

/-!
# Purity across a regular integral effective Cartier divisor

## References

* Tag 0EYJ, second paragraph
* Stacks Project, Tag 0EYE (Lemma 58.31.3), applied as in Tag 0EYJ
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem etale_restrict_sup {L N : Scheme.{u}} (n : N ⟶ L)
    (U W : L.Opens) (hU : Etale (n ∣_ U)) (hW : Etale (n ∣_ W)) :
    Etale (n ∣_ (U ⊔ W)) := by
  let T := U ⊔ W
  let J : Bool → L.Opens := fun b ↦ if b then U else W
  have hJ : ∀ b, J b ≤ T := by
    intro b
    cases b <;> simp [J, T]
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @Etale) (fun b ↦ T.ι ⁻¹ᵁ J b)
  · ext y
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      TopologicalSpace.Opens.map_coe, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
      Set.mem_preimage, Opens.ι_apply, SetLike.mem_coe, Bool.exists_bool,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact Or.symm y.property
  · intro b
    have hI : T.ι ''ᵁ (T.ι ⁻¹ᵁ J b) = J b := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (hJ b)
    have hEt : Etale (n ∣_ T.ι ''ᵁ (T.ι ⁻¹ᵁ J b)) := by
      rw [hI]
      cases b
      · simpa [J] using hW
      · simpa [J] using hU
    exact (MorphismProperty.arrow_mk_iso_iff @Etale
      (morphismRestrictRestrict n T (T.ι ⁻¹ᵁ J b))).mpr hEt

private theorem restrict_over_iso {L N E : Scheme.{u}} (n : N ⟶ L) (p : E ⟶ L)
    {U V : L.Opens} (hUV : U ≤ V)
    (e : (n ⁻¹ᵁ V).toScheme ≅ (p ⁻¹ᵁ V).toScheme)
    (he : e.hom ≫ (p ∣_ V) = n ∣_ V) :
    ∃ e' : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme,
      e'.hom ≫ (p ∣_ U) = n ∣_ U := by
  let A := n ⁻¹ᵁ V
  let B := p ⁻¹ᵁ V
  let UA := A.ι ⁻¹ᵁ (n ⁻¹ᵁ U)
  let UB := B.ι ⁻¹ᵁ (p ⁻¹ᵁ U)
  have hfac : e.hom ≫ B.ι ≫ p = A.ι ≫ n := by
    rw [← morphismRestrict_ι, ← Category.assoc, he, morphismRestrict_ι]
  have hpre : e.hom ⁻¹ᵁ UB = UA := by
    change e.hom ⁻¹ᵁ (B.ι ⁻¹ᵁ (p ⁻¹ᵁ U)) = A.ι ⁻¹ᵁ (n ⁻¹ᵁ U)
    rw [← Hom.comp_preimage, ← Hom.comp_preimage, Category.assoc, hfac, Hom.comp_preimage]
  let a := Opens.isoOfLE (n.preimage_mono hUV)
  let b := Opens.isoOfLE (p.preimage_mono hUV)
  let c := A.toScheme.isoOfEq hpre.symm ≪≫ e.hom.preimageIso UB
  let e' := a.symm ≪≫ c ≪≫ b
  refine ⟨e', ?_⟩
  apply (cancel_mono U.ι).mp
  have hc : c.hom ≫ UB.ι = UA.ι ≫ e.hom := by
    simp [c]
  have hb : b.hom ≫ (p ⁻¹ᵁ U).ι = UB.ι ≫ B.ι :=
    Opens.isoOfLE_hom_ι (p.preimage_mono hUV)
  have ha : a.inv ≫ UA.ι ≫ A.ι = (n ⁻¹ᵁ U).ι :=
    Opens.isoOfLE_inv_ι (n.preimage_mono hUV)
  dsimp only [e', Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [← Category.assoc b.hom, hb]
  simp only [Category.assoc]
  rw [← Category.assoc c.hom, hc]
  simp only [Category.assoc]
  rw [hfac]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ n) ha

/-- A finite cover, etale off a regular integral Cartier divisor and near its
unique generic point, has a finite etale extension of its restriction. -/
theorem exists_finite_etale_extension_of_regular_integral_divisor
    {L D N : Scheme.{u}} [IsLocallyNoetherian L] [IsRegular D] [IsIntegral D]
    (i : D ⟶ L) (hi : IsEffectiveCartierCenter i)
    (U : L.Opens) (hU : ∀ z : L, z ∈ U ↔ z ∉ Set.range i)
    (n : N ⟶ L) [IsFinite n] (het : Etale (n ∣_ U))
    (W : L.Opens) (hgeneric : i (genericPoint D) ∈ W) (hW : Etale (n ∣_ W)) :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : (n ⁻¹ᵁ U).toScheme ≅ (p ⁻¹ᵁ U).toScheme,
        e.hom ≫ (p ∣_ U) = n ∣_ U := by
  let V := U ⊔ W
  have hboundary := regular_dim_ge_two_outside_divisor_generic_neighbourhood
    i hi U hU W hgeneric
  have : Etale (n ∣_ V) := etale_restrict_sup n U W het hW
  obtain ⟨E, p, hpfin, hpet, e, he⟩ :=
    exists_finite_etale_extension_of_regular_codimension_two_boundary V hboundary (n ∣_ V)
  exact ⟨E, p, hpfin, hpet, restrict_over_iso n p le_sup_left e he⟩

end AlgebraicGeometry.Scheme
