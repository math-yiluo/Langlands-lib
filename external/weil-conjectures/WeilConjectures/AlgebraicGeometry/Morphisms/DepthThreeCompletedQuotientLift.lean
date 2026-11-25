/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedQuotientCoverLift
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedPuncturedQuotientFullyFaithful

/-! # Lifting the quotient cover over the maximal-ideal completion

## References

* Stacks Project, proof of Tag 0BLS, Tags 0BM6, 09ZL, 0AVY and 0A02
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The prescribed quotient restriction lifts over the completion. -/
theorem exists_completed_etale_extension_of_depth_three_of_quotient_extension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q]
    (hquot :
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let V := i ⁻¹ᵁ U
      ∃ (F₀ : Scheme.{u}) (r₀ : F₀ ⟶ Spec (.of (A ⧸ Ideal.span {f}))),
        IsFinite r₀ ∧ Etale r₀ ∧
          ∃ e₀ : pullback q (i ∣_ U) ≅ (r₀ ⁻¹ᵁ V).toScheme,
            e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
    let W := c ⁻¹ᵁ U
    ∃ (E : Scheme.{u}) (s : E ⟶ Spec (.of C)), IsFinite s ∧ Etale s ∧
      ∃ e : pullback q (c ∣_ U) ≅ (s ⁻¹ᵁ W).toScheme,
        e.hom ≫ s ∣_ W = pullback.snd q (c ∣_ U) := by
  classical
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let W := c ⁻¹ᵁ U
  let j := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {algebraMap A C f})))
  obtain ⟨E, s, hsfin, hset, e₀, he₀⟩ :=
    exists_completed_cover_with_quotient_iso A f hf U q hquot
  let := hsfin
  let := hset
  let P : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ W.toScheme :=
    MorphismProperty.Over.mk ⊤ (pullback.snd q (c ∣_ U))
      ⟨inferInstance, inferInstance⟩
  let Q : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ W.toScheme :=
    MorphismProperty.Over.mk ⊤ (s ∣_ W) ⟨inferInstance, inferInstance⟩
  let F := MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ (j ∣_ W)
  let a₀ : F.obj P ≅ F.obj Q := MorphismProperty.Over.isoMk e₀ he₀
  obtain ⟨hff⟩ := fullyFaithful_completed_punctured_quotient A f hf hdepth U hU
  let a : P ≅ Q := hff.preimageIso a₀
  refine ⟨E, s, hsfin, hset, ?_⟩
  refine ⟨((MorphismProperty.Over.forget _ ⊤ W.toScheme) ⋙
    CategoryTheory.Over.forget W.toScheme).mapIso a, ?_⟩
  exact MorphismProperty.Over.w a.hom

end AlgebraicGeometry.Scheme
