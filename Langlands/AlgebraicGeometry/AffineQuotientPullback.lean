import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Pullbacks of affine closed subschemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Extending an ideal and then quotienting is the pushout of its quotient map. -/
lemma isPushout_quotient_map (φ : A →+* B) (I : Ideal A) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I)) (CommRingCat.ofHom φ)
      (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) := by
  have hw : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)) := by
    ext x
    simp
  let d (c : PushoutCocone (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom φ)) : B ⧸ I.map φ →+* c.pt :=
    Ideal.Quotient.lift _ c.inr.hom (by
      have h : I.map φ ≤ RingHom.ker c.inr.hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change c.inr.hom (φ a) = 0
        have hc := congrArg (fun k : CommRingCat.of A ⟶ c.pt ↦ k a) c.condition
        simpa [Ideal.Quotient.eq_zero_iff_mem.mpr ha] using hc.symm
      exact fun b hb ↦ h hb)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
  refine PushoutCocone.IsColimit.mk hw (fun c ↦ CommRingCat.ofHom (d c)) ?_ ?_ ?_
  · intro c
    ext a
    change c.inr.hom (φ a) = c.inl.hom (Ideal.Quotient.mk I a)
    exact (congrArg (fun k : CommRingCat.of A ⟶ c.pt ↦ k a) c.condition).symm
  · intro c
    ext b
    rfl
  · intro c m _ hm
    ext b
    change m.hom (Ideal.Quotient.mk (I.map φ) b) = c.inr.hom b
    exact congrArg
      (fun k : CommRingCat.of B ⟶ c.pt ↦ k b) hm

/-- The affine quotient by the extended ideal is the pullback of the closed
subscheme defined by the original ideal. -/
def affineQuotientPullbackIso (φ : A →+* B) (I : Ideal A) :
    Spec (CommRingCat.of (B ⧸ I.map φ)) ≅
      pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        (Spec.map (CommRingCat.ofHom φ)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_map φ I)).isoPullback

@[reassoc (attr := simp)]
lemma affineQuotientPullbackIso_hom_fst (φ : A →+* B) (I : Ideal A) :
    (affineQuotientPullbackIso φ I).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_map φ I)).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma affineQuotientPullbackIso_hom_snd (φ : A →+* B) (I : Ideal A) :
    (affineQuotientPullbackIso φ I).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient_map φ I)).isoPullback_hom_snd

/-- A point lies in an affine closed subscheme precisely when its prime
contains the defining ideal. -/
lemma mem_range_SpecMap_quotient_iff (I : Ideal A) (x : Spec (CommRingCat.of A)) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ↔
      I ≤ x.asIdeal := by
  change x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) ↔ _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  rfl

end Langlands.AlgebraicGeometry
