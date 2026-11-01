import Langlands.Geometry.Analytic.ChosenAtlasLocallyConstantTransport

/-! # Actual target-sieve gluing and chosen atlas pullback -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {D E : Type z}

section Pullback

variable (e : A ≅ B) {S : A.atlas.OriginalChartDomain}
  {R : Sieve (isoOriginalDomain e S)}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf B.atlas D) R.arrows)

/-- Restrict the actual target family to mapped arrows and pull its sections
back by the actual chosen domain homeomorphisms. -/
def isoOriginalDomainLocallyConstantPullbackFamily :
    Presieve.FamilyOfElements (locallyConstantPresheaf A.atlas D)
      (R.functorPullback (isoOriginalDomainEquivalence e).functor).arrows :=
  (p.functorPullback (isoOriginalDomainEquivalence e).functor).map
    (isoOriginalDomainLocallyConstant e D).hom

@[simp]
theorem isoOriginalDomainLocallyConstantPullbackFamily_apply
    {T : A.atlas.OriginalChartDomain} (f : T ⟶ S)
    (hf : (R.functorPullback (isoOriginalDomainEquivalence e).functor) f) (x : T) :
    (isoOriginalDomainLocallyConstantPullbackFamily e p f hf : LocallyConstant T D) x =
      (p ((isoOriginalDomainEquivalence e).functor.map f) hf :
        LocallyConstant (isoOriginalDomain e T) D) (isoOriginalDomainHomeomorph e T x) := rfl

/-- Target compatibility gives source compatibility by functorial pullback
and the literal restriction naturality of the section comparison. -/
theorem isoOriginalDomainLocallyConstantPullbackFamily_compatible (hp : p.Compatible) :
    (isoOriginalDomainLocallyConstantPullbackFamily e p).Compatible :=
  (hp.functorPullback (isoOriginalDomainEquivalence e).functor).map
    (isoOriginalDomainLocallyConstant e D).hom

/-- The actual target covering sieve has a covering functorial pullback. -/
theorem isoOriginalDomain_functorPullback_isCovering (hR : IsCovering R) :
    IsCovering (R.functorPullback (isoOriginalDomainEquivalence e).functor) :=
  (isoOriginalDomain_functorPullback_mem_iff e R).mpr hR

variable (hp : p.Compatible) (hR : IsCovering R)

/-- Construct the source glue from the full pulled-back matching family. -/
def isoOriginalDomainLocallyConstantPullbackGlue : LocallyConstant S D :=
  locallyConstantSieveGlue (isoOriginalDomainLocallyConstantPullbackFamily e p)
    (isoOriginalDomainLocallyConstantPullbackFamily_compatible e p hp)
    (isoOriginalDomain_functorPullback_isCovering e hR)

/-- The constructed source glue recovers every pulled-back local section
along its literal source inclusion. -/
theorem isoOriginalDomainLocallyConstantPullbackGlue_apply
    {T : A.atlas.OriginalChartDomain} (f : T ⟶ S)
    (hf : (R.functorPullback (isoOriginalDomainEquivalence e).functor) f) (x : T) :
    isoOriginalDomainLocallyConstantPullbackGlue e p hp hR
        (Set.inclusion (leOfHom f) x) =
      (p ((isoOriginalDomainEquivalence e).functor.map f) hf :
        LocallyConstant (isoOriginalDomain e T) D) (isoOriginalDomainHomeomorph e T x) :=
  locallyConstantSieveGlue_apply _ _ _ f hf x

/-- Gluing the restricted target family on the source sieve and transporting
back gives the literal target-site glue of the original family. -/
theorem isoOriginalDomainLocallyConstantImageGlue_eq_target :
    isoOriginalDomainLocallyConstantSieveGlue (D := D) e (S := S)
        (R := R.functorPullback (isoOriginalDomainEquivalence e).functor)
        (p.functorPullback (isoOriginalDomainEquivalence e).functor)
        (hp.functorPullback (isoOriginalDomainEquivalence e).functor)
        (isoOriginalDomain_functorPullback_isCovering e hR) =
      locallyConstantSieveGlue p hp hR := by
  symm
  apply isoOriginalDomainLocallyConstantSieveGlue_unique (D := D) e (S := S)
    (R := R.functorPullback (isoOriginalDomainEquivalence e).functor)
    (p.functorPullback (isoOriginalDomainEquivalence e).functor)
    (hp.functorPullback (isoOriginalDomainEquivalence e).functor)
    (isoOriginalDomain_functorPullback_isCovering e hR)
  intro T f hf
  ext x
  exact locallyConstantSieveGlue_apply p hp hR
    ((isoOriginalDomainEquivalence e).functor.map f) hf x

/-- Pullback of the literal target-site glue is exactly the source glue
constructed from its functorially pulled-back matching family. -/
theorem isoOriginalDomainLocallyConstantSieveGlue_functorPullback :
    isoOriginalDomainLocallyConstantEquiv e S (locallyConstantSieveGlue p hp hR) =
      isoOriginalDomainLocallyConstantPullbackGlue e p hp hR := by
  exact (congrArg (isoOriginalDomainLocallyConstantEquiv e S)
    (isoOriginalDomainLocallyConstantImageGlue_eq_target e p hp hR).symm).trans
    (isoOriginalDomainLocallyConstantSieveGlue_pullback (D := D) e (S := S)
    (R := R.functorPullback (isoOriginalDomainEquivalence e).functor)
    (p.functorPullback (isoOriginalDomainEquivalence e).functor)
    (hp.functorPullback (isoOriginalDomainEquivalence e).functor)
    (isoOriginalDomain_functorPullback_isCovering e hR))

/-- Descent of the constructed source glue recovers the entire literal
original target glue. -/
theorem isoOriginalDomainLocallyConstantPullbackGlue_descend :
    (isoOriginalDomainLocallyConstantEquiv e S).symm
        (isoOriginalDomainLocallyConstantPullbackGlue e p hp hR) =
      locallyConstantSieveGlue p hp hR := by
  rw [← isoOriginalDomainLocallyConstantSieveGlue_functorPullback e p hp hR]
  exact (isoOriginalDomainLocallyConstantEquiv e S).symm_apply_apply _

/-- Recovery holds on every original target sieve member, including those
not presented as direct images of source domains. -/
theorem isoOriginalDomainLocallyConstantPullbackGlue_target_apply
    {T : B.atlas.OriginalChartDomain} (f : T ⟶ isoOriginalDomain e S) (hf : R f) (x : T) :
    (isoOriginalDomainLocallyConstantEquiv e S).symm
        (isoOriginalDomainLocallyConstantPullbackGlue e p hp hR)
        (Set.inclusion (leOfHom f) x) = (p f hf : LocallyConstant T D) x := by
  rw [isoOriginalDomainLocallyConstantPullbackGlue_descend e p hp hR]
  exact locallyConstantSieveGlue_apply p hp hR f hf x

/-- Coefficient postcomposition commutes with pullback of the entire actual
matching family, before choosing any glue. -/
theorem isoOriginalDomainLocallyConstantPullbackFamily_map (φ : D → E) :
    isoOriginalDomainLocallyConstantPullbackFamily e
        (p.map (locallyConstantCoefficientMap φ)) =
      (isoOriginalDomainLocallyConstantPullbackFamily e p).map
        (locallyConstantCoefficientMap φ) := by
  ext T f hf x
  rfl

/-- Coefficient change commutes with the constructed source glue of every
actual target covering sieve. -/
theorem isoOriginalDomainLocallyConstantPullbackGlue_map (φ : D → E) :
    LocallyConstant.map φ (isoOriginalDomainLocallyConstantPullbackGlue e p hp hR) =
      isoOriginalDomainLocallyConstantPullbackGlue e
        (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR := by
  rw [← isoOriginalDomainLocallyConstantSieveGlue_functorPullback e p hp hR,
    ← isoOriginalDomainLocallyConstantSieveGlue_functorPullback e
      (p.map (locallyConstantCoefficientMap φ))
      (hp.map (locallyConstantCoefficientMap φ)) hR]
  ext x
  exact congrArg (fun f : LocallyConstant (isoOriginalDomain e S) E =>
    f (isoOriginalDomainHomeomorph e S x)) (locallyConstantSieveGlue_map φ p hp hR)

end Pullback

end Langlands.Analytic.AffinoidAtlasPresentation
