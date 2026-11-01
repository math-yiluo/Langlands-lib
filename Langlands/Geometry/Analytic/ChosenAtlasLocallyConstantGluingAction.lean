import Langlands.Geometry.Analytic.ChosenAtlasLocallyConstantAction
import Langlands.Geometry.Analytic.ChosenAtlasLocallyConstantSievePullback

/-! # Equivariance of actual arbitrary-sieve locally constant gluing -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {D E : Type z}

namespace OriginalDomainSection

section Gluing

variable {S : A.atlas.OriginalChartDomain} {R : Sieve S}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf A.atlas D) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)

/-- The actual source-sieve glue together with its original domain. -/
def sieveGlue : OriginalDomainSection A D :=
  ⟨S, locallyConstantSieveGlue p hp hR⟩

@[simp]
theorem sieveGlue_domain : (sieveGlue p hp hR).domain = S := rfl

/-- The whole restricted pair is the original local domain-section pair. -/
theorem sieveGlue_restrict {T : A.atlas.OriginalChartDomain}
    (f : T ⟶ S) (hf : R f) :
    restrict (sieveGlue p hp hR) T (leOfHom f) =
      ⟨T, (p f hf : LocallyConstant T D)⟩ := by
  apply OriginalDomainSection.ext
  · rfl
  · intro x hs hr
    exact locallyConstantSieveGlue_apply p hp hR f hf ⟨x, hs⟩

/-- Coefficient change commutes with gluing the entire domain-section pair. -/
theorem sieveGlue_map (φ : D → E) :
    map φ (sieveGlue p hp hR) =
      sieveGlue (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR := by
  apply OriginalDomainSection.ext
  · rfl
  · intro x hs hr
    exact congrArg (fun f : LocallyConstant S E => f ⟨x, hs⟩)
      (locallyConstantSieveGlue_map φ p hp hR)

end Gluing

section Pullback

variable (e : A ≅ B) {S : A.atlas.OriginalChartDomain}
  {R : Sieve (isoOriginalDomain e S)}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf B.atlas D) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)

/-- Glue the entire functorially pulled-back matching family on its actual
source domain. -/
def pullbackSieveGlue : OriginalDomainSection A D :=
  sieveGlue (isoOriginalDomainLocallyConstantPullbackFamily e p)
    (isoOriginalDomainLocallyConstantPullbackFamily_compatible e p hp)
    (isoOriginalDomain_functorPullback_isCovering e hR)

/-- Moving the constructed source glue gives the literal original target
glue, as equality of the whole domain-section pairs. -/
theorem transport_pullbackSieveGlue :
    transport e (pullbackSieveGlue e p hp hR) = sieveGlue p hp hR := by
  apply OriginalDomainSection.ext
  · rfl
  · intro x hs hr
    exact congrArg (fun f : LocallyConstant (isoOriginalDomain e S) D => f ⟨x, hs⟩)
      (isoOriginalDomainLocallyConstantPullbackGlue_descend e p hp hR)

/-- Every original target sieve member is recovered as a full restricted pair. -/
theorem transport_pullbackSieveGlue_restrict
    {T : B.atlas.OriginalChartDomain} (f : T ⟶ isoOriginalDomain e S) (hf : R f) :
    restrict (transport e (pullbackSieveGlue e p hp hR)) T (leOfHom f) =
      ⟨T, (p f hf : LocallyConstant T D)⟩ := by
  have hv := isoOriginalDomainLocallyConstantPullbackGlue_target_apply e p hp hR f hf
  apply OriginalDomainSection.ext
  · rfl
  · intro x hs hr
    exact hv ⟨x, hs⟩

/-- The source construction also commutes with arbitrary coefficient functions. -/
theorem pullbackSieveGlue_map (φ : D → E) :
    map φ (pullbackSieveGlue e p hp hR) =
      pullbackSieveGlue e (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR := by
  apply OriginalDomainSection.ext
  · rfl
  · intro x hs hr
    exact congrArg (fun f : LocallyConstant S E => f ⟨x, hs⟩)
      (isoOriginalDomainLocallyConstantPullbackGlue_map e p hp hR φ)

end Pullback

end OriginalDomainSection

namespace ChosenAtlasSectionAction

variable {G : Type t} [Group G]
  (X : Action (AffinoidAtlasPresentation.{u, v, w} K) G)
  (g : G) {S : X.V.atlas.OriginalChartDomain}
  {R : Sieve (isoOriginalDomain (X.ρAut g) S)}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf X.V.atlas D) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)

/-- The actual induced group action takes the constructed pullback glue to
the original target-sieve glue. -/
theorem action_pullbackSieveGlue :
    ((action X D).ρ g).hom
        (OriginalDomainSection.pullbackSieveGlue (X.ρAut g) p hp hR) =
      OriginalDomainSection.sieveGlue p hp hR :=
  OriginalDomainSection.transport_pullbackSieveGlue (X.ρAut g) p hp hR

/-- The action recovers each whole original local domain-section pair,
including target members not supplied as direct image presentations. -/
theorem action_pullbackSieveGlue_restrict
    {T : X.V.atlas.OriginalChartDomain}
    (f : T ⟶ isoOriginalDomain (X.ρAut g) S) (hf : R f) :
    OriginalDomainSection.restrict
        (((action X D).ρ g).hom
          (OriginalDomainSection.pullbackSieveGlue (X.ρAut g) p hp hR))
        T (leOfHom f) =
      ⟨T, (p f hf : LocallyConstant T D)⟩ :=
  OriginalDomainSection.transport_pullbackSieveGlue_restrict (X.ρAut g) p hp hR f hf

/-- In particular, every original local value is recovered at its literal
target inclusion under the actual group action. -/
theorem action_pullbackSieveGlue_apply
    {T : X.V.atlas.OriginalChartDomain}
    (f : T ⟶ isoOriginalDomain (X.ρAut g) S) (hf : R f) (x : T) :
    (((action X D).ρ g).hom
      (OriginalDomainSection.pullbackSieveGlue (X.ρAut g) p hp hR)).value
        (Set.inclusion (leOfHom f) x) = (p f hf : LocallyConstant T D) x :=
  isoOriginalDomainLocallyConstantPullbackGlue_target_apply (X.ρAut g) p hp hR f hf x

/-- The actual equivariant coefficient map takes the constructed source glue
to the source glue of the full coefficient-mapped target family. -/
theorem coefficientMap_pullbackSieveGlue (φ : D → E) :
    (coefficientMap X φ).hom.hom
        (OriginalDomainSection.pullbackSieveGlue (X.ρAut g) p hp hR) =
      OriginalDomainSection.pullbackSieveGlue (X.ρAut g)
        (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR :=
  OriginalDomainSection.pullbackSieveGlue_map (X.ρAut g) p hp hR φ

/-- Acting and then changing coefficients gives the original target glue
for the entire coefficient-mapped matching family. -/
theorem action_pullbackSieveGlue_map (φ : D → E) :
    (coefficientMap X φ).hom.hom
        (((action X D).ρ g).hom
          (OriginalDomainSection.pullbackSieveGlue (X.ρAut g) p hp hR)) =
      OriginalDomainSection.sieveGlue (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR := by
  rw [action_pullbackSieveGlue X g p hp hR]
  exact OriginalDomainSection.sieveGlue_map p hp hR φ

end ChosenAtlasSectionAction

end Langlands.Analytic.AffinoidAtlasPresentation
