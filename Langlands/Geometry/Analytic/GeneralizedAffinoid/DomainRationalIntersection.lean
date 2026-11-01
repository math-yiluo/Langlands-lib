import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartBaseChange

/-! # Intersecting a full affinoid domain with an actual rational chart -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem spectrum_comp (i : BoundedAlgHom K A B) (j : BoundedAlgHom K B C)
    (x : BanachSpectrum C) :
    BanachSpectrum.comap (j.comp i).toBoundedRingHom x =
      BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap j.toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Representing the entire inverse image of a closed ambient set gives a
representation of its intersection with the outer full domain. No structural
spectrum map is assumed injective. -/
theorem Represents.comp_preimage {i : BoundedAlgHom K A B}
    {j : BoundedAlgHom K B C} {U V : Set (BanachSpectrum A)}
    (hi : Represents K i U)
    (hj : Represents K j ((BanachSpectrum.comap i.toBoundedRingHom) ⁻¹' V))
    (hV : IsClosed V) : Represents K (j.comp i) (U ∩ V) := by
  refine ⟨hi.1.inter hV, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      rw [spectrum_comp]
      exact ⟨hi.hasImageIn _, hj.hasImageIn z⟩
    · rintro ⟨hU, hV⟩
      obtain ⟨y, hy⟩ := hi.2.1.symm ▸ hU
      have hyV : y ∈ (BanachSpectrum.comap i.toBoundedRingHom) ⁻¹' V := by
        change BanachSpectrum.comap i.toBoundedRingHom y ∈ V
        exact hy.symm ▸ hV
      obtain ⟨z, hz⟩ := hj.2.1.symm ▸ hyV
      exact ⟨z, (spectrum_comp i j z).trans ((congrArg _ hz).trans hy)⟩
  · intro R φ hφ
    obtain ⟨ψ, hψ, hψuniq⟩ := hi.2.2 R φ (fun x => (hφ x).1)
    have hpre : HasImageIn K ψ
        ((BanachSpectrum.comap i.toBoundedRingHom) ⁻¹' V) := by
      intro x
      change BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap ψ.toBoundedRingHom x) ∈ V
      rw [← spectrum_comp, hψ]
      exact (hφ x).2
    obtain ⟨θ, hθ, hθuniq⟩ := hj.2.2 R ψ hpre
    refine ⟨θ, ?_, ?_⟩
    · change (θ.comp j).comp i = φ
      rw [hθ, hψ]
    · intro θ' hθ'
      apply hθuniq θ'
      exact hψuniq (θ'.comp j) hθ'

namespace Domain

private theorem hom_unique {U V : Domain K A} (f g : U ⟶ V) : f = g :=
  @Subsingleton.elim (Inclusion U V) inferInstance f g

/-- The pulled rational quotient over the actual algebra of U represents the
ambient intersection, with its two bounded structural maps composed. -/
def rationalInter (U : Domain K A) (d : RationalChart K A) : Domain K A where
  algebra := (RationalChart.pullback U.baseMap d).algebra
  baseMap := (RationalChart.pullback U.baseMap d).baseMap.comp U.baseMap
  locus := U.locus ∩ d.locus
  represents := U.represents.comp_preimage
    (by
      rw [← RationalChart.pullback_locus U.baseMap d]
      exact (RationalChart.pullback U.baseMap d).represents)
    d.represents.1

@[simp] theorem rationalInter_algebra (U : Domain K A) (d : RationalChart K A) :
    (U.rationalInter d).algebra = (RationalChart.pullback U.baseMap d).algebra := rfl

@[simp] theorem rationalInter_baseMap (U : Domain K A) (d : RationalChart K A) :
    (U.rationalInter d).baseMap =
      (RationalChart.pullback U.baseMap d).baseMap.comp U.baseMap := rfl

@[simp] theorem rationalInter_locus (U : Domain K A) (d : RationalChart K A) :
    (U.rationalInter d).locus = U.locus ∩ d.locus := rfl

/-- Projection to the full domain is the pulled rational quotient's actual
bounded structural map. -/
def rationalInterLeft (U : Domain K A) (d : RationalChart K A) :
    U.rationalInter d ⟶ U where
  restriction := (RationalChart.pullback U.baseMap d).baseMap
  comp_baseMap := rfl

/-- Projection to the ambient rational chart is actual quotient transport
along the full domain's bounded structural map. -/
def rationalInterRight (U : Domain K A) (d : RationalChart K A) :
    U.rationalInter d ⟶ d.toDomain where
  restriction := RationalChart.pullbackMap U.baseMap d
  comp_baseMap := RationalChart.pullbackMap_comp_baseMap U.baseMap d

@[simp] theorem rationalInterLeft_restriction (U : Domain K A)
    (d : RationalChart K A) :
    (U.rationalInterLeft d).restriction =
      (RationalChart.pullback U.baseMap d).baseMap := rfl

@[simp] theorem rationalInterRight_restriction (U : Domain K A)
    (d : RationalChart K A) :
    (U.rationalInterRight d).restriction = RationalChart.pullbackMap U.baseMap d := rfl

/-- Full representation constructs the lift from the two actual inclusions,
by their intersection of image containments. -/
def rationalInterLift {U W : Domain K A} {d : RationalChart K A}
    (f : W ⟶ U) (g : W ⟶ d.toDomain) : W ⟶ U.rationalInter d :=
  inclusionOfSubset W (U.rationalInter d) (fun _ hx => ⟨f.subset hx, g.subset hx⟩)

@[simp] theorem rationalInterLift_left {U W : Domain K A} {d : RationalChart K A}
    (f : W ⟶ U) (g : W ⟶ d.toDomain) :
    rationalInterLift f g ≫ U.rationalInterLeft d = f :=
  @Subsingleton.elim (Inclusion W U) inferInstance _ _

@[simp] theorem rationalInterLift_right {U W : Domain K A} {d : RationalChart K A}
    (f : W ⟶ U) (g : W ⟶ d.toDomain) :
    rationalInterLift f g ≫ U.rationalInterRight d = g :=
  @Subsingleton.elim (Inclusion W d.toDomain) inferInstance _ _

/-- The constructed intersection supplies a cone over any common containing
full domain, with its actual two bounded projections. -/
def rationalInterPullbackCone {U W : Domain K A} {d : RationalChart K A}
    (f : U ⟶ W) (g : d.toDomain ⟶ W) : PullbackCone f g :=
  PullbackCone.mk (U.rationalInterLeft d) (U.rationalInterRight d)
    (@Subsingleton.elim (Inclusion (U.rationalInter d) W) inferInstance _ _)

/-- Image containment constructs each limit lift, and full-test uniqueness
proves all projection and uniqueness equations. -/
def rationalInterPullbackConeIsLimit {U W : Domain K A} {d : RationalChart K A}
    (f : U ⟶ W) (g : d.toDomain ⟶ W) :
    IsLimit (rationalInterPullbackCone f g) :=
  PullbackCone.IsLimit.mk _
    (fun S => rationalInterLift S.fst S.snd)
    (fun _ => hom_unique _ _)
    (fun _ => hom_unique _ _)
    (fun _ _ _ _ => hom_unique _ _)

/-- The same actual quotient spectrum and two bounded-map projections form
the topological pullback over the ambient algebra spectrum. -/
def rationalInterSpectrumCone (U : Domain K A) (d : RationalChart K A) :
    PullbackCone (TopCat.ofHom U.spectrumMap) (TopCat.ofHom d.spectrumMap) :=
  RationalChart.pullbackSpectrumCone U.baseMap d

@[simp] theorem rationalInterSpectrumCone_pt (U : Domain K A) (d : RationalChart K A) :
    (U.rationalInterSpectrumCone d).pt =
      TopCat.of (BanachSpectrum (U.rationalInter d).algebra) := rfl

@[simp] theorem rationalInterSpectrumCone_fst (U : Domain K A) (d : RationalChart K A) :
    (U.rationalInterSpectrumCone d).fst =
      TopCat.ofHom (U.rationalInterLeft d).spectrumMap := rfl

@[simp] theorem rationalInterSpectrumCone_snd (U : Domain K A) (d : RationalChart K A) :
    (U.rationalInterSpectrumCone d).snd =
      TopCat.ofHom (U.rationalInterRight d).spectrumMap := rfl

/-- The concrete spectrum limit follows from the proved rational coefficient
base-change construction, with U.baseMap as its actual coefficient map. -/
def rationalInterSpectrumConeIsLimit (U : Domain K A) (d : RationalChart K A) :
    IsLimit (U.rationalInterSpectrumCone d) :=
  RationalChart.pullbackSpectrumConeIsLimit U.baseMap d

end Domain
end Langlands.Analytic.PresentedAffinoidAlgebra
