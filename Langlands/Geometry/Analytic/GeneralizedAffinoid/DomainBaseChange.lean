import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection

/-! # Actual inverse images of full affinoid domains and finite covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K A B)

/-- The actual affinoid pushout leg represents the full spectrum inverse image. -/
theorem represents_pullback (U : Domain K A) :
    Represents K (AffinoidPushout.leftMap φ U.baseMap)
      ((BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' U.locus) := by
  let Q := AffinoidPushout.algebra φ U.baseMap
  let l := AffinoidPushout.leftMap φ U.baseMap
  let r := AffinoidPushout.rightMap φ U.baseMap
  have hcomm : l.comp φ = r.comp U.baseMap := AffinoidPushout.condition φ U.baseMap
  have heq (z : BanachSpectrum Q) :
      BanachSpectrum.comap φ.toBoundedRingHom
          (BanachSpectrum.comap l.toBoundedRingHom z) =
        U.spectrumMap (BanachSpectrum.comap r.toBoundedRingHom z) := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun h : BoundedAlgHom K A Q => z (h a)) hcomm
  refine ⟨U.represents.1.preimage (BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous,
    ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨z, rfl⟩
      change BanachSpectrum.comap φ.toBoundedRingHom
        (BanachSpectrum.comap l.toBoundedRingHom z) ∈ U.locus
      rw [heq]
      exact U.represents.hasImageIn _
    · intro hx
      obtain ⟨y, hy⟩ := U.represents.2.1.symm ▸ hx
      obtain ⟨z, hzx, _⟩ := AffinoidPushout.exists_point φ U.baseMap x y hy.symm
      exact ⟨z, hzx⟩
  · intro R ψ hψ
    have himage : HasImageIn K (ψ.comp φ) U.locus := fun z => hψ z
    obtain ⟨β, hβ, hβuniq⟩ := U.represents.2.2 R (ψ.comp φ) himage
    let θ := AffinoidPushout.lift φ U.baseMap R ψ β hβ.symm
    have hθl : θ.comp l = ψ := AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _
    have hθr : θ.comp r = β := AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _
    refine ⟨θ, hθl, ?_⟩
    intro η hη
    apply AffinoidPushout.hom_ext φ U.baseMap R
    · exact hη.trans hθl.symm
    · rw [hθr]
      apply hβuniq
      change η.comp (r.comp U.baseMap) = ψ.comp φ
      rw [← hcomm, ← BoundedAlgHom.comp_assoc, hη]

/-- The actual inverse-image full domain uses the constructed pushout quotient. -/
def pullback (U : Domain K A) : Domain K B where
  algebra := AffinoidPushout.algebra φ U.baseMap
  baseMap := AffinoidPushout.leftMap φ U.baseMap
  locus := (BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' U.locus
  represents := represents_pullback φ U

@[simp]
theorem pullback_locus (U : Domain K A) :
    (pullback φ U).locus = (BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' U.locus := rfl

@[simp]
theorem pullback_algebra (U : Domain K A) :
    (pullback φ U).algebra = AffinoidPushout.algebra φ U.baseMap := rfl

/-- The second original quotient leg transports the actual domain algebra. -/
def pullbackMap (U : Domain K A) : BoundedAlgHom K U.algebra (pullback φ U).algebra :=
  AffinoidPushout.rightMap φ U.baseMap

/-- The original bounded structural square commutes. -/
theorem pullbackMap_comp_baseMap (U : Domain K A) :
    (pullbackMap φ U).comp U.baseMap = (pullback φ U).baseMap.comp φ :=
  (AffinoidPushout.condition φ U.baseMap).symm

private theorem pullbackRestriction_compatible {U V : Domain K A} (f : U ⟶ V) :
    (pullback φ U).baseMap.comp φ =
      ((pullbackMap φ U).comp f.restriction).comp V.baseMap := by
  rw [BoundedAlgHom.comp_assoc, f.comp_baseMap, pullbackMap_comp_baseMap]

/-- The bounded pushout lifts the original restriction after arbitrary coefficient change. -/
def pullbackRestriction {U V : Domain K A} (f : U ⟶ V) :
    pullback φ U ⟶ pullback φ V where
  restriction := AffinoidPushout.lift φ V.baseMap (pullback φ U).algebra
    (pullback φ U).baseMap ((pullbackMap φ U).comp f.restriction)
    (pullbackRestriction_compatible φ f)
  comp_baseMap := AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

/-- Original quotient transport commutes with the constructed changed restriction. -/
theorem pullbackRestriction_comp_pullbackMap {U V : Domain K A} (f : U ⟶ V) :
    (pullbackRestriction φ f).restriction.comp (pullbackMap φ V) =
      (pullbackMap φ U).comp f.restriction :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ (pullbackRestriction_compatible φ f)

/-- Arbitrary bounded coefficient maps induce actual full-domain pullback functors. -/
def pullbackFunctor : Domain K A ⥤ Domain K B where
  obj := pullback φ
  map := pullbackRestriction φ
  map_id U := @Subsingleton.elim (Inclusion (pullback φ U) (pullback φ U)) inferInstance _ _
  map_comp _ _ := @Subsingleton.elim (Inclusion _ _) inferInstance _ _

/-- The original quotient spectra map continuously through the transported algebra map. -/
def pullbackSpectrumMap (U : Domain K A) :
    C(BanachSpectrum (pullback φ U).algebra, BanachSpectrum U.algebra) :=
  BanachSpectrum.comapContinuous (pullbackMap φ U).toBoundedRingHom

/-- The continuous spectrum maps retain the original structural square. -/
theorem pullbackSpectrumMap_over_base (U : Domain K A)
    (x : BanachSpectrum (pullback φ U).algebra) :
    U.spectrumMap (pullbackSpectrumMap φ U x) =
      BanachSpectrum.comap φ.toBoundedRingHom ((pullback φ U).spectrumMap x) := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun h : BoundedAlgHom K A (pullback φ U).algebra => x (h a))
    (pullbackMap_comp_baseMap φ U)

namespace FiniteCover

variable {U : Domain K A}

/-- Pull back every original cover member and its actual bounded restriction. -/
def pullback (c : FiniteCover U) : FiniteCover (Domain.pullback φ U) where
  size := c.size
  obj i := Domain.pullback φ (c.obj i)
  map i := pullbackRestriction φ (c.map i)
  covers x hx := c.covers (BanachSpectrum.comap φ.toBoundedRingHom x) hx

@[simp]
theorem pullback_obj (c : FiniteCover U) (i : Fin c.size) :
    (c.pullback φ).obj i = Domain.pullback φ (c.obj i) := rfl

@[simp]
theorem pullback_map (c : FiniteCover U) (i : Fin c.size) :
    (c.pullback φ).map i = pullbackRestriction φ (c.map i) := rfl

end FiniteCover
end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
