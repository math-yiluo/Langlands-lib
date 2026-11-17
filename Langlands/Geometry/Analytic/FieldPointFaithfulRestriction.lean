import Langlands.Geometry.Analytic.FieldPointFaithfulTests

/-! # Restriction and requotienting of faithful field-point tests -/

noncomputable section

universe u v uL

namespace Langlands.Analytic

open Set CategoryTheory PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace SmallAffinoidSpectrum

variable {R S : PresentedAffinoidAlgebra K}
  [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]

omit [CompleteSpace K] in
private theorem transported_comp
    {R' S' : PresentedAffinoidAlgebra K}
    (hR : R' = R) (hS : S' = S)
    (f : BoundedAlgHom K R S) (f' : BoundedAlgHom K R' S') (hf : HEq f' f)
    (χ : BoundedAlgHom K S L) :
    (hS.symm ▸ χ).comp f' = hR.symm ▸ (χ.comp f) := by
  subst R
  subst S
  cases eq_of_heq hf
  rfl

/-- The bounded pullback on the retained global charts is exactly the
original algebra map, with only the actual global-algebra transports. -/
theorem globalCharacter_comp_map_pullback
    (f : BoundedAlgHom K R S) (χ : BoundedAlgHom K S L)
    (h : (map f).baseMap '' range ((saturated S).presentation.atlas.chart (globalIndex S)) ⊆
      range ((saturated R).presentation.atlas.chart (globalIndex R))) :
    (globalCharacter S χ).comp ((map f).pullback (globalIndex S) (globalIndex R) h) =
      globalCharacter R (χ.comp f) := by
  have h0 : (strongMap f).baseMap '' range ((presentation S).atlas.chart PUnit.unit) ⊆
      range ((presentation R).atlas.chart PUnit.unit) := by
    intro x _
    exact ⟨(spectrumHomeomorph R).symm x, (spectrumHomeomorph R).apply_symm_apply x⟩
  exact transported_comp (globalAlgebra R) (globalAlgebra S) f _
    ((strongMap f).saturationExtension_pullback_original
      (strongMap_coherent f) PUnit.unit PUnit.unit h0) χ

variable [CompleteSpace L]

/-- Full field points on the actual small spectra are natural under every
bounded algebra map, including every chart restriction. -/
theorem fieldPoint_map
    (hd : DomainCompletedResidueSurjectivityStatement.{u})
    (f : BoundedAlgHom K R S) (χ : BoundedAlgHom K S L) :
    (fieldPoint S hd χ).map (map f) (saturated S).hasAllLocalDomains =
      fieldPoint R hd (χ.comp f) := by
  apply FieldPoint.boundedEval_injective hd (globalIndex R) (globalRange R)
  dsimp only
  refine (FieldPoint.map_boundedEval (fieldPoint S hd χ) (map f)
    (saturated S).hasAllLocalDomains (globalIndex R)
    ((globalRange R).symm ▸ mem_univ _) (globalIndex S)
    ((globalRange S).symm ▸ mem_univ _)
    (by rw [globalRange R]; exact subset_univ _)).trans ?_
  simp only [fieldPoint, FieldPoint.boundedEval_ofGlobalCharacter]
  exact globalCharacter_comp_map_pullback f χ _

end SmallAffinoidSpectrum

namespace PresentedAffinoidAlgebra.FaithfulCharacterQuotient

variable {R S T : PresentedAffinoidAlgebra K}
  (χ : BoundedAlgHom K R L) (ψ : BoundedAlgHom K S L)
  (φ : BoundedAlgHom K S R) (h : χ.comp φ = ψ)

/-- A bounded character-compatible algebra map descends between the
quotients by the two actual character kernels. -/
def descend : BoundedAlgHom K (algebra ψ) (algebra χ) :=
  ClosedQuotient.lift S (kernel ψ) ((map χ).comp φ) (by
    intro s hs
    apply (map_eq_zero_iff χ (φ s)).mpr
    exact (congrArg (fun c : BoundedAlgHom K S L => c s) h).trans hs)

omit [CompleteSpace K] in
@[simp]
theorem descend_map (s : S) : descend χ ψ φ h (map ψ s) = map χ (φ s) :=
  ClosedQuotient.lift_map S (kernel ψ) _ _ s

omit [CompleteSpace K] in
theorem descend_comp_map : (descend χ ψ φ h).comp (map ψ) = (map χ).comp φ :=
  BoundedAlgHom.ext (descend_map χ ψ φ h)

omit [CompleteSpace K] in
/-- The descended map preserves the exact faithful characters. -/
theorem character_comp_descend :
    (character χ).comp (descend χ ψ φ h) = character ψ := by
  apply BoundedAlgHom.ext
  intro a
  obtain ⟨s, rfl⟩ := map_surjective ψ a
  change character χ (descend χ ψ φ h (map ψ s)) = character ψ (map ψ s)
  rw [descend_map, character_map, character_map]
  exact congrArg (fun c : BoundedAlgHom K S L => c s) h

omit [CompleteSpace K] in
/-- Requotienting the restricted evaluation removes any new local kernel,
so the induced algebra map is injective even if the original map is not. -/
theorem descend_injective : Function.Injective (descend χ ψ φ h) := by
  intro a b hab
  apply character_injective ψ
  have hc := character_comp_descend χ ψ φ h
  exact (congrArg (fun c : BoundedAlgHom K (algebra ψ) L => c a) hc).symm.trans
    ((congrArg (character χ) hab).trans
      (congrArg (fun c : BoundedAlgHom K (algebra ψ) L => c b) hc))

variable [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
  [CompleteSpace L]

/-- The actual contravariant map of small saturated quotient test sources. -/
def testMap : testSource.{u, v} χ ⟶ testSource.{u, v} ψ :=
  letI := small_spectrum.{u, v} χ
  letI := small_spectrum.{u, v} ψ
  SmallAffinoidSpectrum.map (descend χ ψ φ h)

/-- Mapping the local quotient test point gives the original quotient test
point as a full field point, including every chart evaluation. -/
theorem testPoint_map (hd : DomainCompletedResidueSurjectivityStatement.{u}) :
    (testPoint χ hd).map (testMap χ ψ φ h) (testSource χ).hasAllLocalDomains =
      testPoint ψ hd := by
  let := small_spectrum.{u, v} χ
  let := small_spectrum.{u, v} ψ
  change (SmallAffinoidSpectrum.fieldPoint (algebra χ) hd (character χ)).map
    (SmallAffinoidSpectrum.map (descend χ ψ φ h)) _ =
      SmallAffinoidSpectrum.fieldPoint (algebra ψ) hd (character ψ)
  rw [SmallAffinoidSpectrum.fieldPoint_map, character_comp_descend]

end PresentedAffinoidAlgebra.FaithfulCharacterQuotient

end Langlands.Analytic
