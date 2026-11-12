import Langlands.AlgebraicGeometry.AlgebraicSpace.LimitRepresentedPullback
import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreProductFinitePresentation

/-! # Eventual target atlases and conditional descent of represented properties -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An actual target-atlas square whose two scheme corners are finitely
presented over the base. -/
structure FinitePresentationSchemeTargetAtlas {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  atlas : SchemeTargetAtlas f
  sourceLocallyOfFinitePresentation : LocallyOfFinitePresentation atlas.source.hom
  sourceQuasiCompact : QuasiCompact atlas.source.hom
  sourceQuasiSeparated : QuasiSeparated atlas.source.hom
  targetLocallyOfFinitePresentation : LocallyOfFinitePresentation atlas.target.hom
  targetQuasiCompact : QuasiCompact atlas.target.hom
  targetQuasiSeparated : QuasiSeparated atlas.target.hom

/-- A morphism represented at the affine limit has a later actual scheme
target-atlas square with finite-presentation corners, under model uniqueness. -/
theorem exists_finitePresentation_schemeTargetAtlas_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)}
    (hXqs : IsQuasiSeparated X)
    (hXfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y)
    (hYfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (f : X ⟶ Y)
    (hf : IsRepresentableMorphism (hom (baseChangeMap (c.π.app i) f))) :
    ∃ (j : I) (r : j ⟶ i),
      Nonempty (FinitePresentationSchemeTargetAtlas (baseChangeMap (D.map r) f)) := by
  obtain ⟨V, b, hVa, hb, hs, hVlfp⟩ :=
    exists_affine_finitePresentation_atlas Y hYfp
  have : IsAffine V.left := hVa
  have : LocallyOfFinitePresentation V.hom := hVlfp
  let b' : (schemeToSpace (D.obj i)).obj V ⟶ Y := homMk b
  obtain ⟨hWqs, hWfp⟩ := FibreProduct.finitePresentation f b'
    hXqs (isQuasiSeparated_schemeToSpace V) hYqs
    hXfp (HasAtlasProperty.of_scheme V ⟨inferInstance, inferInstance⟩) hYfp
  obtain ⟨j, r, a, hAlfp, hAqc, hAqs, hBlfp, hBqc, hBqs⟩ :=
    exists_schemeTargetAtlas_of_modelUniqueness huni D c hc i b hb hs
      (hom (FibreProduct.fst f b')) (hom (FibreProduct.snd f b'))
      (FibreProduct.isPullback_presheaf f b') hWqs hWfp hf
  exact ⟨j, r, ⟨⟨a, hAlfp, hAqc, hAqs, hBlfp, hBqc, hBqs⟩⟩⟩

/-- Scheme descent and effective descent from one target atlas give the full
space limit equivalence, conditional on model uniqueness. All scheme
finiteness hypotheses and original-stage representability are discharged. -/
theorem spaceLimitRelativePropertyDescent_of_modelUniqueness
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (huni : SpaceLimitModelUniqueness.{u})
    (heff : EtaleAtlasPropertyEffectivity P)
    (hP : SchemeStructuralPropertyDescent P) :
    SpaceLimitPropertyDescends.{u} (fun {S} {_X _Y} f =>
      (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) (hom f)) := by
  intro I _ _ D _ c hc i X Y hXqs hXfp hYqs hYfp f
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  constructor
  · intro hf
    obtain ⟨j, r, ⟨a⟩⟩ :=
      exists_finitePresentation_schemeTargetAtlas_of_modelUniqueness
        huni D c hc i hXqs hXfp hYqs hYfp f hf.1
    let := a.sourceLocallyOfFinitePresentation
    let := a.sourceQuasiCompact
    let := a.sourceQuasiSeparated
    let := a.targetLocallyOfFinitePresentation
    let := a.targetQuasiCompact
    let := a.targetQuasiSeparated
    have hfj := (relative_baseChangeMap_comp_iff (D.map r) (c.π.app j)
      (c.π.app i) P (c.w r) f).mpr hf
    obtain ⟨k, s, hk⟩ :=
      (SchemeTargetAtlas.property_limit_iff P heff hP D c hc j a.atlas).mp hfj
    refine ⟨k, s ≫ r, ?_⟩
    exact (relative_baseChangeMap_comp_iff (D.map r) (D.map s)
      (D.map (s ≫ r)) P (D.map_comp s r).symm f).mp hk
  · rintro ⟨j, r, hj⟩
    exact relative_baseChangeMap_of_stage D c r f P hj

/-- Closed-immersion descent with only the two displayed foundational inputs. -/
theorem spaceLimitClosedImmersionDescent_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    (heff : EtaleAtlasPropertyEffectivity.{u} @_root_.AlgebraicGeometry.IsClosedImmersion) :
    SpaceLimitPropertyDescends.{u} (fun f => IsClosedImmersion (hom f)) :=
  spaceLimitRelativePropertyDescent_of_modelUniqueness
    @_root_.AlgebraicGeometry.IsClosedImmersion huni heff
    closedImmersion_schemeStructuralPropertyDescent

/-- Affine-morphism descent with only the two displayed foundational inputs. -/
theorem spaceLimitAffineDescent_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    (heff : EtaleAtlasPropertyEffectivity.{u} @IsAffineHom) :
    SpaceLimitPropertyDescends.{u} (fun f => IsAffineMorphism (hom f)) :=
  spaceLimitRelativePropertyDescent_of_modelUniqueness
    @IsAffineHom huni heff affine_schemeStructuralPropertyDescent

/-- Open-immersion descent with only the two displayed foundational inputs. -/
theorem spaceLimitOpenImmersionDescent_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    (heff : EtaleAtlasPropertyEffectivity.{u} @_root_.AlgebraicGeometry.IsOpenImmersion) :
    SpaceLimitPropertyDescends.{u} (fun f => IsOpenImmersion (hom f)) :=
  spaceLimitRelativePropertyDescent_of_modelUniqueness
    @_root_.AlgebraicGeometry.IsOpenImmersion huni heff
    openImmersion_schemeStructuralPropertyDescent

/-- Finite-morphism descent with only the two displayed foundational inputs. -/
theorem spaceLimitFiniteDescent_of_modelUniqueness
    (huni : SpaceLimitModelUniqueness.{u})
    (heff : EtaleAtlasPropertyEffectivity.{u} @_root_.AlgebraicGeometry.IsFinite) :
    SpaceLimitPropertyDescends.{u} (fun f => IsFinite (hom f)) :=
  spaceLimitRelativePropertyDescent_of_modelUniqueness
    @_root_.AlgebraicGeometry.IsFinite huni heff finite_schemeStructuralPropertyDescent

end Langlands.AlgebraicGeometry.AlgebraicSpace
