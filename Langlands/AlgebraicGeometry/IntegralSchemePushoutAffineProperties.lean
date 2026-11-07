import Langlands.Algebra.IntegralPullbackProjection
import Mathlib.AlgebraicGeometry.Morphisms.Integral

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout

variable {R S T : CommRingCat.{u}}

/-- The map from the first spectrum into the compatible-pair spectrum is integral. -/
theorem isIntegralHom_specMap_pullbackFst (f : R ⟶ T) (g : S ⟶ T)
    (hf : Function.Surjective f) (hg : g.hom.IsIntegral) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom))) :=
  IsIntegralHom.SpecMap_iff.mpr
    (Langlands.Algebra.isIntegral_pullbackFst_of_surjective f.hom g.hom hf hg)

/-- The map from the second spectrum is a closed immersion. -/
theorem isClosedImmersion_specMap_pullbackSnd (f : R ⟶ T) (g : S ⟶ T)
    (hf : Function.Surjective f) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) :=
  IsClosedImmersion.spec_of_surjective _
    (RingHom.surjective_pullbackSnd_of_surjective f.hom g.hom hf)

/-- The actual affine cocone, bundled with its integral and closed-immersion maps. -/
noncomputable def integralAffinePushoutCocone (f : R ⟶ T) (g : S ⟶ T)
    (hf : Function.Surjective f) (hg : g.hom.IsIntegral) :
    {c : PushoutCocone (Spec.map f) (Spec.map g) //
      IsIntegralHom c.inl ∧ IsClosedImmersion c.inr} :=
  ⟨PushoutCocone.mk
    (Spec.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
    (Spec.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.pullback_comm_sq _ _))),
    isIntegralHom_specMap_pullbackFst f g hf hg,
    isClosedImmersion_specMap_pullbackSnd f g hf⟩

end Langlands.AlgebraicGeometry.IntegralSchemePushout
