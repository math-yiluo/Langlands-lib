import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Fibres of smooth geometrically connected affine schemes are domains

See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.SelfNormalizingAmbient

/-- **Fibres over fields are domains.** If `Spec C → Spec R` is smooth and geometrically
connected, then `K ⊗[R] C` is a domain for every field `K` over `R`. -/
theorem isDomain_tensor_of_smooth_geometricallyConnected {R C : Type u} [CommRing R]
    [CommRing C] [Algebra R C] (hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R C))))
    (hc : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap R C))))
    (K : Type u) [Field K] [Algebra R K] : IsDomain (K ⊗[R] C) := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap R C))
  set g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : Smooth (pullback.snd f g) := inferInstance
  have : GeometricallyConnected (pullback.snd f g) := inferInstance
  have : GeometricallyIntegral (pullback.snd f g) :=
    Langlands.AbelianScheme.smoothGeometricIntegrality K _ _ inferInstance inferInstance
  have : Subsingleton (Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : IsIntegral (pullback f g) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f g)
  have : IsIntegral (Spec (CommRingCat.of (C ⊗[R] K))) :=
    IsIntegral.of_isIso (pullbackSpecIso R C K).hom
  have : IsDomain (C ⊗[R] K) := (affine_isIntegral_iff (CommRingCat.of (C ⊗[R] K))).1 this
  exact (Algebra.TensorProduct.comm R K C).toMulEquiv.isDomain

end Langlands.GroupScheme.SelfNormalizingAmbient
