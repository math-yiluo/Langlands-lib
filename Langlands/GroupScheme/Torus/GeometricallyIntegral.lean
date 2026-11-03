import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Tori over fields are geometrically integral -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The structure morphism of a torus over a field is geometrically integral. -/
theorem IsTorus.geometricallyIntegral {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    GeometricallyIntegral T.X.hom := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  have : IsIntegral (Limits.pullback T.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    (hT.baseChange (K := K)).isIntegral
  exact IsIntegral.of_isIso h.isoPullback.inv

end Langlands.GroupScheme
