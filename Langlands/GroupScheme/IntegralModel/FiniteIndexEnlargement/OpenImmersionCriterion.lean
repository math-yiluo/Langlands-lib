import Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AwayBijective
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # An affine open-immersion criterion from principal localizations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement

/-- If the source is covered by principal opens on which an affine scheme map
is an isomorphism onto the corresponding target opens, the map is an open
immersion. The index type need not be finite. -/
theorem isOpenImmersion_specMap_of_away_bijective
    {B A : Type u} [CommRing B] [CommRing A]
    (φ : B →+* A) {ι : Type*} (s : ι → B)
    (hspan : Ideal.span (Set.range (φ ∘ s)) = ⊤)
    (hbij : ∀ i, Function.Bijective (Localization.awayMap φ (s i))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let V : (Spec (CommRingCat.of B)).Opens :=
    ⨆ i, PrimeSpectrum.basicOpen (s i)
  have hpre : f ⁻¹ᵁ V = ⊤ := by
    dsimp only [V]
    rw [Scheme.Hom.preimage_iSup]
    change (⨆ i, PrimeSpectrum.basicOpen (φ (s i))) = ⊤
    exact PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan
  have : IsIso (f ∣_ V) :=
    Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.isIso_SpecMap_restrict_iSup_basicOpen
      (CommRingCat.ofHom φ) s hbij
  have : IsIso (f ⁻¹ᵁ V).ι := by
    rw [hpre]
    exact (Spec (CommRingCat.of A)).topIso.isIso_hom
  have he : f = inv (f ⁻¹ᵁ V).ι ≫ (f ∣_ V) ≫ V.ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  change IsOpenImmersion f
  rw [he]
  infer_instance

end Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
