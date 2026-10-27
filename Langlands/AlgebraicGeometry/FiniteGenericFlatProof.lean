import Langlands.AlgebraicGeometry.FiniteGenericFlatStatement
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Generic flatness for finite morphisms

Finite-presentation descent gives a free localization of the finite affine
coordinate algebra. Basic-open localization and restriction isomorphisms then
prove the published generic-flatness statement.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace TensorProduct

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

private lemma exists_flat_away {R B : Type u} [CommRing R] [CommRing B]
    [IsDomain R] [IsNoetherianRing R] (φ : R →+* B) (hφ : φ.Finite) :
    ∃ r : R, r ≠ 0 ∧ (Localization.awayMap φ r).Flat := by
  algebraize [φ]
  have : Module.FinitePresentation R B := Module.finitePresentation_of_finite R B
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R) (TensorProduct.mk R (FractionRing R) B 1) (FractionRing R)
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, ?_⟩
  let Br := Localization.Away (algebraMap R B r)
  let : Algebra (Localization.Away r) Br :=
    localizationAlgebra (.powers r) B
  have : IsScalarTower R (Localization.Away r) Br :=
    isScalarTower_localizationAlgebra (.powers r) B
  let e : LocalizedModule.Away r B ≃ₗ[Localization.Away r] Br :=
    (IsLocalizedModule.linearEquiv (.powers r) (LocalizedModule.mkLinearMap (.powers r) B)
      (IsScalarTower.toAlgHom R B Br).toLinearMap).extendScalarsOfIsLocalization
        (.powers r) (Localization.Away r)
  have : Module.Free (Localization.Away r) Br := Module.Free.of_equiv e
  have hflat : (algebraMap (Localization.Away r) Br).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hflat

set_option backward.isDefEq.respectTransparency false in
private lemma exists_flat_restrict_of_affine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [IsIntegral Y] [IsLocallyNoetherian Y] [IsFinite f] :
    ∃ U : Y.Opens, Set.Nonempty (U : Set Y) ∧ Flat (f ∣_ U) := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  obtain ⟨r, hr, hflat⟩ := exists_flat_away f.appTop.hom f.finite_appTop
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · exact (Opens.ne_bot_iff_nonempty _).mp (by simpa using hr)
  · have hpre : IsAffineOpen (f ⁻¹ᵁ (⊤ : Y.Opens)) :=
      (isAffineOpen_top Y).preimage f
    have hmap : (f.app (Y.basicOpen r)).hom.Flat := by
      rw [(isAffineOpen_top Y).app_basicOpen_eq_away_map f hpre r,
        CommRingCat.hom_comp, RingHom.Flat.respectsIso.cancel_right_isIso]
      exact (RingHom.Flat.respectsIso.isLocalization_away_iff
        Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.appTop r)) f.appTop.hom r).mp hflat
    have : IsAffine (f ⁻¹ᵁ Y.basicOpen r).toScheme :=
      ((isAffineOpen_top Y).basicOpen r).preimage f
    apply (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
    rw [morphismRestrict_appTop, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    change (f.app ((Y.basicOpen r).ι ''ᵁ ⊤)).hom.Flat
    rw [Scheme.Opens.ι_image_top]
    exact hmap

set_option backward.isDefEq.respectTransparency false in
/-- A finite morphism to an integral locally Noetherian scheme is flat over
some nonempty open subset of the target. -/
theorem finiteGenericFlat : FiniteGenericFlatStatement.{u} := by
  intro X Y f hY hN hf
  have : IsIntegral Y := hY
  have : IsLocallyNoetherian Y := hN
  have : IsFinite f := hf
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨U, hU, hyU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
  have : Nonempty U.toScheme := ⟨⟨y, hyU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  obtain ⟨V, hV, hflat⟩ := exists_flat_restrict_of_affine (f ∣_ U)
  refine ⟨U.ι ''ᵁ V, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hV
    exact ⟨U.ι v, ⟨v, hv, rfl⟩⟩
  · exact (MorphismProperty.arrow_mk_iso_iff @Flat.{u}
      (morphismRestrictRestrict f U V)).mp hflat

end Langlands.AlgebraicGeometry
