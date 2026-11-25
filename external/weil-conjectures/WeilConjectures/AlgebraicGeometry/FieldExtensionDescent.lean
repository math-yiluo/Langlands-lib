/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.RingTheory.Etale.Descent

/-!
# Descent of properties of schemes along field extensions

We show that properness, smoothness of relative dimension `n` and geometric integrality of a
scheme over a field `k` can be checked after base change to an arbitrary field extension `K` of
`k` (blueprint `proposition-jacobian-over-ground-field--1`).

## Main statements

- `Algebra.locally_isStandardSmoothOfRelativeDimension_iff`: an algebra is locally standard smooth
  of relative dimension `n` if and only if it is smooth with Kähler differentials of constant
  rank `n`.
- `RingHom.locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat`: this
  property descends along faithfully flat ring maps.
- `AlgebraicGeometry.smoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact`,
  `AlgebraicGeometry.isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact`,
  `AlgebraicGeometry.isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact`: smoothness of
  relative dimension `n`, separatedness and properness satisfy fpqc descent.
- `AlgebraicGeometry.isIntegral_of_flat_of_surjective`: integrality descends along flat
  surjective morphisms.
- `AlgebraicGeometry.GeometricallyIntegral.of_isPullback`: geometric integrality descends along
  field extensions.
- `AlgebraicGeometry.of_isPullback_Spec_map_algebraMap`,
  `AlgebraicGeometry.connectedSpace_of_isPullback_Spec_map_algebraMap`: properties satisfying fpqc
  descent, and connectedness, descend along field extensions.
- `AlgebraicGeometry.isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback_aux`:
  the combination of the above for a base change along a field extension.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The rank of the Kähler differentials at a prime of a localization `S[1/t]` agrees with the
rank of `Ω[S⁄R]` at the corresponding prime of `S`. -/
lemma rankAtStalk_kaehlerDifferential_localizationAway [Smooth R S] (t : S)
    (q : PrimeSpectrum (Localization.Away t)) :
    Module.rankAtStalk Ω[Localization.Away t⁄R] q =
      Module.rankAtStalk Ω[S⁄R] (q.comap (algebraMap S (Localization.Away t))) := by
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S (Localization.Away t))]

/-- A standard smooth algebra with a prime `q` has relative dimension `n` if and only if its
Kähler differentials have rank `n` at `q`. -/
lemma isStandardSmoothOfRelativeDimension_iff_rankAtStalk [IsStandardSmooth R S]
    (q : PrimeSpectrum S) (n : ℕ) :
    IsStandardSmoothOfRelativeDimension n R S ↔ Module.rankAtStalk Ω[S⁄R] q = n := by
  have := q.nontrivial
  rw [IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth,
    congrFun Module.rankAtStalk_eq_finrank_of_free q, Pi.natCast_apply, Nat.cast_id]
  exact ⟨Module.finrank_eq_of_rank_eq, fun h ↦ by rw [← Module.finrank_eq_rank, h]⟩

/-- An algebra is locally standard smooth of relative dimension `n` if and only if it is smooth
and its Kähler differentials have rank `n` at every prime. -/
theorem locally_isStandardSmoothOfRelativeDimension_iff (n : ℕ) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R S) ↔
      Smooth R S ∧ ∀ p : PrimeSpectrum S, Module.rankAtStalk Ω[S⁄R] p = n := by
  constructor
  · intro h
    have hsm : Smooth R S := by
      rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
      exact RingHom.locally_of_locally
        (fun hf ↦ RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n) _ hf) h
    refine ⟨hsm, fun p ↦ ?_⟩
    obtain ⟨s, hs, H⟩ := h
    obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p.asIdeal := by
      by_contra! hcon
      exact p.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hcon))
    have H := H t ht
    rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      at H
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away t))) := by
      rw [PrimeSpectrum.localization_away_comap_range _ t]
      exact htp
    obtain ⟨q, rfl⟩ := hp
    have := IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := R)
      (S := Localization.Away t) n
    rw [← rankAtStalk_kaehlerDifferential_localizationAway,
      ← isStandardSmoothOfRelativeDimension_iff_rankAtStalk]
    exact H
  · rintro ⟨hsm, hrank⟩
    choose f hf₁ hf₂ using fun p : PrimeSpectrum S ↦
      IsSmoothAt.exists_notMem_isStandardSmooth R p.asIdeal
    refine ⟨Set.range f, ?_, ?_⟩
    · by_contra hne
      obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
      exact hf₁ ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
    · rintro - ⟨p, rfl⟩
      rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (f p)))) := by
        rw [PrimeSpectrum.localization_away_comap_range _ (f p)]
        exact hf₁ p
      obtain ⟨q, hq⟩ := hp
      have := hf₂ p
      rw [isStandardSmoothOfRelativeDimension_iff_rankAtStalk q,
        rankAtStalk_kaehlerDifferential_localizationAway, hq, hrank]

end Algebra

namespace RingHom

/-- Being locally standard smooth of relative dimension `n` descends along faithfully flat
ring maps. -/
theorem locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat (n : ℕ) :
    CodescendsAlong (Locally (IsStandardSmoothOfRelativeDimension n)) FaithfullyFlat := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hR' h
  rw [Algebra.locally_isStandardSmoothOfRelativeDimension_iff] at h ⊢
  obtain ⟨hsm, hrank⟩ := h
  have hsmS : Algebra.Smooth R S := by
    rw [← RingHom.smooth_algebraMap]
    exact Smooth.codescendsAlong_faithfullyFlat hR' (RingHom.smooth_algebraMap.mpr hsm)
  refine ⟨hsmS, fun p ↦ ?_⟩
  have : Algebra.IsPushout R R' S S' := .symm inferInstance
  have hff : (algebraMap S S').FaithfullyFlat :=
    FaithfullyFlat.isStableUnderBaseChange R R' S S' hR'
  rw [faithfullyFlat_algebraMap_iff] at hff
  obtain ⟨p', rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := S') p
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv
    (KaehlerDifferential.tensorKaehlerEquiv R R' S S'), hrank]

end RingHom

namespace AlgebraicGeometry

open MorphismProperty

/-- Being smooth of relative dimension `n` descends along fpqc morphisms. -/
instance smoothOfRelativeDimension_descendsAlong_surjective_inf_flat_inf_quasiCompact (n : ℕ) :
    DescendsAlong (@SmoothOfRelativeDimension n) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  HasRingHomProperty.descendsAlong_flat
    (RingHom.locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat n)

/-- Separatedness descends along fpqc morphisms. -/
instance isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsSeparated
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  have := IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact.{u}
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

/-- Properness descends along fpqc morphisms. -/
instance isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong @IsProper
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  rw [isProper_eq.{u}]
  infer_instance

/-- A field extension induces a faithfully flat quasi-compact morphism of spectra. -/
lemma surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap (k K : Type u) [Field k]
    [Field K] [Algebra k K] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance)
  exact ⟨⟨h.2, h.1⟩, inferInstance⟩

/-- Reducedness descends along flat surjective morphisms. -/
lemma isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    algebraize [(f.stalkMap x).hom]
    have : Module.Flat _ _ := Flat.stalkMap f x
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      .of_flat_of_isLocalHom
    exact isReduced_of_injective _
      (FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))
  exact isReduced_of_isReduced_stalk Y

/-- Integrality descends along flat surjective morphisms. -/
lemma isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsIntegral X] : IsIntegral Y := by
  have := isReduced_of_flat_of_surjective f
  have : IrreducibleSpace Y := f.surjective.irreducibleSpace f.continuous
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- Any two field extensions `Ω` and `K` of `k` embed into a common field extension `L`. -/
lemma exists_field_comp_algebraMap_eq (k Ω K : Type u) [Field k] [Field Ω] [Field K]
    [Algebra k Ω] [Algebra k K] :
    ∃ (L : Type u) (_ : Field L) (φ : Ω →+* L) (ψ : K →+* L),
      φ.comp (algebraMap k Ω) = ψ.comp (algebraMap k K) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (α := Ω ⊗[k] K)
  refine ⟨_, Ideal.Quotient.field M,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeLeft : Ω →ₐ[k] Ω ⊗[k] K),
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight : K →ₐ[k] Ω ⊗[k] K), ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc, AlgHom.comp_algebraMap, AlgHom.comp_algebraMap]

/-- Geometric integrality descends along a field extension: if `Z'` is the base change of a
`k`-scheme `Z` to a field extension `K` of `k` and `Z'` is geometrically integral over `K`, then
`Z` is geometrically integral over `k`. For a field `Ω` over `k`, choose a field `L` containing
`Ω` and `K`; then `Z_L` is integral and `Z_L ⟶ Z_Ω` is flat and surjective. -/
theorem GeometricallyIntegral.of_isPullback {k K : Type u} [Field k] [Field K] [Algebra k K]
    {Z Z' : Scheme.{u}} {z : Z ⟶ Spec (.of k)} {z' : Z' ⟶ Spec (.of K)} {q : Z' ⟶ Z}
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [GeometricallyIntegral z'] : GeometricallyIntegral z := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing]
  intro Ω _ _ Y fst snd hY
  obtain ⟨L, _, φ, ψ, hφψ⟩ := exists_field_comp_algebraMap_eq k Ω K
  let sL : Spec (.of L) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom φ)
  let tL : Spec (.of L) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom ψ)
  have hst : sL ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      tL ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    simp only [sL, tL, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφψ]
  have hout := (IsPullback.of_hasPullback snd sL).paste_horiz hY
  rw [hst] at hout
  have hW : IsPullback (h.lift (pullback.fst snd sL ≫ fst) (pullback.snd snd sL ≫ tL)
      (by simpa using hout.w))
      (pullback.snd snd sL) z' tL :=
    IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ _) h
  have : IsIntegral (pullback snd sL) :=
    GeometricallyIntegral.geometrically_isIntegral (f := z') tL _ _ hW
  let := φ.toAlgebra
  obtain ⟨⟨hs, hf⟩, -⟩ := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap Ω L
  have : Flat sL := hf
  have : Surjective sL := hs
  exact isIntegral_of_flat_of_surjective (pullback.fst snd sL)

/-- A property of morphisms satisfying fpqc descent descends along a field extension: if the base
change `Z'` of a `k`-scheme `Z` to a field extension `K` of `k` has it over `K`, then `Z` has it
over `k`. This applies to being locally of finite type, smooth or proper, among others (blueprint
`proposition-jacobian-over-ground-field--1`). -/
theorem of_isPullback_Spec_map_algebraMap (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] {k K : Type u} [Field k] [Field K]
    [Algebra k K] {Z Z' : Scheme.{u}} {z : Z ⟶ Spec (.of k)} {z' : Z' ⟶ Spec (.of K)}
    {q : Z' ⟶ Z} (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hz' : P z') : P z :=
  of_isPullback_of_descendsAlong h.flip
    (surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap k K) hz'

/-- Connectedness descends along a field extension: if the base change `Z'` of a `k`-scheme `Z`
to a field extension `K` of `k` is connected, then so is `Z`, the projection `Z' ⟶ Z` being
surjective (blueprint `proposition-jacobian-over-ground-field--1`). -/
theorem connectedSpace_of_isPullback_Spec_map_algebraMap {k K : Type u} [Field k] [Field K]
    [Algebra k K] {Z Z' : Scheme.{u}} {z : Z ⟶ Spec (.of k)} {z' : Z' ⟶ Spec (.of K)}
    {q : Z' ⟶ Z} (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace Z'] : ConnectedSpace Z := by
  obtain ⟨⟨hs, -⟩, -⟩ := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap k K
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective) h.flip hs
  exact q.surjective.connectedSpace q.continuous


/-- **Properties of morphisms are local in the fpqc topology on the target.** Let `k ⊆ K` be a
field extension and let `Z` be a scheme over `k` whose base change `Z'` to `K` is proper, smooth
of relative dimension `n` and geometrically integral over `K`. Then so is `Z` over `k`.

(blueprint: `proposition-jacobian-over-ground-field--1`) -/
theorem isProper_smoothOfRelativeDimension_geometricallyIntegral_of_isPullback_aux {k K : Type u}
    [Field k] [Field K] [Algebra k K] {Z Z' : Scheme.{u}} (z : Z ⟶ Spec (.of k))
    (z' : Z' ⟶ Spec (.of K)) (q : Z' ⟶ Z)
    (h : IsPullback q z' z (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (n : ℕ)
    [IsProper z'] [SmoothOfRelativeDimension n z'] [GeometricallyIntegral z'] :
    IsProper z ∧ SmoothOfRelativeDimension n z ∧ GeometricallyIntegral z := by
  have hK := surjective_inf_flat_inf_quasiCompact_Spec_map_algebraMap k K
  exact ⟨of_isPullback_of_descendsAlong (P := @IsProper) h.flip hK ‹_›,
    of_isPullback_of_descendsAlong (P := @SmoothOfRelativeDimension n) h.flip hK ‹_›,
    GeometricallyIntegral.of_isPullback h⟩

end AlgebraicGeometry
