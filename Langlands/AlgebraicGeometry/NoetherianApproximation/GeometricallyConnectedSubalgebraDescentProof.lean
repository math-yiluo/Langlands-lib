/-
Adapted from `P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_exists_fg_subalgebra_of_geometricallyConnected_pullback_snd.lean`
of the Anthropic Lean formalization of Fermat's Last Theorem (commit
6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the
Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the FLT namespaces `P2MW.<module>.GeomConnDesc` and `P2MW.<module>` are replaced by
`Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof`
and `Langlands.AlgebraicGeometry.NoetherianApproximation`; in `of_ring` the FLT argument through
geometric integrality of the smooth generic fibre is replaced by
`Langlands.AlgebraicGeometry.NoetherianApproximation.geometricallyConnected_of_smooth_of_geometricallyConnected_pullback_snd`;
the final theorem proves the published statement. The paired Markdown file lists the changes.
-/
import Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements
import Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedOfGenericFibre
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
import Langlands.AnthropicFLT.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates

/-!
# Descent of geometric connectedness to finitely generated subalgebras (proof)

Proves `GeometricallyConnectedSubalgebraDescentStatement`, following the FLT proof of
`AlgebraicGeometry.GeometricallyConnected.exists_fg_subalgebra_of_geometricallyConnected_pullback_snd`.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof

lemma iff_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {X X₁ Y B : Scheme.{u}}
    {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B} (sq : IsPullback π g f ι) :
    P (pullback.snd f ι) ↔ P g := by
  rw [← sq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

lemma exists_isPullback_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y}
    {f : X₁ ⟶ B} {ι : Y ⟶ B}
    (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι) :
    ∃ π' : X ⟶ pullback f κ, IsPullback π' g (pullback.snd f κ) ι' := by
  have w : π ≫ f = (g ≫ ι') ≫ κ := by rw [Category.assoc, hι]; exact sq.w
  refine ⟨pullback.lift π (g ≫ ι') w, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

lemma exists_isPullback_comp {A₀ B C : Type u} [CommRing A₀] [CommRing B] [CommRing C]
    (β : A₀ →+* B) (δ : B →+* C) {γ : A₀ →+* C} (hγ : δ.comp β = γ)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) :
    ∃ π : pullback f (Spec.map (CommRingCat.ofHom γ)) ⟶
        pullback f (Spec.map (CommRingCat.ofHom β)),
      IsPullback π (pullback.snd f (Spec.map (CommRingCat.ofHom γ)))
        (pullback.snd f (Spec.map (CommRingCat.ofHom β))) (Spec.map (CommRingCat.ofHom δ)) :=
  exists_isPullback_of_fac (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom γ))) _ _
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hγ])

lemma surjective_specMap_of_field {K L : Type u} [Field K] [Field L] (φ : K →+* L) :
    Surjective (Spec.map (CommRingCat.ofHom φ)) :=
  ⟨fun x => ⟨(default : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ x⟩⟩

scoped instance descendsAlong :
    MorphismProperty.DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u})
      @Surjective :=
  AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective

/-- Given ring maps `T → R → L` with `R` a noetherian integrally closed domain and `R → L`
injective, if the base change of `f` to `L` is geometrically connected then so is the fibre of
the base change of `f` to `T` over the image of any point `c` of `Spec R`. -/
theorem of_ring {A₀ T : Type u} [CommRing A₀] [CommRing T]
    (τ : A₀ →+* T)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [IsProper f] [Smooth f]
    (R L : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Field L]
    (φ : T →+* R) (ψ : R →+* L) (hψ : Function.Injective ψ)
    (hL : GeometricallyConnected
      (pullback.snd f (Spec.map (CommRingCat.ofHom ((ψ.comp φ).comp τ)))))
    (c : ↥(Spec (CommRingCat.of R))) (t : ↥(Spec (CommRingCat.of T)))
    (hct : (Spec.map (CommRingCat.ofHom φ)) c = t) :
    GeometricallyConnected
      ((pullback.snd f (Spec.map (CommRingCat.ofHom τ))).fiberToSpecResidueField t) := by
  classical
  let fR := pullback.snd f (Spec.map (CommRingCat.ofHom (φ.comp τ)))
  let K := FractionRing R
  let ψK : K →+* L := IsFractionRing.lift hψ
  have hψK : ψK.comp (algebraMap R K) = ψ :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hψ x
  let fK := pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap R K).comp (φ.comp τ))))
  have hfacL : (ψK.comp ((algebraMap R K).comp (φ.comp τ))) = (ψ.comp φ).comp τ := by
    rw [← RingHom.comp_assoc, hψK, RingHom.comp_assoc]
  obtain ⟨πL, sqL⟩ := exists_isPullback_comp ((algebraMap R K).comp (φ.comp τ)) ψK hfacL f
  have : GeometricallyConnected fK :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @GeometricallyConnected)
      (Q := @Surjective) sqL.flip (surjective_specMap_of_field ψK) hL
  obtain ⟨πK, sqK⟩ := exists_isPullback_comp (φ.comp τ) (algebraMap R K) rfl f
  have : GeometricallyConnected
      (pullback.snd fR (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    (iff_of_isPullback (P := @GeometricallyConnected) sqK).mpr inferInstance
  have : IsProper fR := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  have : Smooth fR := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have hR : GeometricallyConnected fR :=
    geometricallyConnected_of_smooth_of_geometricallyConnected_pullback_snd K fR
  have hRc : GeometricallyConnected (fR.fiberToSpecResidueField c) := inferInstance
  obtain ⟨πR, sqR⟩ := exists_isPullback_comp τ φ rfl f
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sqR c
  have key := MorphismProperty.of_isPullback_of_descendsAlong (P := @GeometricallyConnected)
    (Q := @Surjective) sqF.flip (surjective_specMap_of_field _) hRc
  rw [hct] at key
  exact key

/-- For an injective ring map `ι : T → A` with `T` noetherian and a point `t` of `Spec T`, there
are a noetherian integrally closed domain `R`, a field `L`, ring maps `φ : T → R`, an injective
`ψ : R → L` and `α : A → L` with `ψ ∘ φ = α ∘ ι`, and a point of `Spec R` over `t`. -/
theorem exists_ring {T A : Type u} [CommRing T] [CommRing A] [IsNoetherianRing T]
    (ι : T →+* A) (hι : Function.Injective ι) (t : ↥(Spec (CommRingCat.of T))) :
    ∃ (R L : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : IsIntegrallyClosed R) (_ : Field L) (φ : T →+* R) (ψ : R →+* L) (α : A →+* L),
      Function.Injective ψ ∧ ψ.comp φ = α.comp ι ∧
      ∃ c : ↥(Spec (CommRingCat.of R)), (Spec.map (CommRingCat.ofHom φ)) c = t := by
  classical
  obtain ⟨η, hη, hηt⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal T)) (J := t.asIdeal) bot_le
  obtain ⟨𝔮, h𝔮, h𝔮η⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hι η hη
  have := h𝔮
  have : η.IsPrime := hη.1.1
  let L := FractionRing (A ⧸ 𝔮)
  let α : A →+* L := (algebraMap (A ⧸ 𝔮) L).comp (Ideal.Quotient.mk 𝔮)
  have hαker : Ideal.comap (α.comp ι) ⊥ = η := by
    rw [← Ideal.comap_comap, ← Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective (A ⧸ 𝔮) L),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, h𝔮η]
  by_cases ht : t.asIdeal = η
  · refine ⟨L, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      α.comp ι, RingHom.id L, α, fun a b h => h, RingHom.id_comp _, default, ?_⟩
    apply PrimeSpectrum.ext
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, ht, ← hαker]
    congr 1
  · let D := T ⧸ η
    let P : Ideal D := t.asIdeal.map (Ideal.Quotient.mk η)
    have hP : P.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hηt)
    have hPcomap : P.comap (Ideal.Quotient.mk η) = t.asIdeal := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hηt]
    have hPne : P ≠ ⊥ := by
      intro h
      apply ht
      rw [← hPcomap, h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    let B := Localization.AtPrime P
    let K₀ := FractionRing D
    have hBfield : ¬ IsField B := by
      intro hF
      apply hPne
      rw [← Localization.AtPrime.under_maximalIdeal (I := P), Ideal.under_def,
        IsLocalRing.isField_iff_maximalIdeal_eq.mp hF,
        Ideal.comap_bot_of_injective _ (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)]
    obtain ⟨V, hV, hBV, hdom⟩ :=
      IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates (R := B) hBfield K₀
    have := hV
    let φ₀ : T →+* K₀ := (algebraMap B K₀).comp ((algebraMap D B).comp (Ideal.Quotient.mk η))
    let φ : T →+* ↥V := φ₀.codRestrict V.toSubring (fun x => hBV _)
    let δ : D →+* A ⧸ 𝔮 := Ideal.quotientMap 𝔮 ι (le_of_eq h𝔮η.symm)
    have hδ : Function.Injective δ := Ideal.quotientMap_injective' (le_of_eq h𝔮η)
    let κL : K₀ →+* L :=
      IsFractionRing.lift (g := (algebraMap (A ⧸ 𝔮) L).comp δ)
        ((IsFractionRing.injective (A ⧸ 𝔮) L).comp hδ)
    let ψ : ↥V →+* L := κL.comp V.subtype
    refine ⟨↥V, L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, φ, ψ,
      α, ?_, ?_, IsLocalRing.closedPoint ↥V, ?_⟩
    · exact κL.injective.comp Subtype.val_injective
    · ext x
      change κL (algebraMap B K₀ (algebraMap D B (Ideal.Quotient.mk η x))) = α (ι x)
      rw [← IsScalarTower.algebraMap_apply D B K₀, IsFractionRing.lift_algebraMap]
      change algebraMap (A ⧸ 𝔮) L (δ (Ideal.Quotient.mk η x)) =
        algebraMap (A ⧸ 𝔮) L (Ideal.Quotient.mk 𝔮 (ι x))
      rw [Ideal.quotientMap_mk]
    · apply PrimeSpectrum.ext
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, CommRingCat.hom_ofHom, ← hPcomap]
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change φ x ∈ IsLocalRing.maximalIdeal ↥V ↔ _
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      change algebraMap B K₀ (algebraMap D B (Ideal.Quotient.mk η x)) ∈ V.nonunits ↔ _
      rw [← hdom, IsLocalization.AtPrime.to_map_mem_maximal_iff B P]

end Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open GeometricallyConnectedSubalgebraDescentProof

/-- Descent of geometric connectedness to finitely generated subalgebras. -/
theorem geometricallyConnectedSubalgebraDescent :
    GeometricallyConnectedSubalgebraDescentStatement.{u} := by
  intro A₀ _ _ A _ _ X f _ _ _ s
  classical
  let T : Subalgebra A₀ A := Algebra.adjoin A₀ ↑s
  refine ⟨T, Subalgebra.fg_adjoin_finset s, Algebra.subset_adjoin, ?_⟩
  have : Algebra.FiniteType A₀ ↥T :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  have : IsNoetherianRing ↥T := Algebra.FiniteType.isNoetherianRing A₀ ↥T
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro t
  obtain ⟨R, L, _, _, _, _, _, φ, ψ, α, hψ, hcomp, c, hct⟩ :=
    exists_ring (algebraMap ↥T A) Subtype.val_injective t
  have hfac : (ψ.comp φ).comp (algebraMap A₀ ↥T) = α.comp (algebraMap A₀ A) := by
    rw [hcomp, RingHom.comp_assoc]; rfl
  obtain ⟨πA, sqA⟩ := exists_isPullback_comp (algebraMap A₀ A) α hfac.symm f
  have hL : GeometricallyConnected
      (pullback.snd f (Spec.map (CommRingCat.ofHom ((ψ.comp φ).comp (algebraMap A₀ ↥T))))) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqA inferInstance
  exact of_ring (algebraMap A₀ ↥T) f R L φ ψ hψ hL c t hct

end Langlands.AlgebraicGeometry.NoetherianApproximation
