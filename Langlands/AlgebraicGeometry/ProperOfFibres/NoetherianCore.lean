import Mathlib
import Langlands.AlgebraicGeometry.ProperOfFibres.LocalZariski
import Langlands.AlgebraicGeometry.ProperOfFibres.MonoNormalization
import Langlands.AlgebraicGeometry.ClosedFibreOpenIntegrality
import Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Properness over a localization of a normal finitely generated `ℤ`-domain -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProperOfFibres

/-- The zero ideal lies in the image of the spectrum of a field under an injective ring map. -/
theorem bot_mem_range_SpecMap_of_injective {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsLocalRing.closedPoint K, ?_⟩
  change PrimeSpectrum.comap φ (IsLocalRing.closedPoint K) = _
  ext1
  rw [PrimeSpectrum.comap_asIdeal]
  have : (IsLocalRing.closedPoint K).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [this]
  exact Ideal.comap_bot_of_injective _ hφ

/-- A flat scheme over the spectrum of a domain is irreducible as soon as some irreducible
scheme maps onto its generic fibre. -/
theorem irreducibleSpace_of_flat {R : Type u} [CommRing R] [IsDomain R] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] (e : Z ⟶ X) [IrreducibleSpace Z]
    (he : ∀ x, f x = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) → x ∈ Set.range e) :
    IrreducibleSpace X := by
  have hirr : IsIrreducible (Set.range e) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Z).image _ e.continuous.continuousOn
  have hdense : closure (Set.range e) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    have hy : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ f x :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp bot_le)
    obtain ⟨x', hx'x, hx'⟩ := Flat.generalizingMap f hy
    exact closure_mono (Set.singleton_subset_iff.mpr (he x' hx')) hx'x.mem_closure
  have h := hirr.closure
  rw [hdense] at h
  exact (irreducibleSpace_def X).mpr h

/-- Over the spectrum of a finitely generated `ℤ`-algebra, the rings of sections of a scheme
locally of finite type over affine opens are finitely generated `ℤ`-algebras. -/
theorem finiteType_int_of_locallyOfFiniteType {R : Type u} [CommRing R] [Algebra.FiniteType ℤ R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType g]
    (U : Y.Opens) (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(Y, U) := by
  have h1 : (g.appLE ⊤ U (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨U, hU⟩ (by simp)
  have h2 : (algebraMap ℤ Γ(Spec (CommRingCat.of R), ⊤)).FiniteType := by
    have hR : (algebraMap ℤ R).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
    have he : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    rw [show algebraMap ℤ Γ(Spec (CommRingCat.of R), ⊤) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap ℤ R) from
        Subsingleton.elim _ _]
    exact he.comp hR
  rw [← RingHom.finiteType_algebraMap,
    show algebraMap ℤ Γ(Y, U) = (g.appLE ⊤ U (by simp)).hom.comp
      (algebraMap ℤ Γ(Spec (CommRingCat.of R), ⊤)) from Subsingleton.elim _ _]
  exact h1.comp h2

section

variable {N : Type u} [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra.FiniteType ℤ N]
  (p : Ideal N) [p.IsPrime] (B : Type u) [CommRing B] [IsLocalRing B] [Algebra N B]
  [IsLocalization.AtPrime B p] (K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]

include p in
/-- **Properness over a localization of a normal finitely generated `ℤ`-domain.** Let `N` be
a normal domain of finite type over `ℤ`, let `B` be its localization at a prime `p`, and let
`K` be the fraction field of `B`. Let `f : X ⟶ Spec N` be smooth and quasi-compact, and let
`j : X ⟶ Y` be a monomorphism over `Spec N` into a proper `N`-scheme. If the generic fibre of
`X_B` is proper and geometrically connected over `K` and the closed fibre of `X_B` is proper
and nonempty, then `X_B ⟶ Spec B` is proper. -/
theorem isProper_pullback_snd_of_mono
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of N)) [Smooth f] [QuasiCompact f]
    (g : Y ⟶ Spec (CommRingCat.of N)) [IsProper g] (j : X ⟶ Y) [Mono j] (hfac : j ≫ g = f)
    [IsProper (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap N B))))
      (Spec.map (CommRingCat.ofHom (algebraMap B K))))]
    [GeometricallyConnected
      (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap N B))))
        (Spec.map (CommRingCat.ofHom (algebraMap B K))))]
    [IsProper (pullback.snd (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap N B))))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))))]
    [Nonempty ↥(pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap N B))))
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))))] :
    IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap N B)))) := by
  set σ := Spec.map (CommRingCat.ofHom (algebraMap N B)) with hσ
  set φK := Spec.map (CommRingCat.ofHom (algebraMap B K)) with hφK
  set fB := pullback.snd f σ with hfB
  -- ring-theoretic input
  have : IsNoetherianRing N := Algebra.FiniteType.isNoetherianRing ℤ N
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B p.primeCompl_le_nonZeroDivisors
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hNB : Function.Injective (algebraMap N B) :=
    IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  -- finiteness properties of `j`
  have : LocallyOfFiniteType j := by
    have : LocallyOfFiniteType (j ≫ g) := by rw [hfac]; infer_instance
    exact locallyOfFiniteType_of_comp j g
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ g) := by rw [hfac]; infer_instance
    exact QuasiCompact.of_comp j g
  -- `X` is integral
  have : GeometricallyReduced f := SmoothReducedProof.geometricallyReduced_of_smooth f
  have : IsReduced X := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  have : GeometricallyIntegral (pullback.snd fB φK) :=
    geometricallyIntegral_of_smooth_geometricallyConnected _
  have : IsIntegral (pullback fB φK) := GeometricallyIntegral.isIntegral_of_subsingleton
    (pullback.snd fB φK)
  have : IrreducibleSpace X := by
    refine irreducibleSpace_of_flat f (pullback.fst fB φK ≫ pullback.fst f σ) fun x hx ↦ ?_
    have hcomp : φK ≫ σ =
        Spec.map (CommRingCat.ofHom ((algebraMap B K).comp (algebraMap N B))) := by
      rw [hφK, hσ, ← Spec.map_comp]
      rfl
    have hxr : x ∈ Set.range (pullback.fst f (φK ≫ σ)) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx, hcomp]
      exact bot_mem_range_SpecMap_of_injective _
        ((IsFractionRing.injective B K).comp hNB)
    obtain ⟨z, rfl⟩ := hxr
    refine ⟨(pullbackLeftPullbackSndIso f σ φK).inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullbackLeftPullbackSndIso_inv_fst]
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  -- the relative normalization of `Y` in `X`
  have : IsFinite j.fromNormalization :=
    isFinite_fromNormalization j (finiteType_int_of_locallyOfFiniteType g)
  let w := j.fromNormalization ≫ g
  have : IsProper w := inferInstance
  let ι := j.toNormalization
  have : IsOpenImmersion ι := inferInstance
  have hιw : ι ≫ w = f := by
    simp only [ι, w, Scheme.Hom.toNormalization_fromNormalization_assoc, hfac]
  -- base change to `B`
  have s : IsPullback (pullback.snd f σ) (pullback.fst f σ) σ (ι ≫ w) := by
    rw [hιw]
    exact (IsPullback.of_hasPullback f σ).flip
  have t : IsPullback (pullback.snd w σ) (pullback.fst w σ) σ w :=
    (IsPullback.of_hasPullback w σ).flip
  have hsq := IsPullback.of_right' s t
  set ιB := t.lift (pullback.snd f σ) (pullback.fst f σ ≫ ι)
    (by rw [s.w, Category.assoc]) with hιB
  have : IsOpenImmersion ιB :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip ‹IsOpenImmersion ι›
  have hfacB : ιB ≫ pullback.snd w σ = fB := t.lift_fst _ _ _
  have : IsIso (pullback.snd fB φK).appTop :=
    fieldSmoothProperConnectedGlobalFunctions K _ (pullback.snd fB φK) inferInstance
      inferInstance inferInstance
  have hK : Function.Bijective (pullback.snd fB φK).appTop :=
    ConcreteCategory.bijective_of_isIso _
  exact isProper_of_isOpenImmersion K fB ιB (pullback.snd w σ) hfacB hK

end

end Langlands.AlgebraicGeometry.ProperOfFibres
