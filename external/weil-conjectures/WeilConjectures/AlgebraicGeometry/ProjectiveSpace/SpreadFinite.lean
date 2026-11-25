/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Spreading out finite algebras from the generic fibre

Let `A` be a Noetherian domain with fraction field `K` and `T ⟶ Spec A` projective. A finite
morphism `Y₀ ⟶ T_K` to the generic fibre, i.e. a finite coherent `𝒪_{T_K}`-algebra, is the
generic fibre of a finite morphism `Y ⟶ T_U` over a nonempty open `U` of `Spec A`; finitely many
of them (the factors of a finite product decomposition) can be spread out simultaneously.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_spread`

## Proof

Instead of clearing denominators chart by chart, we write `Spec K` as the cofiltered limit of
the schemes `Spec A[1/a]`, `a ≠ 0`, so that `T_K` is the limit of the `T_{A[1/a]}`. The finite,
hence finitely presented, morphisms `gₐ` descend to a stage
(`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`), and the descended
morphisms become finite at a later stage
(`AlgebraicGeometry.Scheme.exists_isFinite_pullback_snd_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

/-- **Spreading a finite algebra from the generic fibre.** Let `A` be a Noetherian domain with
fraction field `K`, `η: Spec K ⟶ Spec A` the generic point,
and `f: T ⟶ Spec A` projective (`f = π ∘ i` for a closed immersion `i: T ⟶ ℙ(n; Spec A)`).
Let `gₐ: Y₀ₐ ⟶ T_K = T ×_{Spec A} Spec K`, for `a` in a finite type `ι`, be finite morphisms
(the factors of a finite product decomposition of a finite coherent `𝒪_{T_K}`-algebra). There is
a nonempty open `U` of `Spec A` and finite morphisms `g'ₐ: Yₐ ⟶ f⁻¹(U)` whose base changes
along `T_K ⟶ T` are the `gₐ`. -/
theorem exists_isFinite_spread {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A)) {n : Type u} [Finite n]
    (i : T ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i]
    (hi : i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A) = f) {ι : Type u} [Finite ι]
    (Y₀ : ι → Scheme.{u})
    (g : ∀ a, Y₀ a ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))))
    [∀ a, IsFinite (g a)] :
    ∃ (U : (Spec (.of A)).Opens) (_ : U ≠ ⊥) (Y : ι → Scheme.{u})
      (g' : ∀ a, Y a ⟶ (f ⁻¹ᵁ U).toScheme) (_ : ∀ a, IsFinite (g' a))
      (e : ∀ a, Y₀ a ≅ pullback (g' a ≫ (f ⁻¹ᵁ U).ι)
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))))),
      ∀ a, (e a).hom ≫ pullback.snd _ _ = g a := by
  classical
  have := Fintype.ofFinite ι
  have : LocallyOfFiniteType f := by rw [← hi]; infer_instance
  have : QuasiCompact f := by rw [← hi]; infer_instance
  have : QuasiSeparated f := by rw [← hi]; infer_instance
  -- `K` as the colimit of the localizations `A[1/a]`, `a ≠ 0`
  let K := FractionRing A
  have : IsLocalization (⊥ : Ideal A).primeCompl K := by
    rw [Ideal.primeCompl_bot]; infer_instance
  let eK : CommRingCat.of (Localization.AtPrime (⊥ : Ideal A)) ≅ CommRingCat.of K :=
    (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A))
      K).toRingEquiv.toCommRingCatIso
  let cR := (CommRingCat.awayProdCocone (⊥ : Ideal A)).extend eK.hom
  have hR : IsColimit cR := (CommRingCat.isColimitAwayProdCocone _).ofIsoColimit
    (Cocone.ext eK fun _ ↦ rfl)
  have hRA (s : Finset (⊥ : Ideal A).primeCompl) :
      CommRingCat.ofHom (algebraMap A (CommRingCat.AwayProd ⊥ s)) ≫ cR.ι.app s =
        CommRingCat.ofHom (algebraMap A K) := by
    change _ ≫ _ ≫ eK.hom = _
    rw [CommRingCat.ofHom_algebraMap_comp_awayProdCocone_ι_app_assoc]
    ext x
    exact (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl
      (Localization.AtPrime (⊥ : Ideal A)) K).commutes x
  -- `Spec K` as the limit of the `Spec A[1/a]`, and `T_K` as the limit of the `T_{A[1/a]}`
  let I := (Finset (⊥ : Ideal A).primeCompl)ᵒᵖ
  let D₀ : I ⥤ Scheme.{u} := (CommRingCat.awayProdDiagram (⊥ : Ideal A)).op ⋙ Scheme.Spec
  let c₀ : Cone D₀ := Scheme.Spec.mapCone cR.op
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec hR.op
  let q (s : I) : D₀.obj s ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (CommRingCat.AwayProd ⊥ s.unop)))
  have hq {s s' : I} (u : s ⟶ s') : D₀.map u ≫ q s' = q s := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.ofHom_algebraMap_comp_awayProdDiagram_map _ u.unop)
  let q₀ : Spec (.of K) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A K))
  have hq₀ (s : I) : c₀.π.app s ≫ q s = q₀ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (hRA s.unop)
  have : IsConnected I := IsCofiltered.isConnected I
  let D := baseChangeOverFamilyDiagram D₀ q hq f
  let c := baseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f
  have hc : IsLimit c := isLimitBaseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f hc₀
  have : ∀ {s s' : I} (u : s ⟶ s'), IsAffineHom (D₀.map u) := fun u ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have (s : I) : IsAffine (D₀.obj s) := inferInstanceAs (IsAffine (Spec _))
  have (s : I) : CompactSpace (D.obj s) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (q s))
  have (s : I) : QuasiSeparatedSpace (D.obj s) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (q s))
  have : IsLocallyNoetherian c.pt :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f q₀)
  -- descend each `gₐ` to a finite morphism over some stage
  let Good (a : ι) (s : I) : Prop := ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj s) (h : Y₀ a ⟶ Y),
    IsFinite p ∧ IsPullback h (g a) p (c.π.app s)
  have hmono (a : ι) {s s' : I} (u : s' ⟶ s) (h : Good a s) : Good a s' := by
    obtain ⟨Y, p, h, hp, H⟩ := h
    exact ⟨_, pullback.snd p (D.map u), isPullbackLift D c u H, inferInstance,
      isPullback_isPullbackLift u H⟩
  have hex (a : ι) : ∃ s, Good a s := by
    have : LocallyOfFinitePresentation (g a) :=
      LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
    obtain ⟨s, Y, p, _, _, _, h, H⟩ := Scheme.exists_isPullback_of_finitePresentation hc (g a)
    have : IsFinite (pullback.snd p (c.π.app s)) := by
      rw [← H.isoPullback_inv_snd]
      infer_instance
    obtain ⟨s', u, hu⟩ := Scheme.exists_isFinite_pullback_snd_of_isLimit hc p
    exact ⟨s', _, pullback.snd p (D.map u), isPullbackLift D c u H, hu,
      isPullback_isPullbackLift u H⟩
  choose s₀ hs₀ using hex
  obtain ⟨s, hs⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image s₀)
  have hgood (a : ι) : Good a s :=
    hmono a (hs (Finset.mem_image_of_mem s₀ (Finset.mem_univ a))).some (hs₀ a)
  choose Y p h hp H using hgood
  -- the stage `s` is the preimage of the basic open of the product of the elements of `s`
  let r : A := ∏ x ∈ s.unop, (x : A)
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen r
  have hU : U ≠ ⊥ := by
    intro hU
    have hr : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ hx ↦ x.2 (by simp [hx])
    exact hr ((PrimeSpectrum.basicOpen_eq_bot_iff r).mp hU).eq_zero
  have : IsOpenImmersion (q s) := IsOpenImmersion.of_isLocalization r
  have hrange : Set.range (pullback.fst f (q s)) = Set.range (f ⁻¹ᵁ U).ι := by
    rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
    congr 2
    ext1
    change Set.range (q s) = _
    exact PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
  let e : D.obj s ≅ (f ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst f (q s)) (f ⁻¹ᵁ U).ι hrange
  have hsq (a : ι) : IsPullback (h a) (g a) ((p a ≫ e.hom) ≫ (f ⁻¹ᵁ U).ι)
      (pullback.fst f q₀) := by
    have e1 : (p a ≫ e.hom) ≫ (f ⁻¹ᵁ U).ι = p a ≫ pullback.fst f (q s) := by
      simp [e]
    have e2 : pullback.fst f q₀ = c.π.app s ≫ pullback.fst f (q s) := by
      simp [c]
    rw [e1, e2, IsPullback.comp_mono_iff]
    exact H a
  exact ⟨U, hU, Y, fun a ↦ p a ≫ e.hom, fun a ↦ inferInstance,
    fun a ↦ (hsq a).isoPullback, fun a ↦ (hsq a).isoPullback_hom_snd⟩

end AlgebraicGeometry.ProjectiveSpace
