/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionDerived
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.MumfordComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.RfPerfect

/-!
# Mumford's complex over a Noetherian affine base

Let `p : Y ⟶ S` be proper of finite presentation over an affine scheme `S` whose ring of global
sections `A = Γ(S, ⊤)` is Noetherian, and `𝒢` an `𝒪_Y`-module of finite presentation, flat over
`S`. Every point of `S` has a basic open neighbourhood `D(a)` over which there is a bounded
complex `P` of finite free `𝒪_{D(a)}`-modules whose pullback along every `g : T' ⟶ D(a)` computes
the higher direct images of the base change of `𝒢`
(`exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing`).

The Čech complex `Č(U, 𝒢)` of a finite affine cover is quasi-isomorphic, compatibly with every
base change, to its truncation, a perfect complex of flat `A`-modules; locally on `Spec A` it is
therefore modelled by a complex of finite free modules
(`CochainComplex.exists_free_away_quasiIso_baseChange`), and the complex of free sheaves with the
same matrices computes the higher direct images after any base change
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_freeComplexOfBasis_iso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-compact scheme has a finite nonempty cover by affine opens. -/
lemma exists_finite_nonempty_affine_cover (Z : Scheme.{u}) [CompactSpace Z] :
    ∃ (ι : Type u) (_ : Finite ι) (_ : Nonempty ι) (U : ι → Z.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ := by
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : Z.Opens))).mp (by simpa using isCompact_univ)
  have : Finite s := hs
  refine ⟨Option s, inferInstance, inferInstance, fun i ↦ i.elim ⊥ fun a ↦ a.1.1, ?_, ?_⟩
  · rintro (_ | a)
    exacts [isAffineOpen_bot Z, a.1.2]
  · refine le_antisymm le_top ?_
    rw [hsU]
    exact iSup₂_le fun a ha ↦ le_iSup_of_le (some ⟨a, ha⟩) le_rfl

/-- The finite free complexes produced by
`AlgebraicGeometry.Scheme.Modules.freeComplexOfBasis` from bases indexed by `ULift (Fin r)`. -/
lemma isFiniteFreeComplex_freeComplexOfBasis {Z : Scheme.{u}} {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) {r : ℤ → ℕ}
    (b : ∀ n, Module.Basis (ULift.{u} (Fin (r n))) R (P.X n)) (τ : R →+* Γ(Z, ⊤)) (d : ℕ)
    (hr : ∀ n, n < 0 ∨ (d : ℤ) < n → r n = 0) :
    IsFiniteFreeComplex (freeComplexOfBasis P b τ) d where
  isStrictlyGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have : IsEmpty (ULift.{u} (Fin (r i))) := by rw [hr i (Or.inl hi)]; infer_instance
    exact isZero_free_of_isEmpty _
  isStrictlyLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have : IsEmpty (ULift.{u} (Fin (r i))) := by rw [hr i (Or.inr hi)]; infer_instance
    exact isZero_free_of_isEmpty _
  exists_iso_free n := ⟨r n, ⟨Iso.refl _⟩⟩

/-- **Mumford's complex over a Noetherian affine base**, in the derived category. Let
`p : Y ⟶ S` be proper of finite presentation over an affine scheme `S` with Noetherian ring of
global sections, and `𝒢` an `𝒪_Y`-module of finite presentation which is flat over `S`. Every
point `s₀` of `S` lies in a basic open `D(a)` over which there is a bounded complex `P` of finite
free modules such that for every `g : T' ⟶ D(a)` and every cartesian square over `g ≫ ι` there
is an isomorphism `g^* P ≅ R p'_* g'^* 𝒢` in `D(𝒪_{T'})`.

The Čech complex `Č(U, 𝒢)` of a finite affine cover is, over `Spec A`, quasi-isomorphic to a
perfect complex of flat `A`-modules, which near `s₀` is modelled by a complex `P` of finite free
modules compatibly with every base change (`CochainComplex.exists_free_away_quasiIso_baseChange`).
After base change along `g`, the complex of free sheaves with the matrices of `P` maps
quasi-isomorphically to `p'_* Č(g'⁻¹ U, g'^* 𝒢)`
(`AlgebraicGeometry.Scheme.Modules.quasiIso_mumfordFreeHom`), which is `R p'_* g'^* 𝒢`
(`AlgebraicGeometry.Scheme.Modules.derivedPushforwardSingleIsoCechResolution`). The per-degree
form is `exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing {Y S : Scheme.{u}}
    [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] (p : Y ⟶ S) [IsProper p]
    [LocallyOfFinitePresentation p] (𝒢 : Y.Modules) [𝒢.IsFinitePresentation]
    (h𝒢 : 𝒢.IsFlatOver p) (s₀ : S) :
    ∃ (a : Γ(S, ⊤)) (P : CochainComplex (S.basicOpen a).toScheme.Modules ℤ) (d : ℕ),
      s₀ ∈ S.basicOpen a ∧ IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ (S.basicOpen a).toScheme) (g' : X' ⟶ Y) (f' : X' ⟶ T'),
        IsPullback g' f' p (g ≫ (S.basicOpen a).ι) →
        Nonempty (DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex _).obj P) ≅
          (derivedPushforward f').obj
            ((DerivedCategory.singleFunctor _ 0).obj ((Modules.pullback g').obj 𝒢))) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨ι, _, _, U, hU, hU'⟩ := exists_finite_nonempty_affine_cover Y
  have := Fintype.ofFinite ι
  -- the truncated Čech complex is perfect
  obtain ⟨e₀⟩ := nonempty_Q_cechModuleComplexTrunc_iso p 𝒢 U hU hU'
  have hKP : (DerivedCategory.Q.obj (cechModuleComplexTrunc p 𝒢 U)).IsPerfect :=
    (isPerfect_Q_cechModuleComplex_of_isNoetherianRing p 𝒢 U hU hU' h𝒢).of_iso e₀.symm
  -- a finite free model near `s₀`
  set x : PrimeSpectrum Γ(S, ⊤) := S.toSpecΓ.base s₀
  obtain ⟨s, hs, P, _, _, hP, Φ, hΦ⟩ := CochainComplex.exists_free_away_quasiIso_baseChange
    (cechModuleComplexNat p 𝒢 U) (cechModuleComplexTrunc p 𝒢 U) ((Fintype.card ι : ℤ) - 1)
    (flat_cechModuleComplexTrunc_X p 𝒢 U hU hU' h𝒢) hKP
    ((cechModuleComplex p 𝒢 U).ιTruncLE _)
    (fun B _ _ ↦ quasiIso_map_baseChange_ιTruncLE_cechModuleComplex p 𝒢 U hU hU' h𝒢 B)
    x.asIdeal
  have hs₀ : s₀ ∈ S.basicOpen s := by
    rw [← S.toSpecΓ_preimage_basicOpen]
    exact hs
  set R := Localization.Away s
  have : Nontrivial R := by
    have := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) R x.asIdeal
      x.isPrime ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).2 hs)
    refine nontrivial_of_ne (0 : R) 1 fun h ↦ this.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← h]
    exact Ideal.zero_mem _
  have := fun n ↦ (hP n).1
  have := fun n ↦ (hP n).2
  set r : ℤ → ℕ := fun n ↦ Module.finrank R (P.X n)
  let b (n : ℤ) : Module.Basis (ULift.{u} (Fin (r n))) R (P.X n) :=
    (Module.finBasis R (P.X n)).reindex Equiv.ulift.symm
  set d : ℕ := ((Fintype.card ι : ℤ) - 1).toNat
  have hr (n : ℤ) (hn : n < 0 ∨ (d : ℤ) < n) : r n = 0 := by
    have : Subsingleton (P.X n) := by
      refine ModuleCat.subsingleton_of_isZero ?_
      rcases hn with hn | hn
      · exact P.isZero_of_isStrictlyGE 0 n hn
      · exact P.isZero_of_isStrictlyLE ((Fintype.card ι : ℤ) - 1) n (by lia)
    exact Module.finrank_zero_of_subsingleton
  -- the complex of free modules over `D(s)`
  set V := S.basicOpen s
  let σ : R →+* Γ(V.toScheme, ⊤) :=
    Localization.awayLift V.ι.appTop.hom s (S.isUnit_ι_appTop_basicOpen s)
  have hσ : σ.comp (algebraMap Γ(S, ⊤) R) = V.ι.appTop.hom :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨s, freeComplexOfBasis P b σ, d, hs₀,
    isFiniteFreeComplex_freeComplexOfBasis P b σ d hr, ?_⟩
  intro T' X' g g' f' H
  let _ : Algebra R Γ(T', ⊤) := (g.appTop.hom.comp σ).toAlgebra
  let _ : Algebra Γ(S, ⊤) Γ(T', ⊤) := (g ≫ V.ι).appTop.hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) R Γ(T', ⊤) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change (g ≫ V.ι).appTop a = g.appTop (σ (algebraMap Γ(S, ⊤) R a))
    rw [← RingHom.comp_apply σ, hσ, Scheme.Hom.comp_appTop]
    rfl
  have hg : algebraMap Γ(S, ⊤) Γ(T', ⊤) =
      ((g ≫ V.ι).appLE ⊤ ⊤ (le_top.trans (g ≫ V.ι).preimage_top.ge)).hom := by
    rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hκ (n : ℤ) (hn : n < 0) : IsEmpty (ULift.{u} (Fin (r n))) := by
    rw [hr n (Or.inl hn)]
    infer_instance
  have : IsSeparated f' := MorphismProperty.of_isPullback H inferInstance
  have hUi := isAffineOpen_iInf_of_isSeparated p U hU
  let e₁ : ((Modules.pullback g).mapHomologicalComplex _).obj (freeComplexOfBasis P b σ) ≅
      freeComplexOfBasis P b (algebraMap R Γ(T', ⊤)) :=
    pullbackFreeComplexIso _ _ g ≪≫ eqToIso (by
      unfold freeComplexOfBasis
      congr 1)
  set K := freeComplexOfBasis (Z := T') P b (algebraMap R Γ(T', ⊤))
  have : K.IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have := hκ i hi
    exact isZero_free_of_isEmpty _
  have := quasiIso_mumfordFreeHom H 𝒢 U hg P b Φ hUi hΦ
  have : QuasiIso (HomologicalComplex.extendMap (mumfordFreeHom H 𝒢 U hg P b Φ)
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2 inferInstance
  have hU₂ (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineHom ((⨅ l, g' ⁻¹ᵁ U (y l)).ι ≫ f') :=
    isAffineHom_ι_comp_of_isPullback H (hUi k y) (iInf_preimage_eq_preimage_iInf g' U y)
  have hU₃ : ⨆ i, g' ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU', Scheme.Hom.preimage_top]
  exact ⟨DerivedCategory.Q.mapIso (e₁ ≪≫
      HomologicalComplex.isoExtendRestriction ComplexShape.embeddingUpNat K) ≪≫
    asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap
      (mumfordFreeHom H 𝒢 U hg P b Φ) ComplexShape.embeddingUpNat)) ≪≫
    (derivedPushforwardSingleIsoCechResolution f' (fun i ↦ g' ⁻¹ᵁ U i) hU₂ hU₃
      ((pullback g').obj 𝒢)).symm⟩

/-- **Mumford's complex over a Noetherian affine base.** Let `p : Y ⟶ S` be proper of finite
presentation over an affine scheme `S` with Noetherian ring of global sections, and `𝒢` an
`𝒪_Y`-module of finite presentation which is flat over `S`. Every point `s₀` of `S` lies in a
basic open `D(a)` over which there is a bounded complex `P` of finite free modules such that for
every `g : T' ⟶ D(a)` and every cartesian square over `g ≫ ι` the cohomology of `g^* P` is
`R^q p'_* g'^* 𝒢`. This is the per-degree form of
`exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem exists_isFiniteFreeComplex_higherDirectImage_of_isNoetherianRing {Y S : Scheme.{u}}
    [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] (p : Y ⟶ S) [IsProper p]
    [LocallyOfFinitePresentation p] (𝒢 : Y.Modules) [𝒢.IsFinitePresentation]
    (h𝒢 : 𝒢.IsFlatOver p) (s₀ : S) :
    ∃ (a : Γ(S, ⊤)) (P : CochainComplex (S.basicOpen a).toScheme.Modules ℤ) (d : ℕ),
      s₀ ∈ S.basicOpen a ∧ IsFiniteFreeComplex P d ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ (S.basicOpen a).toScheme) (g' : X' ⟶ Y) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' p (g ≫ (S.basicOpen a).ι) →
        ∀ q : ℕ, Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj 𝒢)) := by
  obtain ⟨a, P, d, hs₀, hP, h⟩ :=
    exists_isFiniteFreeComplex_derivedPushforward_of_isNoetherianRing p 𝒢 h𝒢 s₀
  refine ⟨a, P, d, hs₀, hP, fun g g' f' _ H q ↦ ?_⟩
  obtain ⟨e⟩ := h g g' f' H
  exact ⟨(DerivedCategory.homologyFunctorFactors _ q).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    homologyDerivedPushforwardSingleIso f' ((Modules.pullback g').obj 𝒢) q⟩

end AlgebraicGeometry.Scheme.Modules
