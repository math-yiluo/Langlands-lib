import Langlands.GaloisCohomology.Global.Units.Brauer
import Langlands.GaloisCohomology.Global.Units.DivisorCount
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees
import Langlands.Cohomology.Profinite.InflationRestriction.FiveTerm

/-!
# `H³` of the units and of the `S`-units of `K_S`

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places, `K_S` the maximal
extension of `K` in `Ω` unramified outside `S`, `G_S = Gal(K_S/K)`, `𝒪_Sˣ` the `S`-units of `K_S`,
`D` the divisors of `K_S` prime to `S`, and `ℓ` a prime such that `S` contains the places above `ℓ`.

* `eq_zero_of_infl_three_eq_zero`: for a closed normal subgroup `N` of a profinite group `G` and a
  smooth `G`-module `A` with `H¹(N, A) = 0` and `H²(N, A)` killed, element by element, by integers
  prime to `ℓ`, inflation `H³(G/N, A^N) → H³(G, A)` is injective on classes killed by a power of `ℓ`
  (dimension shifting with the coinduced module and the five-term exact sequence).
* `exists_generator_outsideLocalizationHom`: for `v ∉ S` the image of the local Galois group in `G_S`
  is topologically cyclic up to every neighbourhood of `1`.
* `unitsRestriction_maximal_eq_zero_of_primary`, `exists_coprime_nsmul_cohomology_two_ker_quotientMap`:
  `ℓ`-primary Brauer classes of `K` die in `K_S`, and `H²(Gal(Ω/K_S), Ωˣ)` is killed, element by
  element, by integers prime to `ℓ`.
* `eq_zero_of_cohomology_three_maximalUnits`: `H³(G_S, K_Sˣ)(ℓ) = 0`.
* `exists_coeffMap_unitsToSDivisor_eq`: every `ℓ`-primary class of `H²(G_S, D)` is the divisor class of a
  class of `H²(G_S, K_Sˣ)` (classes with one prescribed local invariant outside `S`, counted against
  `card_le_of_topologicallyCyclic`).
* `eq_zero_of_cohomology_three_maximalSUnits`: `H³(G_S, 𝒪_Sˣ)(ℓ) = 0`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section Abstract

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Inflation in degree three, `ℓ`-primary part.** If `H¹(N, A) = 0` and every class of
`H²(N, A)` is killed by an integer prime to `ℓ`, a class of `H³(G/N, A^N)` killed by a power of `ℓ`
whose inflation to `H³(G, A)` vanishes is zero. -/
theorem eq_zero_of_infl_three_eq_zero (A : Rep.{u} k G) [IsSmoothRep A] (N : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) (ℓ : ℕ)
    (h2 : ∀ y : cohomology (Rep.res N.subtype A) 2, ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0)
    (x : cohomology (A.quotientToInvariants N) 3) (hx : (infl A N 3).hom x = 0)
    (j : ℕ) (hj : ℓ ^ j • x = 0) : x = 0 := by
  have hX := coindShortComplex_shortExact A
  have hS := shortExact_map_res N hX
  have hQ := shortExact_map_quotientToInvariants_coindShortComplex A N h1
  have hδQ : IsIso (δ hQ (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hQ 1
    (isZero_cohomology_quotientToInvariants_discreteCoind A N 1)
    (isZero_cohomology_quotientToInvariants_discreteCoind A N (1 + 1))
  have hδX : IsIso (δ hX (1 + 1) (1 + 1 + 1) rfl) := isIso_δ_of_isZero hX 1
    (isZero_cohomology_discreteCoind k G A 1) (isZero_cohomology_discreteCoind k G A (1 + 1))
  have hδS : IsIso (δ hS (0 + 1) (0 + 1 + 1) rfl) := isIso_δ_of_isZero hS 0
    (isZero_cohomology_res_discreteCoind A N hN 0)
    (isZero_cohomology_res_discreteCoind A N hN (0 + 1))
  have injQ : Function.Injective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injX : Function.Injective (δ hX (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have injS : Function.Injective (δ hS (0 + 1) (0 + 1 + 1) rfl).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have surjQ : Function.Surjective (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨x', rfl⟩ := surjQ x
  have hsq := δ_comp_infl (N := N) hX hQ (1 + 1) (1 + 1 + 1) rfl
  have hx' : (infl (coindCokernel A) N (1 + 1)).hom x' = 0 := by
    have e : (δ hX (1 + 1) (1 + 1 + 1) rfl).hom ((infl (coindCokernel A) N (1 + 1)).hom x') =
        (infl A N 3).hom ((δ hQ (1 + 1) (1 + 1 + 1) rfl).hom x') :=
      (congrArg (fun φ => ModuleCat.Hom.hom φ x') hsq).symm
    exact injX (e.trans (hx.trans (map_zero _).symm))
  have hmem : x' ∈ LinearMap.ker (infl (coindCokernel A) N 2).hom := hx'
  have hfive := ProfiniteCohomology.fiveTerm_exact (coindCokernel A) N hN
  rw [← hfive.2.2.2] at hmem
  obtain ⟨w, rfl⟩ := hmem
  obtain ⟨m, hm, hmw⟩ := h2 ((δ hS (0 + 1) (0 + 1 + 1) rfl).hom w.1)
  have hw : m • w = 0 := by
    apply Subtype.ext
    apply injS
    exact (map_nsmul (δ hS (0 + 1) (0 + 1 + 1) rfl).hom m w.1).trans (hmw.trans (map_zero _).symm)
  have h1' : m • transgression (coindCokernel A) N hN w = 0 := by
    rw [← map_nsmul, hw, map_zero]
  have h2' : ℓ ^ j • transgression (coindCokernel A) N hN w = 0 := by
    apply injQ
    exact (map_nsmul _ (ℓ ^ j) _).trans (hj.trans (map_zero _).symm)
  have h0 := eq_zero_of_coprime_nsmul_eq_zero hm h1' h2'
  exact (congrArg (δ hQ (1 + 1) (1 + 1 + 1) rfl).hom h0).trans (map_zero _)

end Abstract

section Torsion

variable {M : Type*} [AddCommGroup M]

/-- An element of finite order is the sum of an element killed by a power of the prime `ℓ` and one
killed by an integer prime to `ℓ`. -/
theorem exists_primary_add_coprime {ℓ : ℕ} (hℓ : ℓ.Prime) {y : M} (hy : IsOfFinAddOrder y) :
    ∃ y₁ y₂ : M, y = y₁ + y₂ ∧ (∃ a : ℕ, ℓ ^ a • y₁ = 0) ∧ ∃ m : ℕ, m.Coprime ℓ ∧ m • y₂ = 0 := by
  obtain ⟨a, N, hN, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (addOrderOf_pos_iff.2 hy).ne' ℓ
    hℓ.ne_one
  have hcop' : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hN
  have hcop : Nat.Coprime (ℓ ^ a) N := Nat.Coprime.pow_left _ hcop'
  obtain ⟨s, t, hst⟩ := exists_mul_add_mul_eq_one hcop
  have hy0 : ((ℓ ^ a * N : ℕ) : ℤ) • y = 0 := by
    rw [natCast_zsmul, ← hn, addOrderOf_nsmul_eq_zero]
  refine ⟨((N : ℤ) * t) • y, (((ℓ ^ a : ℕ) : ℤ) * s) • y, ?_, ⟨a, ?_⟩, N, hcop'.symm, ?_⟩
  · rw [← add_zsmul, show (N : ℤ) * t + ((ℓ ^ a : ℕ) : ℤ) * s = 1 by linear_combination hst,
      one_zsmul]
  · rw [← natCast_zsmul, smul_smul, show ((ℓ ^ a : ℕ) : ℤ) * (N * t) = t * ((ℓ ^ a * N : ℕ) : ℤ) by
      push_cast; ring, mul_smul, hy0, smul_zero]
  · rw [← natCast_zsmul, smul_smul, show (N : ℤ) * (((ℓ ^ a : ℕ) : ℤ) * s) =
      s * ((ℓ ^ a * N : ℕ) : ℤ) by push_cast; ring, mul_smul, hy0, smul_zero]

end Torsion

section Generator

open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

attribute [local instance] Langlands.Global.AdelicFunctoriality.isGalois_adicCompletion

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) (ι : PlaceEmbeddings K Ω)

/-- The decomposition group in `Gal(E/K)` of the place of `ι` above `v ∉ S`, for a finite Galois
subextension `E` of `K_S`, is cyclic. -/
theorem isCyclic_range_decompositionHom_level (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (E : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S)) :
    haveI := NumberField.of_module_finite K E.toIntermediateField
    IsCyclic (decompositionHom (v.1.adicCompletion K) (levelEmbedding S ι v.1 E.toIntermediateField) :
      Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
        Gal(E.toIntermediateField/K)).range := by
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K _
  let j := levelEmbedding S ι v.1 E.toIntermediateField
  let := completionAlgebraOf v.1 j
  have := isScalarTower_completionAlgebraOf v.1 j
  have hu := isUnramifiedIn_of_maximalUnramifiedOutside S E.toIntermediateField v.2
  rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one] at hu
  have hwv := (placeOfAlgHom j).2
  have hcycl := Langlands.ClassFieldTheory.Global.isCyclic_localGal v.1 (placeOfAlgHom j).1 (hu _ hwv)
  have hdec := decompositionHom_eq_comp v.1 j
  have hsurj : Function.Surjective (BrauerComparison.normalKrullRestriction (v.1.adicCompletion K)
      ((placeOfAlgHom j).1.adicCompletion E.toIntermediateField)
      (AlgebraicClosure (v.1.adicCompletion K))) := AlgEquiv.restrictNormalHom_surjective _
  let D := (decompositionHom (v.1.adicCompletion K) j :
    Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
      Gal(E.toIntermediateField/K)).range
  have hmemD : ∀ x, localDecompositionHomOf v.1 j x ∈ D := fun x => by
    obtain ⟨σ, rfl⟩ := hsurj x
    refine ⟨σ, ?_⟩
    change decompositionHom (v.1.adicCompletion K) j σ = _
    rw [hdec]
    rfl
  let ψ : Gal((placeOfAlgHom j).1.adicCompletion E.toIntermediateField/v.1.adicCompletion K) →* D :=
    (localDecompositionHomOf v.1 j : _ →* Gal(E.toIntermediateField/K)).codRestrict D hmemD
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, σ, rfl⟩
    refine ⟨BrauerComparison.normalKrullRestriction _ _ _ σ, Subtype.ext ?_⟩
    change localDecompositionHomOf v.1 j _ = decompositionHom (v.1.adicCompletion K) j σ
    rw [hdec]
    rfl
  exact isCyclic_of_surjective ψ hψ

/-- Elements of the local Galois group with the same image in `Gal(E/K)` have localizations which
differ by an element fixing `E`. -/
theorem inv_mul_mem_fixingSubgroup_of_decompositionHom_eq (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (E : FiniteGaloisIntermediateField K (maximalUnramifiedOutside K Ω S))
    {h h' : Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K)}
    (hh : decompositionHom (v.1.adicCompletion K) (levelEmbedding S ι v.1 E.toIntermediateField) h =
      decompositionHom (v.1.adicCompletion K) (levelEmbedding S ι v.1 E.toIntermediateField) h') :
    (outsideLocalizationHom S ι v h)⁻¹ * outsideLocalizationHom S ι v h' ∈
      E.toIntermediateField.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv]
  have e1 := levelRestrict_localizationHom S ι v.1 E h
  have e2 := levelRestrict_localizationHom S ι v.1 E h'
  change (levelRestrict S E (localizationHom ι S v.1 h))⁻¹ *
    levelRestrict S E (localizationHom ι S v.1 h') = 1
  rw [e1, e2, hh, inv_mul_cancel]

/-- **Decomposition groups outside `S` are topologically cyclic.** For `v ∉ S` and a neighbourhood
`V` of `1` in `G_S` there is `h₀` in the local Galois group such that every element of the image of the
localization at `v` lies in `φ(h₀)^k V` for some `k` (the images in the finite quotients of `G_S` are
the decomposition groups of an unramified place, which are cyclic). -/
theorem exists_generator_outsideLocalizationHom (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (V : Set (GaloisGroupUnramifiedOutside K Ω S))
    (hV : V ∈ nhds (1 : GaloisGroupUnramifiedOutside K Ω S)) :
    ∃ h₀ : Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K),
      ∀ h, ∃ k : ℤ, (outsideLocalizationHom S ι v (h₀ ^ k))⁻¹ * outsideLocalizationHom S ι v h ∈ V := by
  obtain ⟨L, hL, hLV⟩ := (krullTopology_mem_nhds_one_iff K (maximalUnramifiedOutside K Ω S) V).1 hV
  obtain ⟨E, hLE⟩ := exists_finiteGaloisIntermediateField_le L
  have : NumberField E.toIntermediateField := NumberField.of_module_finite K _
  have hcyc := isCyclic_range_decompositionHom_level S ι v E
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (decompositionHom (v.1.adicCompletion K)
    (levelEmbedding S ι v.1 E.toIntermediateField) :
      Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
        Gal(E.toIntermediateField/K)).range)
  obtain ⟨h₀, hh₀⟩ := g.2
  refine ⟨h₀, fun h => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨_, h, rfl⟩)
  refine ⟨k, hLV (IntermediateField.fixingSubgroup_antitone hLE ?_)⟩
  refine inv_mul_mem_fixingSubgroup_of_decompositionHom_eq S ι v E ?_
  have e1 := congrArg Subtype.val hk
  rw [SubgroupClass.coe_zpow, ← hh₀] at e1
  exact (map_zpow (decompositionHom (v.1.adicCompletion K)
    (levelEmbedding S ι v.1 E.toIntermediateField) :
      Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) →*
        Gal(E.toIntermediateField/K)) h₀ k).trans e1

end Generator

section KernelBrauer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- **`Br(K_S)(ℓ) = 0` on classes of `K`.** A Brauer class of `K` killed by a power of `ℓ` dies in
`K_S`. -/
theorem unitsRestriction_maximal_eq_zero_of_primary (x : cohomology (unitsModule K Ω) 2) {k : ℕ}
    (hx : ℓ ^ k • x = 0) :
    haveI : IsGalois (maximalUnramifiedOutside K Ω S) Ω :=
      IsGalois.tower_top_of_isGalois K (maximalUnramifiedOutside K Ω S) Ω
    (unitsRestriction K (maximalUnramifiedOutside K Ω S) Ω 2).hom x = 0 := by
  classical
  let ι : PlaceEmbeddings K Ω := Classical.arbitrary _
  obtain ⟨hfin, -⟩ := localInvariant_finite_support_and_sum_eq_zero ι x
  obtain ⟨E, _, hES, hEc, hEdeg⟩ :=
    exists_isComplex_le_maximalUnramifiedOutside (Ω := Ω) S hℓ hS hfin.toFinset k
  have hres : brauerRestriction E x = 0 := by
    refine brauerRestriction_eq_zero_of_isComplex ι E hEc x (ℓ ^ k) hx fun v hv w _ =>
      hEdeg v ?_ w
    rw [Set.Finite.mem_toFinset, Function.mem_support, Ne, localInvariant_eq_zero_iff]
    exact hv
  exact unitsRestriction_maximal_eq_zero S E hES x hres

/-- The kernel of `Gal(Ω/K) → G_S` is closed. -/
theorem isClosed_ker_quotientMap :
    IsClosed (((GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker : Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) := by
  have : (((GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker : Subgroup Gal(Ω/K)) : Set Gal(Ω/K)) =
        GaloisGroupUnramifiedOutside.quotientMap K Ω S ⁻¹' {1} := rfl
  rw [this]
  have : T1Space (GaloisGroupUnramifiedOutside K Ω S) :=
    @T2Space.t1Space _ _ (GaloisGroupUnramifiedOutside.t2Space K Ω S)
  exact isClosed_singleton.preimage (GaloisGroupUnramifiedOutside.quotientMap K Ω S).continuous

/-- The fixed field of an open subgroup containing `Gal(Ω/K_S)` lies in `K_S`. -/
theorem algebraMap_fixedField_mem (U : OpenSubgroup Gal(Ω/K))
    (hNU : (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker ≤ (U : Subgroup Gal(Ω/K)))
    (x : IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) :
    algebraMap (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) Ω x ∈
      maximalUnramifiedOutside K Ω S := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramifiedOutside K Ω S)]
  intro σ
  have hσ : (σ : Gal(Ω/K)) ∈ (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker :=
    (mem_ker_quotientMap_iff S _).2 fun y hy =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 y hy
  exact x.2 ⟨σ, hNU hσ⟩

/-- **Restriction to `Gal(Ω/K_S)` through an open subgroup.** Let `U ⊇ Gal(Ω/K_S)` be open with fixed
field `F`. A class of `H²(Gal(Ω/F), Ωˣ)` which dies in the maximal extension of `F` unramified outside
the places above `S` (which is `K_S`) restricts to zero on `Gal(Ω/K_S)`. -/
theorem resOfLE_openCohomologyIso_inv_eq_zero (U : OpenSubgroup Gal(Ω/K))
    (hNU : (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker ≤ (U : Subgroup Gal(Ω/K)))
    (z : cohomology (unitsModule (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) Ω) 2)
    (hz : haveI := NumberField.of_module_finite K (IntermediateField.fixedField (U : Subgroup Gal(Ω/K)))
      haveI : IsGalois (maximalUnramifiedOutside (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) Ω
          (finitePlacesAbove (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) S)) Ω :=
        IsGalois.tower_top_of_isGalois (IntermediateField.fixedField (U : Subgroup Gal(Ω/K)))
          (maximalUnramifiedOutside (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) Ω
            (finitePlacesAbove (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) S)) Ω
      (unitsRestriction (IntermediateField.fixedField (U : Subgroup Gal(Ω/K)))
        (maximalUnramifiedOutside (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) Ω
          (finitePlacesAbove (IntermediateField.fixedField (U : Subgroup Gal(Ω/K))) S)) Ω 2).hom z = 0) :
    (resOfLE (unitsModule K Ω) hNU 2).hom ((openCohomologyIso U 2).inv.hom z) = 0 := by
  let F := IntermediateField.fixedField (U : Subgroup Gal(Ω/K))
  have : NumberField F := NumberField.of_module_finite K F
  let M := maximalUnramifiedOutside F Ω (finitePlacesAbove F S)
  have : IsGalois M Ω := IsGalois.tower_top_of_isGalois F M Ω
  let N := (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
    GaloisGroupUnramifiedOutside K Ω S).ker
  have hM : M.restrictScalars K = maximalUnramifiedOutside K Ω S :=
    restrictScalars_maximalUnramifiedOutside S (algebraMap_fixedField_mem S U hNU)
  have hMS : ∀ y : Ω, y ∈ M ↔ y ∈ maximalUnramifiedOutside K Ω S := fun y => by
    rw [← hM, IntermediateField.mem_restrictScalars]
  let h : Gal(Ω/M) →ₜ* (U : Subgroup Gal(Ω/K)) :=
    (galFixedFieldHomOpen U).comp (BrauerComparison.krullRestriction F M Ω Ω)
  have hh : ∀ (σ : Gal(Ω/M)) (y : Ω), ((h σ : Gal(Ω/K)) : Ω → Ω) y = σ y := fun σ y =>
    krullRestriction_self_apply F M Ω σ y
  have hmem : ∀ σ : Gal(Ω/M), (h σ : Gal(Ω/K)) ∈ N := fun σ =>
    (mem_ker_quotientMap_iff S _).2 fun y hy => by
      rw [hh]
      exact σ.commutes ⟨y, (hMS y).2 hy⟩
  let e : Gal(Ω/M) ≃* N :=
    { toFun := fun σ => ⟨h σ, hmem σ⟩
      invFun := fun τ => { (τ.1 : Ω ≃ₐ[K] Ω) with
        commutes' := fun c => (mem_ker_quotientMap_iff S τ.1).1 τ.2 c ((hMS c).1 c.2) }
      left_inv := fun σ => AlgEquiv.ext fun y => hh σ y
      right_inv := fun τ => Subtype.ext (AlgEquiv.ext fun y => hh _ y)
      map_mul' := fun σ τ => Subtype.ext (show (h (σ * τ) : Gal(Ω/K)) =
        (h σ : Gal(Ω/K)) * (h τ : Gal(Ω/K)) by rw [map_mul]; rfl) }
  have he : Continuous e.toMonoidHom :=
    (continuous_subtype_val.comp h.continuous).subtype_mk _
  have : CompactSpace Gal(Ω/M) := galois_compactSpace _ _
  have : T2Space Gal(Ω/K) := galois_t2Space _ _
  have he' : Continuous e.symm.toMonoidHom := by
    let hm := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
    exact hm.symm.continuous
  let f : Rep.res e.toMonoidHom (Rep.res N.subtype (unitsModule K Ω)) ⟶ unitsModule M Ω :=
    Rep.ofHom ⟨LinearMap.id, fun σ => LinearMap.ext fun x =>
      Additive.toMul.injective (Units.ext (hh σ ((Additive.toMul (show Additive Ωˣ from x) : Ωˣ) : Ω)))⟩
  have hiso := isIso_map_of_mulEquiv (A := Rep.res N.subtype (unitsModule K Ω))
    (B := unitsModule M Ω) e he he' f (by exact Function.bijective_id) 2
  have hinj : Function.Injective (map ⟨e.toMonoidHom, he⟩ f 2).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero]
  let y := (openCohomologyIso U 2).inv.hom z
  have hzy : z = (map (galFixedFieldHomOpen U) (unitsModuleOpenHom U) 2).hom y := by
    rw [← openCohomologyIso_hom]
    exact (Iso.inv_hom_id_apply (openCohomologyIso U 2) z).symm
  rw [hzy] at hz
  have h1 := map_comp (subgroupInclusionOfLE hNU) (resResHom (unitsModule K Ω) hNU)
    ⟨e.toMonoidHom, he⟩ f 2
  have h2 := map_comp (galFixedFieldHomOpen U) (unitsModuleOpenHom U)
    (BrauerComparison.krullRestriction F M Ω Ω)
    (underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients F M Ω Ω)) 2
  refine (congrArg (fun F => F.hom y) h1).symm.trans ?_
  refine Eq.trans ?_ ((congrArg (fun F => F.hom y) h2).trans hz)
  refine congrArg (fun F => F.hom y) (ProfiniteCohomology.map_congr
    (A := Rep.res (U : Subgroup Gal(Ω/K)).subtype (unitsModule K Ω))
    (ψ := (galFixedFieldHomOpen U).comp (BrauerComparison.krullRestriction F M Ω Ω)) _
    ((Rep.resFunctor (BrauerComparison.krullRestriction F M Ω Ω : Gal(Ω/M) →* Gal(Ω/F))).map
      (unitsModuleOpenHom U) ≫
        underlyingHom _ (BrauerComparison.continuousUnitRestrictionCoefficients F M Ω Ω)) ?_
    (fun a => ?_) 2)
  · ext σ : 1
    exact Subtype.ext (AlgEquiv.ext fun x => rfl)
  · exact Additive.toMul.injective (Units.ext rfl)

include hℓ hS in
/-- **`H²(Gal(Ω/K_S), Ωˣ)` has no `ℓ`-torsion**: every class is killed by an integer prime to
`ℓ`. -/
theorem exists_coprime_nsmul_cohomology_two_ker_quotientMap
    (y : cohomology (Rep.res (GaloisGroupUnramifiedOutside.quotientMap K Ω S : Gal(Ω/K) →*
      GaloisGroupUnramifiedOutside K Ω S).ker.subtype (unitsModule K Ω)) 2) :
    ∃ m : ℕ, m.Coprime ℓ ∧ m • y = 0 := by
  obtain ⟨U, hU, hNU, y', rfl⟩ := exists_resOfLE_eq (unitsModule K Ω) (isClosed_ker_quotientMap S)
    2 y
  let U' : OpenSubgroup Gal(Ω/K) := ⟨U, hU⟩
  set F := IntermediateField.fixedField (U' : Subgroup Gal(Ω/K)) with hF
  have : FiniteDimensional K F := finiteDimensional_fixedField_openSubgroup U'
  have : NumberField F := NumberField.of_module_finite K F
  have : CompactSpace Gal(Ω/F) := galois_compactSpace _ _
  set z := (openCohomologyIso U' 2).hom.hom y' with hz
  obtain ⟨z₁, z₂, hz12, ⟨a, ha⟩, m, hm, hmz⟩ := exists_primary_add_coprime hℓ
    (isTorsion_cohomology (unitsModule F Ω) (by norm_num) z)
  have hy' : y' = (openCohomologyIso U' 2).inv.hom z₁ + (openCohomologyIso U' 2).inv.hom z₂ := by
    rw [← map_add, ← hz12, hz]
    exact (Iso.hom_inv_id_apply (openCohomologyIso U' 2) y').symm
  have hSF : ∀ w : HeightOneSpectrum (𝓞 F), ((ℓ : ℕ) : 𝓞 F) ∈ w.asIdeal →
      w ∈ finitePlacesAbove F S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 F) ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  have h1 := resOfLE_openCohomologyIso_inv_eq_zero S U' hNU z₁
    (unitsRestriction_maximal_eq_zero_of_primary (finitePlacesAbove F S) hℓ hSF z₁ ha)
  refine ⟨m, hm, ?_⟩
  rw [hy', map_add, h1, zero_add, ← map_nsmul, ← map_nsmul, hmz, map_zero, map_zero]

include hℓ hS in
/-- **`H³(G_S, K_Sˣ)(ℓ) = 0`.** A class of `H³(G_S, K_Sˣ)` killed by a power of `ℓ` is zero. -/
theorem eq_zero_of_cohomology_three_maximalUnits
    (x : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 3) {k : ℕ}
    (hx : ℓ ^ k • x = 0) : x = 0 := by
  have : CompactSpace Gal(Ω/K) := galois_compactSpace _ _
  obtain ⟨I, hI, -⟩ := exists_map_eq_iso_comp_infl (GaloisGroupUnramifiedOutside.quotientMap K Ω S)
    (GaloisGroupUnramifiedOutside.quotientMap_surjective K Ω S)
    (GaloisGroupUnramifiedOutside.isQuotientMap_quotientMap K Ω S) (maximalUnitsHom K Ω S)
    (maximalUnitsHom_injective S) (exists_maximalUnitsHom_eq S) 3
  have h0 : (infl (unitsModule K Ω) _ 3).hom (I.hom x) = 0 := by
    have : Subsingleton (cohomology (unitsModule K Ω) 3) := subsingleton_cohomology_three_unitsModule
    exact Subsingleton.elim _ _
  have hIx := eq_zero_of_infl_three_eq_zero (unitsModule K Ω) _ (isClosed_ker_quotientMap S)
    (isZero_cohomology_one_ker_quotientMap S) ℓ
    (exists_coprime_nsmul_cohomology_two_ker_quotientMap S hℓ hS) (I.hom x) h0 k
    (by rw [← map_nsmul, hx, map_zero])
  have hinj : Function.Injective I.hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  exact hinj (hIx.trans (map_zero _).symm)

end KernelBrauer

section PlaceAbove

variable {K : Type u} [Field K] [NumberField K]

/-- A prime number lies in some finite place of `K`. -/
theorem exists_natCast_mem_asIdeal {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hP : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hℓ).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(ℓ : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [(algebraMap ℤ (𝓞 K)).injective_int (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral _ hker
  have hmem : ((ℓ : ℕ) : 𝓞 K) ∈ Q := by
    have h : (ℓ : ℤ) ∈ Ideal.under ℤ Q := hQP ▸ Ideal.mem_span_singleton_self _
    change algebraMap ℤ (𝓞 K) (ℓ : ℤ) ∈ Q at h
    rw [eq_intCast, Int.cast_natCast] at h
    exact h
  have hne : Q ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hmem
    exact (Nat.cast_ne_zero.2 hℓ.ne_zero) hmem
  exact ⟨⟨Q, hQ.isPrime, hne⟩, hmem⟩

end PlaceAbove

section DivisorClasses

open Langlands.ClassFieldTheory.Local

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- **A class of `K_S` with one prescribed local invariant outside `S`.** For `v ∉ S` and `r ∈ ℚ/ℤ`
killed by a power of `ℓ`, some class of `H²(G_S, K_Sˣ)` has image in the Brauer group of `K` with
invariant `r` at `v` and localization zero at every other finite place outside `S`. -/
theorem exists_maximalUnits_localInvariant_single (ι : PlaceEmbeddings K Ω)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (r : RationalModIntegers) {n : ℕ}
    (hr : ℓ ^ n • r = 0) :
    ∃ z : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      localInvariant ι v.1 (maximalUnitsInflation K Ω S 2 z) = r ∧
        ∀ w, w ∉ S → w ≠ v.1 → brauerLocalization ι w 2 (maximalUnitsInflation K Ω S 2 z) = 0 := by
  classical
  obtain ⟨v₀, hv₀⟩ := exists_natCast_mem_asIdeal (K := K) hℓ
  have hv₀S : v₀ ∈ S := hS v₀ hv₀
  have hne : v₀ ≠ v.1 := fun h => v.2 (h ▸ hv₀S)
  let f₁ : HeightOneSpectrum (𝓞 K) → RationalModIntegers := Pi.single v.1 r
  let f₂ : HeightOneSpectrum (𝓞 K) → RationalModIntegers := Pi.single v₀ r
  have h1 : (Function.support f₁).Finite :=
    (Set.finite_singleton v.1).subset Pi.support_single_subset
  have h2 : (Function.support f₂).Finite :=
    (Set.finite_singleton v₀).subset Pi.support_single_subset
  have hs : ∀ (a w : HeightOneSpectrum (𝓞 K)),
      ℓ ^ n • (Pi.single a r : HeightOneSpectrum (𝓞 K) → RationalModIntegers) w = 0 := fun a w => by
    by_cases h : w = a
    · subst h
      rw [Pi.single_eq_same, hr]
    · rw [Pi.single_eq_of_ne h, smul_zero]
  have hsum : ∑ᶠ w, (f₁ w - f₂ w) = 0 := by
    rw [finsum_sub_distrib h1 h2, finsum_eq_single f₁ v.1 fun w hw => by
        simp only [f₁]
        exact Pi.single_eq_of_ne hw _,
      finsum_eq_single f₂ v₀ fun w hw => by
        simp only [f₂]
        exact Pi.single_eq_of_ne hw _]
    simp only [f₁, f₂, Pi.single_eq_same, sub_self]
  obtain ⟨x, hx1, hx2⟩ := exists_localInvariant_eq ι (fun w => f₁ w - f₂ w)
    ((h1.union h2).subset (Function.support_sub _ _)) hsum
  have hxk : ℓ ^ n • x = 0 := eq_zero_of_brauerLocalization_eq_zero' ι _
    (fun w => by
      rw [← localInvariant_eq_zero_iff, map_nsmul, hx1 w, smul_sub]
      simp only [f₁, f₂]
      rw [hs, hs, sub_zero])
    (fun w => by rw [map_nsmul, hx2 w, smul_zero])
  have hres := unitsRestriction_maximal_eq_zero_of_primary S hℓ hS x hxk
  obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1
    ((mem_range_maximalUnitsInflation_two_iff S x).2 (res_ker_quotientMap_eq_zero S x hres))
  refine ⟨z, ?_, fun w hwS hwv => ?_⟩
  · rw [hz, hx1]
    simp only [f₁, f₂, Pi.single_eq_same, Pi.single_eq_of_ne hne.symm, sub_zero]
  · rw [hz, ← localInvariant_eq_zero_iff, hx1]
    have hw0 : w ≠ v₀ := fun h => hwS (h ▸ hv₀S)
    simp only [f₁, f₂, Pi.single_eq_of_ne hwv, Pi.single_eq_of_ne hw0, sub_zero]

/-- The local Galois groups at the finite places are profinite. -/
theorem compactSpace_and_totallyDisconnectedSpace_localGal (v : HeightOneSpectrum (𝓞 K)) :
    CompactSpace Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) ∧
      TotallyDisconnectedSpace Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) := by
  have : CharZero (v.adicCompletion K) := charZero_adicCompletion v
  have : IsGalois (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) := IsGalois.mk
  exact ⟨(galois_isProfinite _ _).1, (galois_isProfinite _ _).2.2⟩

/-- In `ℚ/ℤ`, the classes of `k / m` for `0 ≤ k < m` are distinct. -/
theorem injective_rationalClass_div {m : ℕ} (hm : m ≠ 0) :
    Function.Injective fun k : Fin m => rationalClass (((k : ℕ) : ℚ) / (m : ℚ)) := by
  intro k k' hkk
  have h0 : rationalClass (((k : ℕ) : ℚ) / (m : ℚ) - ((k' : ℕ) : ℚ) / (m : ℚ)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hkk
  obtain ⟨j, hj⟩ := (Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff _).1 h0
  have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hj' : (j : ℚ) * (m : ℚ) = ((k : ℕ) : ℚ) - ((k' : ℕ) : ℚ) := by
    rw [hj]
    field_simp
  have hj'' : j * (m : ℤ) = ((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ) := by exact_mod_cast hj'
  have hk : ((k : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast k.2
  have hk' : ((k' : ℕ) : ℤ) < (m : ℤ) := by exact_mod_cast k'.2
  have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := Int.natCast_nonneg _
  have hk0' : (0 : ℤ) ≤ ((k' : ℕ) : ℤ) := Int.natCast_nonneg _
  have hj0 : j = 0 := by
    rcases lt_trichotomy j 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  rw [hj0, zero_mul] at hj''
  apply Fin.ext
  have : ((k : ℕ) : ℤ) = ((k' : ℕ) : ℤ) := by linarith
  exact_mod_cast this

/-- `m • (k / m) = 0` in `ℚ/ℤ`. -/
theorem nsmul_rationalClass_div_eq_zero {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    m • rationalClass ((k : ℚ) / (m : ℚ)) = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hm)]
  exact (Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff _).2
    ⟨(k : ℤ), Int.cast_natCast k⟩

include hℓ hS in
/-- **`ℓ ^ n` components at `v`.** For `v ∉ S` there are `ℓ ^ n` classes of `H²(G_S, K_Sˣ)` whose
divisor classes have distinct components at `v`, killed by `ℓ ^ n`, and component zero at every other
place outside `S` (classes with local invariants `k / ℓ ^ n` at `v`). -/
theorem exists_maximalUnits_component_family (ι : PlaceEmbeddings K Ω)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) (n : ℕ) :
    ∃ z : Fin (ℓ ^ n) → cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      Function.Injective (fun k => (map (outsideLocalizationHom S ι v)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom (z k))) ∧
      (∀ k, ℓ ^ n • (map (outsideLocalizationHom S ι v)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom (z k)) = 0) ∧
      ∀ k w, w ≠ v → (map (outsideLocalizationHom S ι w)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) w) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom (z k)) = 0 := by
  have hm : ℓ ^ n ≠ 0 := pow_ne_zero n hℓ.ne_zero
  choose z hz1 hz2 using fun k : Fin (ℓ ^ n) =>
    exists_maximalUnits_localInvariant_single S hℓ hS ι v
      (rationalClass (((k : ℕ) : ℚ) / ((ℓ ^ n : ℕ) : ℚ)))
      (nsmul_rationalClass_div_eq_zero hm (k : ℕ))
  refine ⟨z, fun k k' hkk => ?_, fun k => ?_, fun k w hw => ?_⟩
  · have h1 : (map (outsideLocalizationHom S ι v)
        (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom (z k - z k')) = 0 := by
      rw [map_sub, map_sub]
      exact sub_eq_zero.2 hkk
    have h2 := (brauerLocalization_maximalUnitsInflation_eq_zero_iff S ι v _).2 h1
    have h3 := (localInvariant_eq_zero_iff ι v.1 _).2 h2
    rw [map_sub, map_sub, hz1 k, hz1 k', sub_eq_zero] at h3
    exact injective_rationalClass_div hm h3
  · have h1 : brauerLocalization ι v.1 2 (maximalUnitsInflation K Ω S 2 (ℓ ^ n • z k)) = 0 := by
      rw [← localInvariant_eq_zero_iff, map_nsmul, map_nsmul, hz1 k]
      exact nsmul_rationalClass_div_eq_zero hm (k : ℕ)
    have h2 := (brauerLocalization_maximalUnitsInflation_eq_zero_iff S ι v _).1 h1
    rw [map_nsmul, map_nsmul] at h2
    exact h2
  · exact (brauerLocalization_maximalUnitsInflation_eq_zero_iff S ι w _).1
      (hz2 k w.1 w.2 fun h => hw (Subtype.ext h))

/-- **Counting.** If `Φ : Fin m → C` is injective with values in a set `P` which has at most `m`
elements in every finite subset, every element of `P` is a value of `Φ`. -/
theorem mem_range_of_card_le {C : Type*} {m : ℕ} {Φ : Fin m → C}
    (hΦ : Function.Injective Φ) (P : C → Prop) (hP : ∀ s : Finset C, (∀ c ∈ s, P c) → s.card ≤ m)
    (hΦP : ∀ k, P (Φ k)) {c : C} (hc : P c) : ∃ k, Φ k = c := by
  classical
  by_contra hcn
  have hcn' : c ∉ Finset.univ.image Φ := fun h => by
    obtain ⟨k, -, hk⟩ := Finset.mem_image.1 h
    exact hcn ⟨k, hk⟩
  have hle := hP (insert c (Finset.univ.image Φ)) fun c' hc' => by
    rcases Finset.mem_insert.1 hc' with rfl | hc'
    · exact hc
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hc'
      exact hΦP k
  rw [Finset.card_insert_of_notMem hcn', Finset.card_image_of_injective _ hΦ, Finset.card_univ,
    Fintype.card_fin] at hle
  omega

omit [IsSepClosure K Ω] in
/-- At most `m` components at `v ∉ S` of classes of `H²(G_S, D)` are killed by `m`. -/
theorem card_le_sDivisor_component [IsGalois K Ω] (ι : PlaceEmbeddings K Ω)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}) {m : ℕ} (hm : m ≠ 0)
    (s : Finset (cohomology (trivialModule
      Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K) (ULift.{u} ℤ)) 2))
    (hs : ∀ c ∈ s, m • c = 0 ∧
      ∃ d' : cohomology (divisorModule (outsideLocalizationHom S ι) (ULift.{u} ℤ)) 2,
        (map (outsideLocalizationHom S ι v)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom d' = c) :
    s.card ≤ m := by
  have := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
    (compactSpace_and_totallyDisconnectedSpace_localGal v.1).1
  have := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
    (compactSpace_and_totallyDisconnectedSpace_localGal v.1).2
  exact card_le_of_topologicallyCyclic (outsideLocalizationHom S ι) v hm
    (fun V hV => exists_generator_outsideLocalizationHom S ι v V hV) s hs

include hℓ hS in
/-- **Components of `ℓ`-primary divisor classes at one place.** For `v ∉ S` and a class `d` of
`H²(G_S, D)` killed by a power of `ℓ`, some class of `H²(G_S, K_Sˣ)` has a divisor class with the same
component as `d` at `v` and component zero at every other place outside `S`. The classes of
`exists_maximalUnits_component_family` realize `ℓ ^ n` distinct components killed by `ℓ ^ n`, and
there are at most `ℓ ^ n` such components (`card_le_sDivisor_component`). -/
theorem exists_unitsToSDivisor_component_eq (ι : PlaceEmbeddings K Ω)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (d : cohomology (divisorModule (outsideLocalizationHom S ι) (ULift.{u} ℤ)) 2) {n : ℕ}
    (hd : ℓ ^ n • d = 0) :
    ∃ z : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      (map (outsideLocalizationHom S ι v)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom z) = (map (outsideLocalizationHom S ι v)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) v) 2).hom d ∧
      ∀ w, w ≠ v → (map (outsideLocalizationHom S ι w)
          (divisorEval (outsideLocalizationHom S ι) (ULift.{u} ℤ) w) 2).hom
          ((coeffMap (unitsToSDivisor S ι) 2).hom z) = 0 := by
  obtain ⟨z, hΦ, hΦm, hz2⟩ := exists_maximalUnits_component_family S hℓ hS ι v n
  obtain ⟨k, hk⟩ := mem_range_of_card_le hΦ _
    (card_le_sDivisor_component S ι v (pow_ne_zero n hℓ.ne_zero))
    (fun k => ⟨hΦm k, _, rfl⟩) ⟨by rw [← map_nsmul, hd, map_zero], d, rfl⟩
  exact ⟨z k, hk, hz2 k⟩

include hℓ hS in
/-- **`ℓ`-primary divisor classes come from `K_Sˣ`.** Every class of `H²(G_S, D)` killed by a power
of `ℓ` is the divisor class of a class of `H²(G_S, K_Sˣ)`. -/
theorem exists_coeffMap_unitsToSDivisor_eq (ι : PlaceEmbeddings K Ω)
    (d : cohomology (sDivisorModule S ι) 2) {n : ℕ} (hd : ℓ ^ n • d = 0) :
    ∃ z : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) 2,
      (coeffMap (unitsToSDivisor S ι) 2).hom z = d := by
  classical
  have := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
    (compactSpace_and_totallyDisconnectedSpace_localGal v.1).1
  have := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
    (compactSpace_and_totallyDisconnectedSpace_localGal v.1).2
  have hfin := finite_divisorEval_ne_zero (outsideLocalizationHom S ι) (ULift.{u} ℤ) 2 d
  choose z hz1 hz2 using fun u => exists_unitsToSDivisor_component_eq S hℓ hS ι u d hd
  refine ⟨∑ u ∈ hfin.toFinset, z u, sub_eq_zero.1 ?_⟩
  refine eq_zero_of_divisorEval_eq_zero (outsideLocalizationHom S ι) _ fun u => ?_
  rw [map_sub, map_sum, map_sum, sub_eq_zero]
  by_cases hu : u ∈ hfin.toFinset
  · rw [Finset.sum_eq_single_of_mem u hu fun w _ hw => hz2 w u fun h => hw h.symm, hz1 u]
  · rw [Finset.sum_eq_zero fun w hw => hz2 w u fun h => hu (h ▸ hw)]
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hu
    exact hu.symm

/-- The divisor class of the class in `K_Sˣ/𝒪_Sˣ` of a class of `K_Sˣ` is its divisor class. -/
theorem coeffMap_unitsModSUnitsToSDivisor_mkQ (ι : PlaceEmbeddings K Ω) (n : ℕ)
    (z : cohomology (unitsModule K (maximalUnramifiedOutside K Ω S)) n) :
    (coeffMap (unitsModSUnitsToSDivisor S ι) n).hom
        ((coeffMap (sUnitsQuotSequence K Ω S).g n).hom z) =
      (coeffMap (unitsToSDivisor S ι) n).hom z := by
  rw [← mkQ_comp_unitsModSUnitsToSDivisor S ι]
  exact (congrArg (fun F => F.hom z) (coeffMap_comp (sUnitsQuotSequence K Ω S).g
    (unitsModSUnitsToSDivisor S ι) n)).symm

include hℓ hS in
/-- **`H³(G_S, 𝒪_Sˣ)(ℓ) = 0`.** A class of `H³(G_S, 𝒪_Sˣ)` killed by a power of `ℓ` is zero. -/
theorem eq_zero_of_cohomology_three_maximalSUnits
    (x : cohomology (maximalSUnitsModule K Ω S) 3) {k : ℕ} (hx : ℓ ^ k • x = 0) : x = 0 := by
  classical
  let ι : PlaceEmbeddings K Ω := Classical.arbitrary _
  have hS' := sUnitsQuotSequence_shortExact K Ω S
  have hf : (coeffMap (sUnitsToUnits S (maximalUnramifiedOutside K Ω S)) 3).hom x = 0 :=
    eq_zero_of_cohomology_three_maximalUnits S hℓ hS _ (k := k)
      (by rw [← map_nsmul, hx, map_zero])
  obtain ⟨p, hp'⟩ : ∃ p : cohomology (unitsModSUnitsModule K Ω S) 2, (δ hS' 2 3 rfl).hom p = x :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS' 2 3 rfl) x hf
  obtain ⟨p', ⟨j, hj⟩, hpp⟩ : ∃ p' : cohomology (unitsModSUnitsModule K Ω S) 2,
      (∃ j : ℕ, ℓ ^ j • p' = 0) ∧ (δ hS' 2 3 rfl).hom p' = (δ hS' 2 3 rfl).hom p :=
    exists_primary_map_eq (δ hS' 2 3 rfl).hom.toAddMonoidHom hℓ
      (isTorsion_cohomology _ (by norm_num) p) (k := k)
      (by
        change ℓ ^ k • (δ hS' 2 3 rfl).hom p = 0
        rw [hp']
        exact hx)
  set dd := (coeffMap (unitsModSUnitsToSDivisor S ι) 2).hom p' with hdd
  have hddj : ℓ ^ j • dd = 0 := by rw [hdd, ← map_nsmul, hj, map_zero]
  obtain ⟨y, hy⟩ := exists_coeffMap_unitsToSDivisor_eq S hℓ hS ι dd hddj
  obtain ⟨y', ⟨i, hi⟩, hyy⟩ := exists_primary_map_eq
    (coeffMap (unitsToSDivisor S ι) 2).hom.toAddMonoidHom hℓ
    (isTorsion_cohomology _ (by norm_num) y) (k := j)
    (by
      change ℓ ^ j • (coeffMap (unitsToSDivisor S ι) 2).hom y = 0
      rw [hy]
      exact hddj)
  have hy'' : (coeffMap (unitsToSDivisor S ι) 2).hom y' = dd := hyy.trans hy
  set gy : cohomology (unitsModSUnitsModule K Ω S) 2 :=
    (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom y' with hgy
  have hgy' : (coeffMap (unitsModSUnitsToSDivisor S ι) 2).hom gy = dd :=
    (coeffMap_unitsModSUnitsToSDivisor_mkQ S ι 2 y').trans hy''
  have hgyi : ℓ ^ i • gy = 0 := by
    have e := map_nsmul (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom (ℓ ^ i) y'
    have e0 : (coeffMap (sUnitsQuotSequence K Ω S).g 2).hom (ℓ ^ i • y') = 0 := by
      rw [hi]
      exact LinearMap.map_zero _
    exact e.symm.trans e0
  set q := p' - gy with hq
  have hq0 : (coeffMap (unitsModSUnitsToSDivisor S ι) 2).hom q = 0 := by
    rw [hq, map_sub, hgy', sub_self]
  obtain ⟨N, hN, hNq⟩ := exists_coprime_nsmul_of_coeffMap_sDivisor_eq_zero S ι hℓ hS q hq0
  have hqk : ℓ ^ (i + j) • q = 0 := by
    have h1 : ℓ ^ (i + j) • p' = 0 := by rw [pow_add, ← smul_smul, hj, smul_zero]
    have h2 : ℓ ^ (i + j) • gy = 0 := by rw [pow_add, mul_comm, ← smul_smul, hgyi, smul_zero]
    rw [hq, smul_sub, h1, h2, sub_zero]
  have hpq : p' = gy := sub_eq_zero.1 (eq_zero_of_coprime_nsmul_eq_zero hN hNq hqk)
  have hδ : (δ hS' 2 3 rfl).hom gy = 0 := by
    have e := congrArg (fun F => F.hom y') (comp_δ hS' 2 3 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, ModuleCat.hom_zero] at e
    exact e
  have h1 : (δ hS' 2 3 rfl).hom p' = 0 := by
    rw [hpq]
    exact hδ
  rw [← hp', ← hpp]
  exact h1

end DivisorClasses

end

end Langlands.GaloisCohomology
