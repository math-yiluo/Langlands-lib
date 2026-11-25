import Langlands.GaloisCohomology.Global.RealPlaces.VanishingDevissage
import Langlands.GaloisCohomology.Global.PoitouTate.LocalPairings
import Langlands.GaloisCohomology.Global.PoitouTate.EvenDuality
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.LocalUnits

/-!
# `H³(G_S, μ₂)` and the real places, through the `S`-units

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K` containing the
places above `2`, `G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω` and `μ₂ = μ₂(K_S)`.

**Theorem** (`bijective_realLocalization_dualizingModule_two`). The localization
`H³(G_S, μ₂) → ∏_{w real} H³(K_w, μ₂)` is bijective.

Proof. The Kummer sequence `0 → μ₂ → 𝒪_Sˣ → 𝒪_Sˣ → 0` of the `S`-units of `K_S`
(`sUnitsKummerSequence_shortExact`) gives `H²(G_S, 𝒪_Sˣ) → H³(G_S, μ₂) → H³(G_S, 𝒪_Sˣ)[2]`, and the
last group is zero (`eq_zero_of_cohomology_three_maximalSUnits`): every class of `H³(G_S, μ₂)` is the
connecting image of a class of `H²(G_S, 𝒪_Sˣ)`. At a real place `w` the Kummer sequence
`0 → μ₂ → K̄_wˣ → K̄_wˣ → 0` (`realKummerSequence`) has a bijective connecting map
`H²(K_w, K̄_wˣ) → H³(K_w, μ₂)` (`bijective_δ_realKummerSequence_two`): `H²(K_w, K̄_wˣ)` is killed by `2`
and `H³(K_w, K̄_wˣ) = 0` (`subsingleton_cohomology_three_unitsModule_of_isReal`: the group has order
`2`, so the cohomology is periodic, and Hilbert 90). The connecting maps commute with the
localization (`realLocalization_δ_kummer`), and the localization of `H²(G_S, 𝒪_Sˣ)` at `w` is the real
localization of its image in the Brauer group of `K` (`map_sUnitsRealHom_eq`). Then:

* surjectivity: a family of real local Brauer classes is the family of real localizations of a
  `2`-primary class of `H²(G_S, 𝒪_Sˣ)`, after choosing the local class at one place of `S` so that
  the sum of the invariants vanishes (`existsUnique_maximalSUnitsInflation_localization`);
* injectivity: a class of `H²(G_S, 𝒪_Sˣ)` whose real localizations vanish is divisible by `2`
  (`exists_two_nsmul_eq_of_realBrauerLocalization_eq_zero`: halve the local invariants keeping their
  sum zero, as in `exists_prime_nsmul_eq_cohomology_two_maximalSUnits`), and `H³(G_S, μ₂)` is killed
  by `2`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.GaloisCohomology.PoitouTate Langlands.ClassFieldTheory.Local
  Langlands.ClassFieldTheory.Global

universe u

noncomputable section

section RealKummer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (N : ℕ) [NeZero N]

/-- The coefficient map `𝒪_Sˣ → K̄_wˣ` of `ι` at an infinite place `w`. -/
def sUnitsRealHom (w : InfinitePlace K) :
    realLocalModule ι (maximalSUnitsModule K Ω S) w ⟶
      unitsModule w.Completion (AlgebraicClosure w.Completion) :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      ((Units.map (((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val :
        maximalUnramifiedOutside K Ω S →ₐ[K] AlgebraicClosure w.Completion) :
          maximalUnramifiedOutside K Ω S →* AlgebraicClosure w.Completion)).comp
        (maximalSUnits K Ω S).subtype)) :
      Additive (maximalSUnits K Ω S) →ₗ[ULift.{u} ℤ]
        Additive (AlgebraicClosure w.Completion)ˣ), fun σ => by
    ext x
    exact Units.ext (realLocalizationHom_apply ι S w σ
      (((Additive.toMul (show Additive (maximalSUnits K Ω S) from x) : maximalSUnits K Ω S) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S))⟩

/-- `sUnitsRealHom` is `ι.infinite w` on `S`-units. -/
theorem sUnitsRealHom_hom_apply (w : InfinitePlace K) (x : Additive (maximalSUnits K Ω S)) :
    (((Additive.toMul ((sUnitsRealHom ι S w).hom x) : (AlgebraicClosure w.Completion)ˣ)) :
        AlgebraicClosure w.Completion) =
      ι.infinite w ((((Additive.toMul x : maximalSUnits K Ω S) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) : Ω) :=
  rfl

/-- The Kummer sequence of the `S`-units, restricted to the Galois group of an infinite place, maps to
the Kummer sequence of `K̄_wˣ`. -/
def kummerRealMap (w : InfinitePlace K) :
    (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) N).map
        (Rep.resFunctor (realLocalizationHom ι S w :
          Gal(AlgebraicClosure w.Completion/w.Completion) →* GaloisGroupUnramifiedOutside K Ω S)) ⟶
      realKummerSequence ι S N w where
  τ₁ := 𝟙 _
  τ₂ := sUnitsRealHom ι S w
  τ₃ := sUnitsRealHom ι S w
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (N • 𝟙 (unitsModule w.Completion (AlgebraicClosure w.Completion))).hom
        ((sUnitsRealHom ι S w).hom x) =
      (sUnitsRealHom ι S w).hom ((N • 𝟙 (maximalSUnitsModule K Ω S)).hom x)
    rw [nsmul_id_hom_apply]
    exact (map_nsmul _ N x).symm.trans
      (congrArg (sUnitsRealHom ι S w).hom (nsmul_id_hom_apply (maximalSUnitsModule K Ω S) N x).symm)

variable {N}

/-- The connecting maps of the two Kummer sequences commute with the localization at `w`. -/
theorem realLocalization_δ_kummer (hNS : ∀ v ∉ S, ((N : ℕ) : 𝓞 K) ∉ v.asIdeal)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (w : InfinitePlace K) (r : ℕ) (y : cohomology (maximalSUnitsModule K Ω S) r) :
    have : IsSepClosed Ω := IsSepClosure.sep_closed K
    realLocalization ι (dualizingModule K Ω S N) w (r + 1)
        ((δ (sUnitsKummerSequence_shortExact (Ω := Ω) S N hNS) r (r + 1) rfl).hom y) =
      (δ (realKummerSequence_shortExact ι S N hS w) r (r + 1) rfl).hom
        ((map (realLocalizationHom ι S w) (sUnitsRealHom ι S w) r).hom y) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact congrArg (fun F => F.hom y)
    (δ_comp_map (realLocalizationHom ι S w) (kummerRealMap ι S N w)
      (sUnitsKummerSequence_shortExact (Ω := Ω) S N hNS) (realKummerSequence_shortExact ι S N hS w)
      r (r + 1) rfl)

end RealKummer

section Brauer

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The localization of `Hⁿ(G_S, 𝒪_Sˣ)` at an infinite place `w` is the localization at `w` of its
image in `Hⁿ(Gal(Ω/K), Ωˣ)`. -/
theorem map_sUnitsRealHom_eq (w : InfinitePlace K) (n : ℕ)
    (y : cohomology (maximalSUnitsModule K Ω S) n) :
    (map (realLocalizationHom ι S w) (sUnitsRealHom ι S w) n).hom y =
      realBrauerLocalization ι w n (maximalSUnitsInflation K Ω S n y) := by
  rw [maximalSUnitsInflation_apply, maximalUnitsInflation_apply, realBrauerLocalization,
    LinearMap.toAddMonoidHom_coe, map_coeffMap_hom_apply, map_map_apply]
  have hφ : (GaloisGroupUnramifiedOutside.quotientMap K Ω S).comp
      (decompositionHom w.Completion (ι.infinite w)) = realLocalizationHom ι S w :=
    ContinuousMonoidHom.ext fun σ => (realLocalizationHom_eq_quotientMap ι S w σ).symm
  rw [map_congr _ (sUnitsRealHom ι S w) hφ ?_ n]
  intro a
  rfl

end Brauer

section LocalReal

variable {K : Type u} [Field K] [NumberField K]

/-- At a real place, `H³(K_w, K̄_wˣ) = 0`: the Galois group has order `2`, so its cohomology is periodic,
and `H¹(K_w, K̄_wˣ) = 0` (Hilbert 90). -/
theorem subsingleton_cohomology_three_unitsModule_of_isReal (w : InfinitePlace K) (hw : w.IsReal) :
    Subsingleton (cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) 3) := by
  have hcard := card_closureGalois w hw
  have : Fact (Nat.card Gal(AlgebraicClosure w.Completion/w.Completion)).Prime :=
    ⟨by rw [hcard]; exact Nat.prime_two⟩
  have : Finite Gal(AlgebraicClosure w.Completion/w.Completion) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : IsCyclic Gal(AlgebraicClosure w.Completion/w.Completion) := isCyclic_of_prime_card rfl
  have h1 : Limits.IsZero (groupCohomology (unitsModule w.Completion
      (AlgebraicClosure w.Completion)) 1) :=
    isZero_cohomology_one_unitsModule.of_iso (isoGroupCohomology _ 1).symm
  have h3 := isZero_groupCohomology_odd (unitsModule w.Completion (AlgebraicClosure w.Completion))
    h1 3 (by decide)
  exact ModuleCat.subsingleton_of_isZero (h3.of_iso (isoGroupCohomology _ 3))

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (ι : PlaceEmbeddings K Ω)
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- At a real place the connecting map `H²(K_w, K̄_wˣ) → H³(K_w, μ₂)` of the Kummer sequence is
bijective. -/
theorem bijective_δ_realKummerSequence_two
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (w : InfinitePlace K) (hw : w.IsReal) :
    Function.Bijective (δ (realKummerSequence_shortExact ι S 2 hS w) 2 3 rfl).hom := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun t => ?_⟩
  · obtain ⟨z, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (cohomology_exact₃ (realKummerSequence_shortExact ι S 2 hS w) 2 3 rfl) y hy
    have key : ∀ z : cohomology (unitsModule w.Completion (AlgebraicClosure w.Completion)) 2,
        (coeffMap (2 • 𝟙 (unitsModule w.Completion (AlgebraicClosure w.Completion))) 2).hom z = 0 :=
      fun z => by
        rw [cohomologyMap_nsmul_id_apply]
        exact two_nsmul_cohomology_closureGalois w hw _ (by norm_num) z
    exact key z
  · exact (ShortComplex.moduleCat_exact_iff _).1
      (cohomology_exact₁ (realKummerSequence_shortExact ι S 2 hS w) 2 3 rfl) t
      (@Subsingleton.elim _ (subsingleton_cohomology_three_unitsModule_of_isReal w hw) _ _)

end LocalReal

section Divisible

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The classes of `H²(G_S, 𝒪_Sˣ)` whose image in the Brauer group of `K` vanishes at the infinite
places. -/
def realTrivialSUnitsClasses : AddSubgroup (cohomology (maximalSUnitsModule K Ω S) 2) where
  carrier := {y | ∀ w : InfinitePlace K,
    realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 y) = 0}
  add_mem' {a b} ha hb w := by rw [map_add, map_add, ha w, hb w, add_zero]
  zero_mem' w := by rw [map_zero, map_zero]
  neg_mem' {a} ha w := by rw [map_neg, map_neg, ha w, neg_zero]

theorem mem_realTrivialSUnitsClasses_iff (y : cohomology (maximalSUnitsModule K Ω S) 2) :
    y ∈ realTrivialSUnitsClasses ι S ↔
      ∀ w : InfinitePlace K, realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 y) = 0 :=
  Iff.rfl

/-- **Divisibility by `2` away from the real places.** If `S` contains the places above `2`, a class of
`H²(G_S, 𝒪_Sˣ)` whose image in the Brauer group of `K` vanishes at the infinite places is divisible by
`2` (within these classes). -/
theorem exists_two_nsmul_eq_of_realBrauerLocalization_eq_zero
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (y : realTrivialSUnitsClasses ι S) : ∃ y', 2 • y' = y := by
  classical
  have hℓ : Nat.Prime 2 := Nat.prime_two
  refine exists_prime_nsmul_eq_of_primary hℓ (fun y => ?_) (fun y₁ ⟨k, hk⟩ => ?_) y
  · obtain ⟨m, hm, hmy⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1
      (isTorsion_cohomology (maximalSUnitsModule K Ω S) (by norm_num) y.1)
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm, Subtype.ext hmy⟩
  have hk' : 2 ^ k • y₁.1 = 0 := congrArg Subtype.val hk
  set x := maximalSUnitsInflation K Ω S 2 y₁.1 with hxdef
  have hxk : 2 ^ k • x = 0 := by rw [hxdef, ← map_nsmul, hk', map_zero]
  have hreal : ∀ w, realBrauerLocalization ι w 2 x = 0 := y₁.2
  by_cases hx0 : x = 0
  · refine ⟨0, Subtype.ext ?_⟩
    rw [smul_zero]
    exact (eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ h2 y₁.1 hk' hx0).symm
  -- a finite place where `x` is nonzero; it lies in `S`
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, brauerLocalization ι v₀ 2 x ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx0 (eq_zero_of_brauerLocalization_eq_zero' ι x hne hreal)
  have hv₀S : v₀ ∈ S := by
    by_contra h
    exact hv₀ (brauerLocalization_maximalSUnitsInflation_eq_zero S ι h y₁.1)
  -- divide the local invariants by `2`, keeping the sum zero
  let r : HeightOneSpectrum (𝓞 K) → RationalModIntegers := fun v => localInvariant ι v x
  have hrk : ∀ v, 2 ^ k • r v = 0 := fun v => by
    simp only [r]
    rw [← map_nsmul, hxk, map_zero]
  choose r' hr'1 hr'2 hr'3 using fun v => exists_rationalModIntegers_nsmul_eq hℓ.ne_zero (r v) (hrk v)
  obtain ⟨hfin, hsum⟩ := localInvariant_finite_support_and_sum_eq_zero ι x
  have hreal' : ∑ w, realLocalInvariant ι w x = 0 :=
    Finset.sum_eq_zero fun w _ => by rw [realLocalInvariant, hreal w, realInvariant_zero]
  rw [hreal', add_zero] at hsum
  have hfin' : (Function.support r').Finite := hfin.subset fun v hv h0 => hv (hr'3 v h0)
  set c := ∑ᶠ v, r' v with hc
  have hcℓ : 2 • c = 0 := by
    rw [hc, smul_finsum' 2 hfin']
    simp only [hr'1]
    exact hsum
  let δ₀ : HeightOneSpectrum (𝓞 K) → RationalModIntegers := fun v => if v = v₀ then c else 0
  have hδfin : (Function.support δ₀).Finite :=
    (Set.finite_singleton v₀).subset fun v hv => by
      by_contra h
      exact hv (ite_eq_right_of_eq_false _ _ (eq_false h))
  let r'' : HeightOneSpectrum (𝓞 K) → RationalModIntegers := fun v => r' v - δ₀ v
  have hfin'' : (Function.support r'').Finite :=
    (hfin'.union hδfin).subset (Function.support_sub _ _)
  have hsum'' : ∑ᶠ v, r'' v = 0 := by
    rw [finsum_sub_distrib hfin' hδfin,
      finsum_eq_single δ₀ v₀ fun v hv => ite_eq_right_of_eq_false _ _ (eq_false hv), ← hc]
    simp [δ₀]
  have hδℓ : ∀ v, 2 • δ₀ v = 0 := fun v => by
    simp only [δ₀]
    split_ifs
    · exact hcℓ
    · exact smul_zero _
  obtain ⟨x', hx'1, hx'2⟩ := exists_localInvariant_eq ι r'' hfin'' hsum''
  -- `2 x' = x`
  have hℓx' : 2 • x' = x := by
    refine sub_eq_zero.1 (eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_))
    · rw [← localInvariant_eq_zero_iff, map_sub, map_nsmul, hx'1 v]
      simp only [r'', smul_sub, hr'1, hδℓ, sub_zero, r, sub_self]
    · rw [map_sub, map_nsmul, hx'2 w, hreal w, smul_zero, sub_zero]
  -- `x'` is killed by `2 ^ (k + 1)` and vanishes outside `S`
  have hx'k : 2 ^ (k + 1) • x' = 0 := by
    refine eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_)
    · rw [← localInvariant_eq_zero_iff, map_nsmul, hx'1 v]
      simp only [r'', smul_sub, hr'2, zero_sub, neg_eq_zero]
      rw [pow_succ, ← smul_smul, hδℓ, smul_zero]
    · rw [map_nsmul, hx'2 w, smul_zero]
  have hx'S : ∀ v, v ∉ S → brauerLocalization ι v 2 x' = 0 := by
    intro v hv
    rw [← localInvariant_eq_zero_iff, hx'1 v]
    have hrv : r v = 0 := by
      simp only [r]
      rw [localInvariant_eq_zero_iff]
      exact brauerLocalization_maximalSUnitsInflation_eq_zero S ι hv y₁.1
    have hvv : v ≠ v₀ := fun h => hv (h ▸ hv₀S)
    simp only [r'', δ₀, hvv, ↓reduceIte, hr'3 v hrv, sub_zero]
  obtain ⟨y', ⟨j, hj⟩, hy'⟩ := exists_maximalSUnitsInflation_eq S hℓ h2 ι x' hx'k hx'S
  have hy'Z : y' ∈ realTrivialSUnitsClasses ι S := fun w => by rw [hy', hx'2 w]
  refine ⟨⟨y', hy'Z⟩, Subtype.ext ?_⟩
  refine sub_eq_zero.1 (eq_zero_of_maximalSUnitsInflation_eq_zero S hℓ h2 _ (k := j + k) ?_ ?_)
  · have h1 : 2 ^ (j + k) • 2 • y' = 0 := by
      rw [smul_comm, pow_add, mul_comm, ← smul_smul, hj, smul_zero, smul_zero]
    have h2' : 2 ^ (j + k) • y₁.1 = 0 := by rw [pow_add, ← smul_smul, hk', smul_zero]
    change 2 ^ (j + k) • (2 • y' - y₁.1) = 0
    rw [smul_sub, h1, h2', sub_zero]
  · change maximalSUnitsInflation K Ω S 2 (2 • y' - y₁.1) = 0
    rw [map_sub, map_nsmul, hy', hℓx', sub_self]

end Divisible

section DegreeThree

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))
  (h2 : ∀ v : HeightOneSpectrum (𝓞 K), ((2 : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hK : (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) 2).ShortExact)

include h2 in
/-- Every class of `H³(G_S, μ₂)` is the connecting image of a class of `H²(G_S, 𝒪_Sˣ)`. -/
theorem exists_δ_kummer_eq (x : cohomology (dualizingModule K Ω S 2) 3) :
    ∃ y : cohomology (maximalSUnitsModule K Ω S) 2, (δ hK 2 3 rfl).hom y = x := by
  have hx : 2 • x = 0 := nsmul_cohomology_eq_zero _ (nsmul_dualizingModule S 2) 3 x
  have hf : (map (.id _) (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) 2).f 3).hom x =
      0 := by
    refine eq_zero_of_cohomology_three_maximalSUnits S Nat.prime_two h2 _ (k := 1) ?_
    rw [pow_one]
    exact (map_nsmul _ 2 x).symm.trans ((congrArg _ hx).trans (map_zero _))
  exact (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hK 2 3 rfl) x hf

/-- The real localization of a connecting image, through the Brauer group of `K`. -/
theorem realLocalization_δ_kummer_eq (w : InfinitePlace K)
    (y : cohomology (maximalSUnitsModule K Ω S) 2) :
    realLocalization ι (dualizingModule K Ω S 2) w 3 ((δ hK 2 3 rfl).hom y) =
      (δ (realKummerSequence_shortExact ι S 2 h2 w) 2 3 rfl).hom
        (realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 y)) := by
  rw [← map_sUnitsRealHom_eq]
  exact realLocalization_δ_kummer ι S (fun v hv h => hv (h2 v h)) h2 w 2 y

include h2 in
/-- A connecting image whose real localizations vanish is zero. -/
theorem δ_kummer_eq_zero (y : cohomology (maximalSUnitsModule K Ω S) 2)
    (hy : ∀ w : InfinitePlace K, w.IsReal →
      realLocalization ι (dualizingModule K Ω S 2) w 3 ((δ hK 2 3 rfl).hom y) = 0) :
    (δ hK 2 3 rfl).hom y = 0 := by
  have hyZ : y ∈ realTrivialSUnitsClasses ι S := by
    intro w
    by_cases hw : w.IsReal
    · have e : (δ (realKummerSequence_shortExact ι S 2 h2 w) 2 3 rfl).hom
          (realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 y)) = 0 :=
        (realLocalization_δ_kummer_eq ι S h2 hK w y).symm.trans (hy w hw)
      exact (injective_iff_map_eq_zero _).1 (bijective_δ_realKummerSequence_two ι S h2 w hw).1 _ e
    · have := subsingleton_realBrauerGroup_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.1 hw)
      exact Subsingleton.elim _ _
  obtain ⟨y', hy'⟩ := exists_two_nsmul_eq_of_realBrauerLocalization_eq_zero ι S h2 ⟨y, hyZ⟩
  have hy'' : 2 • y'.1 = y := congrArg Subtype.val hy'
  have e1 : (δ hK 2 3 rfl).hom y = 2 • (δ hK 2 3 rfl).hom y'.1 :=
    (congrArg (δ hK 2 3 rfl).hom hy''.symm).trans (map_nsmul _ 2 y'.1)
  rw [e1]
  exact nsmul_cohomology_eq_zero _ (nsmul_dualizingModule S 2) 3 _

include h2 in
/-- Every family of real local Brauer classes is the family of real localizations of the image in the
Brauer group of `K` of a class of `H²(G_S, 𝒪_Sˣ)`. -/
theorem exists_realBrauerLocalization_maximalSUnitsInflation_eq
    (b : ∀ w : {w : InfinitePlace K // w.IsReal}, RealBrauerGroup w.1) :
    ∃ y : cohomology (maximalSUnitsModule K Ω S) 2, ∀ w : {w : InfinitePlace K // w.IsReal},
      realBrauerLocalization ι w.1 2 (maximalSUnitsInflation K Ω S 2 y) = b w := by
  classical
  let b' : ∀ w : InfinitePlace K, RealBrauerGroup w := fun w =>
    if hw : w.IsReal then b ⟨w, hw⟩ else 0
  have hb' : ∀ w : {w : InfinitePlace K // w.IsReal}, b' w.1 = b w := fun w => by simp [b', w.2]
  obtain ⟨v₀⟩ := nonempty_of_natCast_mem (N := 2) (by norm_num) h2
  let c : RationalModIntegers := -∑ w, realInvariant w (b' w)
  let a : ∀ v : HeightOneSpectrum (𝓞 K), LocalBrauerGroup v :=
    Pi.single (M := fun v => LocalBrauerGroup v) v₀.1 ((finiteInvariant v₀.1).symm c)
  have ha0 : ∀ v, v ≠ v₀.1 → a v = 0 := fun v hv => Pi.single_eq_of_ne hv _
  have hav : a v₀.1 = (finiteInvariant v₀.1).symm c := Pi.single_eq_same _ _
  have h2inv : ∀ w, 2 • realInvariant w (b' w) = 0 := fun w => by
    rw [← realInvariantHom_apply, ← map_nsmul, two_nsmul_realBrauerGroup, map_zero]
  have h2c : 2 • c = 0 := by
    simp only [c, smul_neg, Finset.smul_sum, h2inv, Finset.sum_const_zero, neg_zero]
  have hfa : ∀ v, finiteInvariant v (a v) = if v = v₀.1 then c else 0 := fun v => by
    by_cases hv : v = v₀.1
    · subst hv
      simp [hav]
    · rw [ha0 v hv, map_zero]
      simp [hv]
  obtain ⟨y, ⟨-, hyb⟩, -⟩ := existsUnique_maximalSUnitsInflation_localization S Nat.prime_two h2 ι
    a b' ((Set.finite_singleton v₀.1).subset fun v hv => by
      by_contra h
      exact hv (ha0 v h))
    (fun v hv => ha0 v fun h => hv (h ▸ v₀.2)) (k := 1)
    (fun v => by
      by_cases hv : v = v₀.1
      · subst hv
        rw [pow_one, hav, ← map_nsmul, h2c, map_zero]
      · rw [ha0 v hv, smul_zero])
    (fun w => by rw [pow_one, two_nsmul_realBrauerGroup])
    (by
      rw [finsum_congr hfa, finsum_eq_single _ v₀.1 fun v hv => by simp [hv]]
      simp [c])
  exact ⟨y.1, fun w => (hyb w.1).trans (hb' w)⟩

include h2 in
/-- **`H³(G_S, μ₂)` and the real places.** If `S` contains the places above `2`, the localization
`H³(G_S, μ₂) → ∏_{w real} H³(K_w, μ₂)` is bijective. -/
theorem bijective_realLocalization_dualizingModule_two :
    Function.Bijective fun (x : cohomology (dualizingModule K Ω S 2) 3)
      (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι (dualizingModule K Ω S 2) w.1 3 x := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hK := sUnitsKummerSequence_shortExact (Ω := Ω) S 2 fun v hv h => hv (h2 v h)
  refine ⟨fun x x' hxx' => ?_, fun t => ?_⟩
  · rw [← sub_eq_zero]
    obtain ⟨y, hy⟩ := exists_δ_kummer_eq S h2 hK (x - x')
    rw [← hy]
    refine δ_kummer_eq_zero ι S h2 hK y fun w hw => ?_
    rw [hy, map_sub, sub_eq_zero]
    exact congrFun hxx' ⟨w, hw⟩
  · choose b hb using fun w : {w : InfinitePlace K // w.IsReal} =>
      (bijective_δ_realKummerSequence_two ι S h2 w.1 w.2).2 (t w)
    obtain ⟨y, hy⟩ := exists_realBrauerLocalization_maximalSUnitsInflation_eq ι S h2 b
    refine ⟨(δ hK 2 3 rfl).hom y, funext fun w => ?_⟩
    exact (realLocalization_δ_kummer_eq ι S h2 hK w.1 y).trans ((congrArg _ (hy w)).trans (hb w))

end DegreeThree

end

end Langlands.GaloisCohomology
