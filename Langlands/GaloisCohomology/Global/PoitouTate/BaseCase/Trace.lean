import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.LocalPairings
import Langlands.GaloisCohomology.Field.Hilbert90

/-!
# The base case: the trace is an isomorphism

For `n = ℓᵏ` a prime power, `S` finite containing the places above `ℓ`, `n` odd or `K` totally complex,
the trace `finiteTrace : H_c³(G_S, μ_n) → ℤ/n` is bijective (`bijective_finiteTrace`). It is onto
because the local invariants are (`surjective_finiteTrace`). It is injective because a family of
classes `ξ_v ∈ H²(K_v, μ_n)`, `v ∈ S`, with sum of invariants zero comes from `H²(G_S, μ_n)`: the
Brauer classes of the `ξ_v` (injective images, by Hilbert 90 and the local Kummer sequence,
`injective_coeffMap_rootsOfUnityLocalHom_two`) are the localizations of a class of
`H²(G_S, 𝒪_{K_S,S}ˣ)` killed by `n` (`existsUnique_maximalSUnitsInflation_localization`), which comes
from `H²(G_S, μ_n)` by the Kummer sequence of the `S`-units (`sUnitsKummerSequence_shortExact`).
-/

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]

/-- `H²(K_v, μ_n) → Br(K_v)` is injective (Hilbert 90). -/
theorem injective_coeffMap_rootsOfUnityLocalHom_two
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (coeffMap (rootsOfUnityLocalHom ι S n v) 2).hom := by
  have : IsSmoothRep (localKummerSequence ι S n v).X₁ :=
    inferInstanceAs (IsSmoothRep (localModule ι (dualizingModule K Ω S n) v))
  have : IsSmoothRep (localKummerSequence ι S n v).X₂ :=
    inferInstanceAs (IsSmoothRep
      (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))))
  have : IsSmoothRep (localKummerSequence ι S n v).X₃ :=
    inferInstanceAs (IsSmoothRep
      (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))))
  have h1 : Subsingleton (cohomology (localKummerSequence ι S n v).X₃ 1) :=
    subsingleton_cohomology_one_unitsModule (K := v.adicCompletion K)
      (L := AlgebraicClosure (v.adicCompletion K))
  exact cohomologyMap_f_injective_of_subsingleton (localKummerSequence_shortExact ι S n hS v) 1 h1

variable [Finite S]

/-- **The trace is injective** for `n = ℓᵏ`. -/
theorem injective_finiteTrace {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : k ≠ 0) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) : Function.Injective (finiteTrace ι S n hK) := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  have hℓS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv =>
    hS v (by
      rw [hnk, Nat.cast_pow]
      exact v.asIdeal.pow_mem_of_mem hv k (Nat.pos_of_ne_zero hk))
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine (surjective_ptLocalToCompact_two ι S n hK hS z).elim fun ξ hξ => ?_
  rw [← hξ] at hz ⊢
  have hsum : ∑ v : S, invariantAt ι S n v.1 (ξ v) = 0 := by
    rw [← isFiniteTrace_finiteTrace ι S n hK ξ, hz, map_zero]
  -- The family of local Brauer classes.
  let a : ∀ v : HeightOneSpectrum (𝓞 K), LocalBrauerGroup v := fun v =>
    if hv : v ∈ S then (coeffMap (rootsOfUnityLocalHom ι S n v) 2).hom (ξ ⟨v, hv⟩) else 0
  have haS : ∀ v, v ∉ S → a v = 0 := fun v hv => dite_eq_right_iff.2 fun h => absurd h hv
  have ha : {v | a v ≠ 0}.Finite := (Set.toFinite S).subset fun v hv => by
    by_contra h
    exact hv (haS v h)
  have hak : ∀ v, ℓ ^ k • a v = 0 := fun v => by
    rw [← hnk]
    by_cases hv : v ∈ S
    · have h0 := nsmul_cohomology_eq_zero (localModule ι (dualizingModule K Ω S n) v)
        (fun d => nsmul_dualizingModule S n d) 2 (ξ ⟨v, hv⟩)
      change n • (if hv : v ∈ S then _ else 0) = 0
      rw [dite_eq_left_of_eq_true (eq_true hv), ← map_nsmul]
      exact (congrArg (coeffMap (rootsOfUnityLocalHom ι S n v) 2).hom h0).trans (map_zero _)
    · rw [haS v hv, smul_zero]
  have hab : ∑ᶠ v, finiteInvariant v (a v) +
      ∑ w, realInvariant w ((0 : ∀ w : InfinitePlace K, RealBrauerGroup w) w) = 0 := by
    have hsupp : Function.support (fun v => finiteInvariant v (a v)) ⊆ S := fun v hv => by
      by_contra hvS
      exact hv (show finiteInvariant v (a v) = 0 by rw [haS v hvS, map_zero])
    have hfin : ∑ᶠ v, finiteInvariant v (a v) = ∑ v : S, finiteInvariant v.1 (a v.1) := by
      rw [finsum_eq_sum_of_support_subset _ (s := S.toFinset) (by simpa using hsupp)]
      exact (Finset.sum_subtype S.toFinset (fun a => by simp) _).trans rfl
    rw [hfin, Finset.sum_eq_zero fun w _ => realInvariant_zero_apply w, add_zero]
    have e : ∀ v : S, finiteInvariant v.1 (a v.1) =
        QZ.toRationalModIntegers (invariantAt ι S n v.1 (ξ v)) := fun v => by
      rw [invariantAt_apply, AddEquiv.apply_symm_apply]
      change finiteInvariant v.1 (if hv : v.1 ∈ S then _ else 0) = _
      rw [dite_eq_left_of_eq_true (eq_true v.2)]
    rw [Finset.sum_congr rfl fun v _ => e v, ← map_sum, hsum, map_zero]
  obtain ⟨y, hy, -⟩ := existsUnique_maximalSUnitsInflation_localization S hℓ hℓS ι a 0 ha haS hak
    (fun w => smul_zero _) hab
  -- `y` is killed by `n`, by uniqueness.
  have hny : n • (y : cohomology (maximalSUnitsModule K Ω S) 2) = 0 := by
    have hu := existsUnique_maximalSUnitsInflation_localization S hℓ hℓS ι 0 0
      (by simp) (fun _ _ => rfl) (k := k) (fun _ => smul_zero _) (fun _ => smul_zero _)
      (by simp only [Pi.zero_apply, map_zero, finsum_zero, zero_add]
          exact Finset.sum_eq_zero fun w _ => realInvariant_zero_apply w)
    have h1 : n • y = 0 := hu.unique (y₁ := n • y) (y₂ := 0)
      ⟨fun v => by
        change brauerLocalization ι v 2 (maximalSUnitsInflation K Ω S 2 (n • (y : _))) = 0
        rw [map_nsmul, map_nsmul, hy.1 v, hnk]
        exact hak v,
       fun w => by
        change realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 (n • (y : _))) = 0
        rw [map_nsmul, map_nsmul, hy.2 w, Pi.zero_apply, smul_zero]⟩
      ⟨fun v => by
        change brauerLocalization ι v 2 (maximalSUnitsInflation K Ω S 2 0) = 0
        rw [map_zero, map_zero],
       fun w => by
        change realBrauerLocalization ι w 2 (maximalSUnitsInflation K Ω S 2 0) = 0
        rw [map_zero, map_zero]⟩
    exact congrArg Subtype.val h1
  -- `y` comes from `H²(G_S, μ_n)`.
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hKum := sUnitsKummerSequence_shortExact (Ω := Ω) S n hnS
  obtain ⟨x, hx⟩ := exists_cohomologyMap_f_eq hKum 2 (y : cohomology (maximalSUnitsModule K Ω S) 2)
    ((cohomologyMap_nsmul_id_apply _ n 2 _).trans hny)
  have hloc : (ptGlobalToLocal (localFamily ι S) (dualizingModule K Ω S n) 2).hom x = ξ := by
    funext v
    apply injective_coeffMap_rootsOfUnityLocalHom_two ι S n hS v.1
    calc (coeffMap (rootsOfUnityLocalHom ι S n v.1) 2).hom
          (localization ι (dualizingModule K Ω S n) v.1 2 x)
        = brauerLocalization ι v.1 2 (brauerClass Ω S n x) :=
          (brauerLocalization_brauerClass ι S n v.1 x).symm
      _ = brauerLocalization ι v.1 2 (maximalSUnitsInflation K Ω S 2
          ((coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) n) 2).hom x)) :=
          congrArg _ (brauerClass_eq_maximalSUnitsInflation S n x)
      _ = brauerLocalization ι v.1 2 (maximalSUnitsInflation K Ω S 2
          (y : cohomology (maximalSUnitsModule K Ω S) 2)) := congrArg _ (congrArg _ hx)
      _ = a v.1 := hy.1 v.1
      _ = _ := dite_eq_left_of_eq_true (eq_true v.2)
  rw [← hloc]
  exact ((ptExact_local (localFamily ι S) (dualizingModule K Ω S n) 2)
    ((ptGlobalToLocal (localFamily ι S) (dualizingModule K Ω S n) 2).hom x)).2 ⟨x, rfl⟩

/-- **The trace is bijective** for `n = ℓᵏ`, `k ≥ 1`. -/
theorem bijective_finiteTrace {ℓ k : ℕ} (hℓ : ℓ.Prime) (hk : k ≠ 0) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) : Function.Bijective (finiteTrace ι S n hK) :=
  ⟨injective_finiteTrace ι S n hℓ hk hnk hS hK, surjective_finiteTrace ι S n hK (by
    rw [hnk]
    exact (Nat.one_lt_pow hk hℓ.one_lt).ne') hS⟩

end

end Langlands.GaloisCohomology.PoitouTate.Internal
