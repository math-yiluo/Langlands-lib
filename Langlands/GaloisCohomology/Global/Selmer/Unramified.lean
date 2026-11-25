import Langlands.GaloisCohomology.Global.Selmer.GreenbergWilesProof
import Langlands.GaloisCohomology.Local.Unramified

/-!
# The unramified condition

Let `K` be a number field, `S` a finite set of finite places, `G_S = Gal(K_S/K)`, `M` a smooth
`G_S`-module and `v` a finite place. The unramified condition at `v` is the subgroup
`H¹_ur(K_v, M) ⊆ H¹(K_v, M)` of the classes that vanish on the inertia subgroup of
`Gal(K̄_v/K_v)`: the unramified classes `Local.unramifiedClasses` of
`Langlands.GaloisCohomology.Local.Unramified` for the local field `K_v = v.adicCompletion K`,
applied to `localModule ι M v` (`unramifiedCondition`). Transported from the local theory:

* for `M` finite, `#H¹_ur(K_v, M) = #H⁰(K_v, M)` (`card_unramifiedCondition`), so that an unramified
  condition contributes the factor `1` to the formula of Greenberg and Wiles;
* for `N ≥ 1` killing `M`, `S` containing the places above `N`, `v ∈ S` and `#M` a unit at `v`, the
  orthogonal complement of `H¹_ur(K_v, M)` under the local pairing is `H¹_ur(K_v, M')`,
  `M' = Hom(M, μ_N)` (`rightOrthogonal_unramifiedCondition`; from
  `Local.mem_unramifiedClasses_cartierDual_iff` through the isomorphism of `M'` with the Cartier
  dual, which respects the unramified classes, `coeffMap_mem_unramifiedClasses_iff` of
  `Langlands.GaloisCohomology.Local.Unramified`); so the dual
  of a family of conditions that is unramified at `v` is unramified at `v`
  (`LocalConditions.dual_finite_eq_unramifiedCondition`).

The formula of Greenberg and Wiles then only involves the places of `S` at which the condition is
not the unramified one (`LocalConditions.card_selmerGroup_div_card_selmerGroup_dual_of_unramified`).
For the zero family it reads
`#Ш¹_S(M) / #H¹(G_S, M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #H⁰(K_v, M)⁻¹
· ∏_{w real} #H⁰(K_w, M)⁻¹ / (#M)^{r₂}` (`card_sha_one_div_card_cohomology_one_dual`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum ValuativeRel PoitouTate

universe u

noncomputable section

section Residue

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- An integer that is a unit at `v` is a unit of `𝒪_v`. -/
theorem isUnit_natCast_adicCompletionIntegers {m : ℕ} (hm : ((m : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    IsUnit ((m : ℕ) : v.adicCompletionIntegers K) := by
  rw [(adicCompletionIntegers.integers K v).isUnit_iff_valuation_eq_one]
  have h := Langlands.ClassFieldTheory.Global.valued_algebraMap_adicCompletion v (m : 𝓞 K)
  rw [map_natCast] at h
  push_cast
  rw [h, intValuation_eq_one_iff]
  exact hm

/-- An integer that is a unit at `v` is prime to the residue characteristic of `K_v`. -/
theorem coprime_ringChar_of_natCast_not_mem {m : ℕ} (hm : ((m : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    letI := Langlands.Global.FiniteCompletion.valuativeRel v
    m.Coprime (ringChar 𝓀[v.adicCompletion K]) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  let e := RingEquiv.subringCongr (integer_eq_adicCompletionIntegers v)
  have hunit : IsUnit ((m : ℕ) : 𝒪[v.adicCompletion K]) := by
    rw [← isUnit_map_iff e, map_natCast]
    exact isUnit_natCast_adicCompletionIntegers v hm
  have hk : ((m : ℕ) : 𝓀[v.adicCompletion K]) ≠ 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪[v.adicCompletion K]), Ne,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hunit
  have hp := CharP.char_ne_zero_of_finite 𝓀[v.adicCompletion K] (ringChar 𝓀[v.adicCompletion K])
  have hprime : (ringChar 𝓀[v.adicCompletion K]).Prime :=
    (CharP.char_is_prime_or_zero 𝓀[v.adicCompletion K] _).resolve_right hp
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hprime, ← ringChar.spec]
  exact hk

end Residue

section Condition

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]

/-- The unramified condition `H¹_ur(K_v, M) ⊆ H¹(K_v, M)` at a finite place `v`: the classes that
vanish on the inertia subgroup of `Gal(K̄_v/K_v)` (`Local.unramifiedClasses` for `K_v`). -/
def unramifiedCondition (v : HeightOneSpectrum (𝓞 K)) :
    AddSubgroup (cohomology (localModule ι M v) 1) :=
  letI := Langlands.Global.FiniteCompletion.valuativeRel v
  haveI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  Local.unramifiedClasses (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
    (localModule ι M v)

/-- A class is unramified exactly when its restriction to the inertia subgroup vanishes. -/
theorem mem_unramifiedCondition_iff (v : HeightOneSpectrum (𝓞 K))
    (x : cohomology (localModule ι M v) 1) :
    letI := Langlands.Global.FiniteCompletion.valuativeRel v
    haveI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
    x ∈ unramifiedCondition ι M v ↔
      (res (localModule ι M v) (Local.inertia (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))) 1).hom x = 0 :=
  Iff.rfl

/-- **The order of the unramified condition**: `#H¹_ur(K_v, M) = #H⁰(K_v, M)`. -/
theorem card_unramifiedCondition [Finite M] (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (unramifiedCondition ι M v) = Nat.card (cohomology (localModule ι M v) 0) := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  have h := Local.card_unramifiedClasses (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K)) (localModule ι M v)
  rw [Nat.card_congr (zeroIso (localModule ι M v)).toLinearEquiv.toEquiv]
  exact h

variable (N : ℕ) [NeZero N] [Finite M]

/-- **The orthogonal complement of the unramified condition** at a place `v ∈ S` at which `#M` is a
unit is the unramified condition of `M' = Hom(M, μ_N)`. -/
theorem rightOrthogonal_unramifiedCondition
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (v : S) (hv : ((Nat.card M : ℕ) : 𝓞 K) ∉ v.1.asIdeal) :
    rightOrthogonal (localPairing ι N M v) (unramifiedCondition ι M v) =
      unramifiedCondition ι (PoitouTate.dual N M) v := by
  let := Langlands.Global.FiniteCompletion.valuativeRel v.1
  have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v.1
  let e := dualIsoCartierDual ι N M hS hM v.1
  ext y
  rw [mem_rightOrthogonal]
  change _ ↔ y ∈ Local.unramifiedClasses _ _ (localModule ι (PoitouTate.dual N M) v.1)
  rw [← coeffMap_mem_unramifiedClasses_iff e, Local.mem_unramifiedClasses_cartierDual_iff _
    (coprime_ringChar_of_natCast_not_mem v.1 hv)]
  refine forall₂_congr fun x _ => ?_
  rw [localPairing_eq, ptLocalPairing_eq_localTatePairing, AddEquiv.map_eq_zero_iff]
  rfl

end Condition

namespace LocalConditions

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ι : PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M] [Finite M]

omit [Finite S] in
/-- If a family of conditions is unramified at `v ∈ S` and `#M` is a unit at `v`, its dual family is
unramified at `v`. -/
theorem dual_finite_eq_unramifiedCondition
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) {v : S}
    (hL : L.finite v = unramifiedCondition ι M v) (hv : ((Nat.card M : ℕ) : 𝓞 K) ∉ v.1.asIdeal) :
    (L.dual N).finite v = unramifiedCondition ι (PoitouTate.dual N M) v := by
  rw [dual_finite, hL, rightOrthogonal_unramifiedCondition ι M N hS hM v hv]

/-- **The formula of Greenberg and Wiles over the places where the condition is not the unramified
one**: if `L_v = H¹_ur(K_v, M)` for the places `v ∈ S` outside a finite set `T`,
`#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ T} #L_v / #H⁰(K_v, M)
· ∏_{w real} #L_w / #H⁰(K_w, M) / (#M)^{r₂}`. -/
theorem card_selmerGroup_div_card_selmerGroup_dual_of_unramified
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) (L : LocalConditions ι M) (T : Finset S)
    (hT : ∀ v : S, v ∉ T → L.finite v = unramifiedCondition ι M v) :
    (Nat.card L.selmerGroup : ℚ) / Nat.card (L.dual N).selmerGroup =
      (Nat.card (cohomology M 0) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 0) *
        (∏ v ∈ T, (Nat.card (L.finite v) : ℚ) / Nat.card (cohomology (localModule ι M v) 0)) *
        (∏ w : {w : InfinitePlace K // w.IsReal},
          (Nat.card (L.real w) : ℚ) / Nat.card (cohomology (realLocalModule ι M w.1) 0)) /
        (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K := by
  let _ : Fintype S := Fintype.ofFinite S
  rw [L.card_selmerGroup_div_card_selmerGroup_dual hS hM]
  congr 3
  refine (Finset.prod_subset (Finset.subset_univ T) fun v _ hv => ?_).symm
  have := finite_cohomology_localModule ι M v 0
  rw [hT v hv, card_unramifiedCondition, div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')]

end LocalConditions

section Sha

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ι : PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M] [Finite M]

/-- **The formula of Greenberg and Wiles for the zero conditions**:
`#Ш¹_S(M) / #H¹(G_S, M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #H⁰(K_v, M)⁻¹
· ∏_{w real} #H⁰(K_w, M)⁻¹ / (#M)^{r₂}`. -/
theorem card_sha_one_div_card_cohomology_one_dual
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hM : ∀ m : M, N • m = 0) :
    letI : Fintype S := Fintype.ofFinite S
    (Nat.card (sha ι M 1) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 1) =
      (Nat.card (cohomology M 0) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 0) *
        (∏ v : S, (Nat.card (cohomology (localModule ι M v) 0) : ℚ)⁻¹) *
        (∏ w : {w : InfinitePlace K // w.IsReal},
          (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)⁻¹) /
        (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K := by
  let _ : Fintype S := Fintype.ofFinite S
  have h := (⊥ : LocalConditions ι M).card_selmerGroup_div_card_selmerGroup_dual hS hM
  have htop : Nat.card (⊤ : AddSubgroup (cohomology (PoitouTate.dual N M) 1)) =
      Nat.card (cohomology (PoitouTate.dual N M) 1) :=
    Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [LocalConditions.dual_bot, LocalConditions.selmerGroup_bot,
    LocalConditions.selmerGroup_top, htop] at h
  rw [h]
  simp only [LocalConditions.bot_finite, LocalConditions.bot_real, AddSubgroup.card_bot,
    Nat.cast_one, one_div]

end Sha

end

end Langlands.GaloisCohomology
