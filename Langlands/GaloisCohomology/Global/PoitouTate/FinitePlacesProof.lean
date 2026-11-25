import Langlands.GaloisCohomology.Global.PoitouTate.FiniteTrace
import Langlands.GaloisCohomology.Global.PoitouTate.EvenDuality
import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlaces
import Langlands.GaloisCohomology.Global.PoitouTate.Sequence
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.Local.Dimension
import Langlands.GaloisCohomology.CompactSupport.DualityPrimary

/-!
# The duality at the finite places from the fields containing the roots of unity

`RootsOfUnityDualityStatement` is the duality for `ℤ/n` with compact support at the places of `S`
(`compactZmodDualityMap`, with the trace `finiteTrace`) for the number fields containing the `n`-th
roots of unity, `n` a prime power with the places above `n` in `S`, `n` odd or the field totally
complex. This file proves `FinitePlacesDualityStatement` from it
(`finitePlacesDualityStatement_of_rootsOfUnity`):

* for `N = q` a prime power, by the dévissage `CompactDualityHypotheses` of the abstract layer: the
  cohomology with compact support vanishes in degree `4` (`subsingleton_compactSupportCohomologyRes_of_four_le`,
  from `cd ≤ 2` globally and locally), and for an open subgroup `U` fixing `K(μ_q)` the duality for
  `ℤ/q` over `U` is that of its fixed field `L ⊇ μ_q`
  (`bijective_zmodCompactDualityMap_of_rootsOfUnity`, through `bijective_compactZmodDualityMap_fixingOpenSubgroup`);
* for general `N`, by the reduction to prime powers `bijective_compactDualityMap_of_primePow`, the
  traces of the primary parts being compatible through the local invariants
  (`zmodToQZ_finiteTrace_rootsOfUnityInclusion`).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory CategoryTheory.Limits MonoidalCategory Langlands.ProfiniteCohomology
  Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

/-- **Duality for `ℤ/n` over the fields containing `μ_n`.** For every number field `K` containing the
`n`-th roots of unity of its separable closure `Ω`, `n` a prime power, `n` odd or `K` totally complex,
and every finite set `S` of finite places containing the places above `n`, the duality map
`Hʳ(G_S, ℤ/n) → Hom(H_cˢ(G_S, μ_n), ℤ/n)` (compact support at the places of `S`, trace
`finiteTrace`) is bijective for `r + s = 3`. -/
def RootsOfUnityDualityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (n : ℕ) [NeZero n],
    IsPrimePow n → (∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ hK : Odd n ∨ IsTotallyComplex K, (∀ ζ : Ω, ζ ^ n = 1 → ζ ∈ (algebraMap K Ω).range) →
    ∀ {r s : ℕ} (h : r + s = 3),
      Function.Bijective (compactZmodDualityMap (localFamily ι S) (dualizingModule K Ω S n)
        (nsmul_dualizingModule S n) (finiteTrace ι S n hK) h)

section Basic

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- **Vanishing of `H_cʳ(G_S, M)` for `r ≥ 4`** (compact support at the places of `S`), for `M`
killed by `n` odd, or by any `n` if `K` is totally complex, the places above `n` in `S`. -/
theorem subsingleton_compactSupportCohomologyRes_of_four_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 4 ≤ r) :
    Subsingleton (compactSupportCohomologyRes (localFamily ι S) M r) := by
  obtain ⟨p, rfl⟩ : ∃ p, r = p + 1 := ⟨r - 1, by omega⟩
  refine ⟨fun x x' => ?_⟩
  suffices h : ∀ x : compactSupportCohomologyRes (localFamily ι S) M (p + 1), x = 0 from
    (h x).trans (h x').symm
  intro x
  have h3 := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S hn hS hK M hM
    (r := p + 1) (by omega)
  refine ((ptExact_compact (localFamily ι S) M p x).1 (Subsingleton.elim _ _)).elim fun ξ hξ => ?_
  have : ξ = 0 := funext fun v => by
    have := subsingleton_cohomology_localModule_of_three_le ι S v.1 hn M hM (r := p) (by omega)
    exact Subsingleton.elim _ _
  rw [← hξ, this, map_zero]

/-- **Surjectivity of the trace at the finite places** (`N ≠ 1`). -/
theorem surjective_finiteTrace [Finite S] (N : ℕ) [NeZero N] (hK : Odd N ∨ IsTotallyComplex K)
    (hN : N ≠ 1) (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Function.Surjective (finiteTrace ι S N hK) := by
  classical
  obtain ⟨v⟩ := nonempty_of_natCast_mem hN hS
  refine (exists_invariantAt_eq ι S N hS v.1 (zmodToQZ N 1) (by
    rw [← map_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, map_zero])).elim fun ξv hξv => ?_
  let ξ : ∀ w : S, cohomology (localModule ι (dualizingModule K Ω S N) w.1) 2 := Pi.single v ξv
  have hξ : ∀ w, w ≠ v → ξ w = 0 := fun w hw =>
    Pi.single_eq_of_ne (M := fun w : S => cohomology (localModule ι (dualizingModule K Ω S N) w.1) 2)
      hw ξv
  have hξv' : ξ v = ξv :=
    Pi.single_eq_same (M := fun w : S => cohomology (localModule ι (dualizingModule K Ω S N) w.1) 2)
      v ξv
  have h1 : finiteTrace ι S N hK
      ((ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S N) 2).hom ξ) = 1 := by
    apply zmodToQZ_injective (n := N)
    refine (isFiniteTrace_finiteTrace ι S N hK ξ).trans ?_
    rw [← hξv]
    let _ : Fintype S := Fintype.ofFinite S
    refine (Finset.sum_eq_single v (fun w _ hw => ?_) (fun h => absurd (Finset.mem_univ v) h)).trans
      ?_
    · rw [hξ w hw, map_zero]
    · rw [hξv']
  intro z
  refine ⟨z.val • (ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S N) 2).hom ξ, ?_⟩
  rw [map_nsmul, h1, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

end Basic

section PrimePow

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (q : ℕ) [NeZero q]

omit [Finite S] in
/-- A finite extension `L ⊆ K_S` whose fixing subgroup fixes `K(ζ)`, `ζ` a primitive `q`-th root of
unity, contains the `q`-th roots of unity. -/
theorem mem_range_of_pow_eq_one {ζ : Ω} (hζ : IsPrimitiveRoot ζ q)
    (hζS : ζ ∈ maximalUnramifiedOutside K Ω S) {L₀ : IntermediateField K Ω} [NumberField L₀]
    (hL₀ : ∀ x : L₀, algebraMap L₀ Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hL₀ζ : L₀ = IntermediateField.adjoin K {ζ}) {L : IntermediateField K Ω} [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hU : GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL ≤
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) :
    ∀ z : Ω, z ^ q = 1 → z ∈ (algebraMap L Ω).range := by
  obtain ⟨y, hy⟩ := exists_embeddingMaximalUnramifiedOutside_eq S hL ⟨ζ, hζS⟩ fun σ hσ =>
    apply_sqrt_neg_one_of_mem S hζS hL₀ hL₀ζ σ (hU hσ)
  have hy' : algebraMap L Ω y = ζ := congrArg Subtype.val hy
  intro z hz
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  exact ⟨y ^ i, by rw [map_pow, hy']⟩

/-- **Duality for `ℤ/q` over an open subgroup fixing `K(μ_q)`**, from the duality over the fields
containing `μ_q`: the fixed field `L` of `U` contains `μ_q`. -/
theorem bijective_zmodCompactDualityMap_of_rootsOfUnity
    (hbase : RootsOfUnityDualityStatement.{u}) (hq : IsPrimePow q)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd q ∨ IsTotallyComplex K)
    (hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, q • m = 0) →
        Subsingleton (compactSupportCohomologyRes (localFamily ι S) M 4))
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) (hζS : ζ ∈ maximalUnramifiedOutside K Ω S)
    {L₀ : IntermediateField K Ω} [NumberField L₀]
    (hL₀ : ∀ x : L₀, algebraMap L₀ Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hL₀ζ : L₀ = IntermediateField.adjoin K {ζ})
    (hD : ∀ d : dualizingModule K Ω S q, q • d = 0)
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    {L : IntermediateField K Ω} [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hUL : GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL = U)
    (hU : U ≤ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (zmodCompactDualityMap (localFamily ι S) (dualizingModule K Ω S q) hD U h
      (finiteTrace ι S q hK)) := by
  subst hUL
  have : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩
  have hLc : Odd q ∨ IsTotallyComplex L := hK.imp id fun hc => by
    have := hc
    exact isTotallyComplex_of_algebra K L
  have : Finite (finitePlacesAbove L S) := (finite_finitePlacesAbove (Set.toFinite S)).to_subtype
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L), ((q : ℕ) : 𝓞 L) ∈ w.asIdeal →
      w ∈ finitePlacesAbove L S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((q : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  let ι₀ : PlaceEmbeddings L Ω := Classical.choice inferInstance
  have hμ := mem_range_of_pow_eq_one S q hζ hζS hL₀ hL₀ζ hL hU
  have hb := fun {r' s' : ℕ} (h' : r' + s' = 3) =>
    hbase L Ω (finitePlacesAbove L S) (placeEmbeddingsOver hL ι ι₀) q hq hSL hLc hμ h'
  have h3 := cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le (K := L) (Ω := Ω)
    (finitePlacesAbove L S) (NeZero.ne q) hSL hLc
    (dualizingModule L Ω (finitePlacesAbove L S) q) (nsmul_dualizingModule _ q) (le_refl 3)
  have hsurjL := surjective_localToCompact_two
    (localFamily (placeEmbeddingsOver hL ι ι₀) (finitePlacesAbove L S))
    (dualizingModule L Ω (finitePlacesAbove L S) q) h3
  have : Finite (dualizingModule K Ω S q) := finite_dualizingModule S q hS
  have hTsurj : Function.Surjective ((finiteTrace ι S q hK).comp
      (compactCores (localFamily ι S) (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (dualizingModule K Ω S q) 3).hom.toAddMonoidHom) :=
    (surjective_finiteTrace ι S q hK hq.ne_one hS).comp (surjective_compactCores_three
      (localFamily ι S) _ (dualizingModule K Ω S q) (nsmul_dualizingModule S q) hV)
  have key := bijective_compactZmodDualityMap_fixingOpenSubgroup (hDU := isSmoothRep_res_subtype _ _)
    hL ι ι₀ q h _ (exists_eq_mul_of_bijective_zero _ _ _ (show 0 + 3 = 3 from rfl) hsurjL _ (hb _))
    (hb h) ((finiteTrace ι S q hK).comp
      (compactCores (localFamily ι S) (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (dualizingModule K Ω S q) 3).hom.toAddMonoidHom) hTsurj
  beta_reduce at key
  -- The trace of `U`, the instance and the proof are those of `key`, so that its type is
  -- syntactically the one expected (the unifier otherwise unfolds the cohomology groups).
  refine bijective_zmodCompactDualityMap_of (hDU := isSmoothRep_res_subtype _ _) (localFamily ι S)
    (dualizingModule K Ω S q) hD _ h _ (nsmul_dualizingModule S q)
    ((finiteTrace ι S q hK).comp
      (compactCores (localFamily ι S) (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
        (dualizingModule K Ω S q) 3).hom.toAddMonoidHom) (fun _ => rfl) ?_
  exact key

/-- **The dévissage hypotheses at a prime power** `q`: the subgroup fixing `K(μ_q)` satisfies
`CompactDualityHypotheses` for `μ_q` and `finiteTrace`. -/
theorem exists_compactDualityHypotheses_of_rootsOfUnity (hbase : RootsOfUnityDualityStatement.{u})
    (hq : IsPrimePow q)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd q ∨ IsTotallyComplex K) :
    ∃ U₀ : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S),
      CompactDualityHypotheses (localFamily ι S) q (dualizingModule K Ω S q)
        (finiteTrace ι S q hK) U₀ := by
  obtain ⟨ζ, hζ, hζS⟩ := exists_isPrimitiveRoot_mem (Ω := Ω) S q hS
  let L₀ : IntermediateField K Ω := IntermediateField.adjoin K {ζ}
  have : FiniteDimensional K L₀ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have : NumberField L₀ := NumberField.of_module_finite K L₀
  have hle : L₀ ≤ maximalUnramifiedOutside K Ω S := IntermediateField.adjoin_simple_le_iff.2 hζS
  have hL₀ : ∀ x : L₀, algebraMap L₀ Ω x ∈ maximalUnramifiedOutside K Ω S := fun x => hle x.2
  have hV : ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
      [Finite M], (∀ m : M, q • m = 0) →
        Subsingleton (compactSupportCohomologyRes (localFamily ι S) M 4) := fun M _ _ hM =>
    subsingleton_compactSupportCohomologyRes_of_four_le ι S (NeZero.ne q) hS hK M hM (le_refl 4)
  exact ⟨GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₀,
    { nonempty_addEquiv := nonempty_addEquiv_dualizingModule hS
      subsingleton_four := hV
      bijective_base := fun U hU {_ _} h =>
        (GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq U).elim fun L ⟨_, hL, hUL⟩ =>
          bijective_zmodCompactDualityMap_of_rootsOfUnity ι S q hbase hq hS hK hV hζ hζS hL₀ rfl _
            U hL hUL hU h }⟩

/-- **Duality at the finite places for a prime power** `q`, from `RootsOfUnityDualityStatement`. -/
theorem bijective_compactDualityMap_of_rootsOfUnity (hbase : RootsOfUnityDualityStatement.{u})
    (hq : IsPrimePow q)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd q ∨ IsTotallyComplex K)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, q • m = 0) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (GaloisCohomology.compactDualityMap (localFamily ι S)
      (dualizingModule K Ω S q) h (finiteTrace ι S q hK) M) :=
  (exists_compactDualityHypotheses_of_rootsOfUnity ι S q hbase hq hS hK).elim fun _ H =>
    H.bijective_compactDualityMap M hM h

end PrimePow

section Primary

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The inclusion `μ_d(K_S) → μ_N(K_S)` for `d ∣ N`. -/
def rootsOfUnityInclusion {d N : ℕ} (hd : d ∣ N) :
    dualizingModule K Ω S d ⟶ dualizingModule K Ω S N :=
  Rep.ofHom ⟨(uliftIntLinearMap (MonoidHom.toAdditive
      (Subgroup.inclusion (rootsOfUnity_le_of_dvd hd))) :
    Additive (rootsOfUnity d (maximalUnramifiedOutside K Ω S)) →ₗ[ULift.{u} ℤ]
      Additive (rootsOfUnity N (maximalUnramifiedOutside K Ω S))), fun _ => LinearMap.ext
    fun _ => rfl⟩

omit [NumberField K] [IsSepClosure K Ω] in
theorem injective_rootsOfUnityInclusion {d N : ℕ} (hd : d ∣ N) :
    Function.Injective (rootsOfUnityInclusion S hd (Ω := Ω)).hom := fun _ _ hab =>
  Additive.toMul.injective (Subtype.ext (congrArg (fun z : Additive (rootsOfUnity N
    (maximalUnramifiedOutside K Ω S)) => ((Additive.toMul z : rootsOfUnity N
      (maximalUnramifiedOutside K Ω S)) : (maximalUnramifiedOutside K Ω S)ˣ)) hab))

/-- The local invariants are compatible with the inclusions `μ_d → μ_N`. -/
theorem invariantAt_coeffMap_rootsOfUnityInclusion {d N : ℕ} (hd : d ∣ N) (v : S)
    (ξ : cohomology (localModule ι (dualizingModule K Ω S d) v.1) 2) :
    invariantAt ι S N v.1 ((coeffMap (resMorphism (localFamily ι S)
      (rootsOfUnityInclusion S hd) v) 2).hom ξ) = invariantAt ι S d v.1 ξ := by
  have e : resMorphism (localFamily ι S) (rootsOfUnityInclusion S hd) v ≫
      rootsOfUnityLocalHom ι S N v.1 = rootsOfUnityLocalHom ι S d v.1 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  rw [invariantAt_apply, invariantAt_apply, ← ConcreteCategory.comp_apply, ← coeffMap_comp, e]

variable [Finite S]

/-- **Compatibility of the traces with the inclusions** `μ_d → μ_N` (`d ∣ N`, the places above `d` in
`S`). -/
theorem zmodToQZ_finiteTrace_rootsOfUnityInclusion {d N : ℕ} [NeZero d] [NeZero N] (hd : d ∣ N)
    (hKd : Odd d ∨ IsTotallyComplex K) (hKN : Odd N ∨ IsTotallyComplex K)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((d : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (z : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S d) 3) :
    zmodToQZ N (finiteTrace ι S N hKN ((compactSupportCohomologyResMap (localFamily ι S)
      (rootsOfUnityInclusion S hd) 3).hom z)) = zmodToQZ d (finiteTrace ι S d hKd z) := by
  let _ : Fintype S := Fintype.ofFinite S
  refine (surjective_ptLocalToCompact_two ι S d hKd hS z).elim fun ξ hξ => ?_
  rw [← hξ, compactSupportCohomologyResMap_ptLocalToCompact, isFiniteTrace_finiteTrace ι S N hKN,
    isFiniteTrace_finiteTrace ι S d hKd]
  exact Finset.sum_congr rfl fun v _ => invariantAt_coeffMap_rootsOfUnityInclusion ι S hd v (ξ v)

end Primary

/-- **Poitou–Tate duality without the real places**, from the duality over the fields containing the
roots of unity (`RootsOfUnityDualityStatement`), with the trace `finiteTrace`. -/
theorem finitePlacesDualityStatement_of_rootsOfUnity (hbase : RootsOfUnityDualityStatement.{u}) :
    FinitePlacesDualityStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι N _ hS hK
  refine ⟨finiteTrace ι S N hK, isFiniteTrace_finiteTrace ι S N hK, fun M _ _ hM r s h => ?_⟩
  have hne : ∀ p, p ^ N.factorization p ≠ 0 := fun p => by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · rw [Nat.factorization_eq_zero_of_not_prime N Nat.not_prime_zero, pow_zero]
      exact one_ne_zero
    · exact pow_ne_zero _ hp.ne'
  have hnz : ∀ p, NeZero (p ^ N.factorization p) := fun p => ⟨hne p⟩
  have hdvd : ∀ p, p ^ N.factorization p ∣ N := fun p => Nat.ordProj_dvd N p
  have hSd : ∀ p, ∀ v : HeightOneSpectrum (𝓞 K),
      ((p ^ N.factorization p : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun p v hv => hS v (by
    obtain ⟨c, hc⟩ := hdvd p
    rw [hc, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv)
  have hKd : ∀ p, Odd (p ^ N.factorization p) ∨ IsTotallyComplex K := fun p =>
    hK.imp (fun ho => ho.of_dvd_nat (hdvd p)) id
  exact bijective_compactDualityMap_of_primePow (localFamily ι S) (dualizingModule K Ω S N)
    (finiteTrace ι S N hK) (fun p => dualizingModule K Ω S (p ^ N.factorization p))
    (fun p => finiteTrace ι S (p ^ N.factorization p) (hKd p))
    (fun p => rootsOfUnityInclusion S (hdvd p)) (nonempty_addEquiv_dualizingModule hS)
    (fun p _ => nonempty_addEquiv_dualizingModule (hSd p))
    (fun p _ => injective_rootsOfUnityInclusion S (hdvd p))
    (fun p _ z => zmodToQZ_finiteTrace_rootsOfUnityInclusion ι S (hdvd p) (hKd p) hK (hSd p) z)
    (fun p hp M _ _ hM {_ _} h => bijective_compactDualityMap_of_rootsOfUnity ι S _ hbase
      ((Nat.prime_of_mem_primeFactors hp).isPrimePow.pow (Finsupp.mem_support_iff.1 (by
        rw [Nat.support_factorization]
        exact hp))) (hSd p) (hKd p) M hM h) M hM h

end

end Langlands.GaloisCohomology.PoitouTate
