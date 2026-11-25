import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Reduction

/-!
# The Euler characteristic formula for `ℓ`-primary modules, from Tate's base case

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places, `ℓ` a prime
with the places above `ℓ` in `S`, and `G_S` the Galois group of `K_S ⊆ Ω`.

**Tate's base case** (`GlobalEulerCharacteristicBaseStatement`): the formula holds for a finite module
`M` killed by `ℓ` when `G_S(L)` acts trivially on `M` for a finite Galois extension `L ⊆ K_S` of `K` of
degree prime to `ℓ` containing a primitive `ℓ`-th root of unity, with `ℓ` odd or `L` totally complex.

This file proves, assuming the base case, the formula for every finite module killed by a power of
`ℓ` (`globalEulerRatio_eq_one_of_primary_of_base`); Tate's theorem on the real places in degree three
(`realLocalizationDegreeThreeStatement`) enters through the multiplicativity of the ratio
(`globalEulerRatio_shortExact`):

* a module killed by `ℓ` is trivial on `G_S(L)` for a finite Galois `L ⊆ K_S` containing `μ_ℓ` (and `i`
  when `ℓ = 2`, so that `L` is totally complex) (`exists_splitting_field`);
* by the reduction to cyclic quotients (`globalEulerRatio_eq_one_of_cyclic`) and to their parts of
  degree prime to `ℓ` (`globalEulerRatio_coind_eq_one`) it suffices to know the formula over the fields
  `K''` with `K ⊆ K'' ⊆ L`, `[L : K'']` prime to `ℓ`, for `M` as a `G_S(K'')`-module, which is the base
  case over `K''` with `S_{K''}` the places above `S` (`globalEulerRatio_resToFixedField_eq_one`);
* the formula for modules killed by `ℓ` gives it for modules killed by `ℓ^r`
  (`globalEulerRatio_eq_one_of_primary`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

-- A separable closure of a number field is Galois over it; found first, before the search for
-- other ways to prove `IsGalois`.
attribute [local instance 2000] IsSepClosure.isGalois

/-- **Tate's base case** of the global Euler characteristic formula: for every number field `K`,
separable closure `Ω`, finite set `S` of finite places, prime `ℓ` with the places above `ℓ` in `S`,
finite Galois extension `L ⊆ K_S` of `K` of degree prime to `ℓ` containing a primitive `ℓ`-th root of
unity, with `ℓ` odd or `L` totally complex, and finite smooth `G_S`-module `M` killed by `ℓ` on which
`G_S(L)` acts trivially, the ratio `globalEulerRatio ι M` is `1`. -/
def GlobalEulerCharacteristicBaseStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ℓ : ℕ) [Fact ℓ.Prime],
    (∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (L : Type u) [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
      (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S),
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal →
      Nat.Coprime (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index ℓ →
      (∃ ζ : L, IsPrimitiveRoot ζ ℓ) → (ℓ ≠ 2 ∨ IsTotallyComplex L) →
      ∀ (ι : PlaceEmbeddings K Ω) (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
        [IsSmoothRep M] [Finite M], (∀ m : M, ℓ • m = 0) →
        (∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1) →
        globalEulerRatio ι M = 1

section Galois

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}

/-- An element of `K_S` fixed by the subgroup fixing `L` comes from `L`. -/
theorem exists_eq_embedding_of_forall_fixingOpenSubgroup {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (y : maximalUnramifiedOutside K Ω S)
    (hy : ∀ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL, σ y = y) :
    ∃ x : L, embeddingMaximalUnramifiedOutside hL x = y := by
  have hmem : y ∈ IntermediateField.fixedField
      (embeddingMaximalUnramifiedOutside hL).fieldRange.fixingSubgroup := fun σ => hy σ.1 σ.2
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx⟩

/-- A field `K''` whose fixing subgroup contains that of `L` lies in `L`. -/
theorem le_of_fixingOpenSubgroup_le (K'' L : IntermediateField K Ω) [NumberField K''] [NumberField L]
    (hK'' : ∀ x : K'', algebraMap K'' Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hle : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'') : K'' ≤ L := by
  intro x hx
  obtain ⟨y, hy⟩ := exists_eq_embedding_of_forall_fixingOpenSubgroup hL
    (embeddingMaximalUnramifiedOutside hK'' ⟨x, hx⟩) fun σ hσ =>
      (GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff S hK'' σ).1 (hle hσ) ⟨x, hx⟩
  have h : ((embeddingMaximalUnramifiedOutside hL y : maximalUnramifiedOutside K Ω S) : Ω) = x :=
    congrArg Subtype.val hy
  rw [coe_embeddingOfRestrictScalarsEq] at h
  rw [← h]
  exact y.2

theorem isTotallyComplex_of_sq_eq_neg_one {E : Type*} [Field E] (x : E) (hx : x ^ 2 = -1) :
    IsTotallyComplex E := by
  refine ⟨fun w => ?_⟩
  by_contra hw
  have hr := InfinitePlace.not_isComplex_iff_isReal.1 hw
  have h := congrArg (InfinitePlace.embedding_of_isReal hr) hx
  rw [map_pow, map_neg, map_one] at h
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hr x)]

end Galois

section Ending

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S]

omit [Finite S] in
/-- `L` is unramified over `K''` outside the places above `S` when it is over `K` outside `S`. -/
theorem algebraMap_mem_maximalUnramifiedOutside_over (K'' : IntermediateField K Ω) [NumberField K'']
    (hK'' : ∀ x : K'', algebraMap K'' Ω x ∈ maximalUnramifiedOutside K Ω S)
    {L : Type*} [Field L] [Algebra K'' L] [Algebra L Ω] {x : L}
    (hx : algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) :
    algebraMap L Ω x ∈ maximalUnramifiedOutside K'' Ω (finitePlacesAbove K'' S) :=
  mem_of_restrictScalars_eq' (restrictScalars_maximalUnramifiedOutside S hK'') hx

/-- **The base case over an intermediate field.** Let `L ⊆ K_S` be finite Galois over `K` with the
properties of the base case except the degree, `M` a module killed by `ℓ` on which `G_S(L)` acts
trivially, and `K ⊆ K'' ⊆ K_S` with `G_S(L) ⊆ G_S(K'')` of index prime to `ℓ`. Then the formula holds
for `M` as a `G_{S_{K''}}(K'')`-module. -/
theorem globalEulerRatio_resToFixedField_eq_one (hbase : GlobalEulerCharacteristicBaseStatement.{u})
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (L : IntermediateField K Ω) [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    [hN : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ) (hc : ℓ ≠ 2 ∨ IsTotallyComplex L)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0)
    (htriv : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1)
    (K'' : IntermediateField K Ω) [NumberField K'']
    (hK'' : ∀ x : K'', algebraMap K'' Ω x ∈ maximalUnramifiedOutside K Ω S)
    (hle : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≤
      GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'')
    (hcop : Nat.Coprime ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S))).index ℓ)
    (ιK'' : PlaceEmbeddings K'' Ω) :
    globalEulerRatio ιK'' (resToFixedField hK'' M) = 1 := by
  have hKL : K'' ≤ L := le_of_fixingOpenSubgroup_le K'' L hK'' hL hle
  let _ : Algebra K'' L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  have : IsScalarTower K'' L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Finite (finitePlacesAbove K'' S) :=
    (finite_finitePlacesAbove (L := K'') (Set.toFinite S)).to_subtype
  have hS'' : ∀ w : HeightOneSpectrum (𝓞 K''), ((ℓ : ℕ) : 𝓞 K'') ∈ w.asIdeal →
      w ∈ finitePlacesAbove K'' S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 K'') ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  have hL'' : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K'' Ω (finitePlacesAbove K'' S) :=
    fun x => algebraMap_mem_maximalUnramifiedOutside_over K'' hK'' (hL x)
  set e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hK''
  -- the subgroup fixing `L` over `K''` corresponds to the subgroup fixing `L` over `K`
  have hmem : ∀ τ, τ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup (finitePlacesAbove K'' S) hL'' ↔
      ((e.symm τ : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S))) : GaloisGroupUnramifiedOutside K Ω S) ∈
          GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL := by
    intro τ
    rw [GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff,
      GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff]
    refine forall_congr' fun x => ?_
    rw [Subtype.ext_iff, Subtype.ext_iff,
      GaloisGroupUnramifiedOutside.coe_fixingOpenSubgroupEquiv_symm_apply]
    exact Iff.rfl
  have hcomap : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup (finitePlacesAbove K'' S) hL'' :
      Subgroup (GaloisGroupUnramifiedOutside K'' Ω (finitePlacesAbove K'' S))) =
      ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hK'' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S))).comap e.symm.toMulEquiv.toMonoidHom := by
    ext τ
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hmem τ
  refine hbase K'' Ω (finitePlacesAbove K'' S) ℓ hS'' L hL'' ?_ ?_ hζ hc ιK''
    (resToFixedField hK'' M) (fun m => hℓM m) ?_
  · rw [hcomap]
    exact (hN.subgroupOf _).comap _
  · rw [hcomap, Subgroup.index_comap_of_surjective _ e.symm.surjective]
    exact hcop
  · intro τ hτ
    exact htriv _ ((hmem τ).1 hτ)

end Ending

section Split

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}

omit [NumberField K] [IsSepClosure K Ω] in
/-- The kernel of a finite smooth representation of `G_S` is open. -/
theorem isOpen_ker_of_finite (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M] [Finite M] :
    IsOpen ((⨅ m : M, vectorStabilizer M.ρ m : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :
      Set (GaloisGroupUnramifiedOutside K Ω S)) := by
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun m => IsSmoothRep.isOpen_stabilizer M m

/-- **A splitting field.** For a finite smooth `G_S`-module `M` and a prime `ℓ` with the places above
`ℓ` in `S`, there is a finite Galois extension `L ⊆ K_S` of `K` containing a primitive `ℓ`-th root of
unity, totally complex if `ℓ = 2`, such that `G_S(L)` acts trivially on `M`. -/
theorem exists_splitting_field {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M] :
    ∃ (L : IntermediateField K Ω) (_ : NumberField L)
      (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S),
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal ∧ (∃ ζ : L, IsPrimitiveRoot ζ ℓ) ∧
      (ℓ ≠ 2 ∨ IsTotallyComplex L) ∧
      ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1 := by
  classical
  set G := GaloisGroupUnramifiedOutside K Ω S
  -- a primitive `n`-th root of unity in `K_S`, `n = ℓ` or `4`
  let n : ℕ := if ℓ = 2 then 4 else ℓ
  have hn0 : n ≠ 0 := by
    by_cases h2 : ℓ = 2
    · simp [n, h2]
    · simp only [n, h2, ↓reduceIte]; exact hℓ.out.ne_zero
  have hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro v hv hmem
    apply hv
    apply hS v
    by_cases h2 : ℓ = 2
    · subst h2
      have h4 : ((4 : ℕ) : 𝓞 K) = ((2 : ℕ) : 𝓞 K) * ((2 : ℕ) : 𝓞 K) := by push_cast; ring
      simp only [n, ↓reduceIte] at hmem
      rw [h4] at hmem
      rcases v.isPrime.mem_or_mem hmem with h | h <;> exact h
    · simpa [n, h2] using hmem
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω n
  have hζS : ζ ∈ maximalUnramifiedOutside K Ω S :=
    mem_maximalUnramifiedOutside_of_pow_eq_one S hn0 hnS hζ.pow_eq_one
  -- the field `K(ζ)` and its fixing subgroup
  let L₂ : IntermediateField K Ω := IntermediateField.adjoin K {ζ}
  have : FiniteDimensional K L₂ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have : NumberField L₂ := NumberField.of_module_finite K L₂
  have hL₂ : ∀ x : L₂, algebraMap L₂ Ω x ∈ maximalUnramifiedOutside K Ω S := fun x =>
    IntermediateField.adjoin_simple_le_iff.2 hζS x.2
  -- the open normal subgroup acting trivially on `M` and on `ζ`
  let N : Subgroup G := (⨅ m : M, vectorStabilizer M.ρ m) ⊓
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₂ : Subgroup G)
  have hNo : IsOpen (N : Set G) :=
    (isOpen_ker_of_finite M).inter (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL₂).isOpen
  have : N.FiniteIndex := finiteIndex_openSubgroup (⟨N, hNo⟩ : OpenSubgroup G)
  let C : OpenSubgroup G := ⟨N.normalCore, Subgroup.isOpen_of_isClosed_of_finiteIndex _
    (N.normalCore_isClosed (Subgroup.isClosed_of_isOpen _ hNo))⟩
  obtain ⟨L, hLf, hL, hC⟩ := GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq (S := S) C
  have hLC : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup G) = N.normalCore := by
    rw [hC]
  have hle : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL : Subgroup G) ≤ N :=
    hLC ▸ N.normalCore_le
  -- `ζ` comes from `L`
  let ζ' : maximalUnramifiedOutside K Ω S := ⟨ζ, hζS⟩
  have hζfix : ∀ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL, σ ζ' = ζ' := by
    intro σ hσ
    have h1 := (GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff S hL₂ σ).1 (hle hσ).2
      ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
    exact h1
  obtain ⟨z, hz⟩ := exists_eq_embedding_of_forall_fixingOpenSubgroup hL ζ' hζfix
  have hzΩ : algebraMap L Ω z = ζ := by
    have := congrArg Subtype.val hz
    rwa [coe_embeddingOfRestrictScalarsEq] at this
  have hzn : IsPrimitiveRoot z n :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L Ω) (hzΩ ▸ hζ)
      (algebraMap L Ω).injective
  refine ⟨L, hLf, hL, ?_, ?_, ?_, ?_⟩
  · rw [hLC]
    exact Subgroup.normalCore_normal N
  · by_cases h2 : ℓ = 2
    · subst h2
      exact ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
    · exact ⟨z, by simpa [n, h2] using hzn⟩
  · by_cases h2 : ℓ = 2
    · right
      have hz4 : IsPrimitiveRoot z 4 := by simpa [n, h2] using hzn
      refine isTotallyComplex_of_sq_eq_neg_one z ?_
      have h1 : (z ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hz4.pow_eq_one
      have h2' : z ^ 2 ≠ 1 := hz4.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
      have h3 : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) h2'
      · exact eq_neg_of_add_eq_zero_left h
    · exact Or.inl h2
  · intro g hg
    refine LinearMap.ext fun m => ?_
    exact (Subgroup.mem_iInf.1 (hle hg).1 m)

end Split

section Assembly

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

/-- The formula for modules killed by a prime `ℓ`, from the base case. -/
theorem globalEulerRatio_eq_one_of_nsmul_of_base
    (hbase : GlobalEulerCharacteristicBaseStatement.{u}) {ℓ : ℕ} [Fact ℓ.Prime]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hℓM : ∀ m : M, ℓ • m = 0) : globalEulerRatio ι M = 1 := by
  obtain ⟨L, hLf, hL, hN, hζ, hc, htriv⟩ := exists_splitting_field hS M
  refine globalEulerRatio_eq_one_of_cyclic ι hS L hL M hℓM htriv
    fun L' _ hL' hle hcyc => ?_
  have : ((GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subgroupOf
        (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL' :
          Subgroup (GaloisGroupUnramifiedOutside K Ω S))).Normal := hN.subgroupOf _
  exact globalEulerRatio_coind_eq_one ι hS (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) M
    hℓM (fun K'' _ hK'' hle'' _ hcop ιK'' =>
      globalEulerRatio_resToFixedField_eq_one hbase hS L hL hζ hc M hℓM htriv K'' hK'' hle'' hcop ιK'')
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL') hle hcyc

/-- **The global Euler characteristic formula for `ℓ`-primary modules**, from the base case: for a
finite smooth module `M` killed by a power of a prime `ℓ` with the places above `ℓ` in `S`,
`globalEulerRatio ι M = 1`. -/
theorem globalEulerRatio_eq_one_of_primary_of_base
    (hbase : GlobalEulerCharacteristicBaseStatement.{u}) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    {r : ℕ} (hr : ∀ m : M, (ℓ ^ r) • m = 0) : globalEulerRatio ι M = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact globalEulerRatio_eq_one_of_primary ι hℓ hS
    (fun N _ _ hN => globalEulerRatio_eq_one_of_nsmul_of_base ι hbase hS N hN) M hr

end Assembly

section AllModules

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)

/-- A finite group killed by `m` has order prime to every prime not dividing `m`. -/
theorem not_dvd_card_of_nsmul {X : Type*} [AddCommGroup X] [Finite X] {m ℓ : ℕ} (hℓ : ℓ.Prime)
    (hm : ¬ ℓ ∣ m) (h : ∀ x : X, m • x = 0) : ¬ ℓ ∣ Nat.card X := by
  intro hdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ hdvd
  exact hm (hx ▸ addOrderOf_dvd_of_nsmul_eq_zero (h x))

/-- **The global Euler characteristic formula for all finite modules**, from the base case: by the
decomposition `0 → M[m] → M → mM → 0` with `#M = ℓ^a m`, `ℓ ∤ m`, into a module of smaller order and
an `ℓ`-primary module, and multiplicativity. -/
theorem globalEulerRatio_eq_one_of_base (hbase : GlobalEulerCharacteristicBaseStatement.{u})
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    globalEulerRatio ι M = 1 := by
  suffices H : ∀ (n : ℕ) (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
      [IsSmoothRep M] [Finite M], Nat.card M = n →
      (∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
      globalEulerRatio ι M = 1 from H _ M rfl hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ hn hS
  by_cases h1 : n = 1
  · have : Subsingleton M := (Nat.card_eq_one_iff_unique.1 (hn.trans h1)).1
    exact globalEulerRatio_eq_one_of_subsingleton ι M
  have hn0 : n ≠ 0 := hn ▸ Nat.card_pos.ne'
  obtain ⟨ℓ, hℓ, hℓn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact ℓ.Prime := ⟨hℓ⟩
  -- `n = ℓ^a · m` with `ℓ ∤ m`
  set a := n.factorization ℓ
  set m := n / ℓ ^ a with hm
  have hnm : ℓ ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hℓm : ¬ ℓ ∣ m := Nat.not_dvd_ordCompl hℓ hn0
  have hm0 : m ≠ 0 := fun h => hn0 (by rw [← hnm, h, mul_zero])
  -- the sequence `0 → M[m] → M → mM → 0`
  let T : Module.End (ULift.{u} ℤ) M := (m : Module.End (ULift.{u} ℤ) M)
  have hTx : ∀ x : M, T x = m • x := fun x => Module.End.natCast_apply m x
  have hT : ∀ g, Commute T (M.ρ g) := fun g => Nat.cast_commute m _
  have hD : ∀ g, (⊤ : Submodule _ M) ≤ Submodule.comap (M.ρ g) ⊤ := fun _ => le_top
  have hSE := rangeStepComplex_shortExact T hT ⊤ hD
  have : IsSmoothRep (rangeStepComplex T hT ⊤ hD).X₁ := isSmoothRep_subrepresentation _ _ _
  have : IsSmoothRep (rangeStepComplex T hT ⊤ hD).X₂ := isSmoothRep_subrepresentation _ _ _
  have : IsSmoothRep (rangeStepComplex T hT ⊤ hD).X₃ := isSmoothRep_subrepresentation _ _ _
  have : Finite (rangeStepComplex T hT ⊤ hD).X₂ :=
    Finite.of_injective (fun x : Rep.subrepresentation M ⊤ hD => (x.1 : M)) fun _ _ h =>
      Subtype.ext h
  have : Finite (rangeStepComplex T hT ⊤ hD).X₁ :=
    Finite.of_injective (fun x : Rep.subrepresentation M _ (inf_ker_le_comap T hT ⊤ hD) =>
      (x.1 : M)) fun _ _ h => Subtype.ext h
  have : Finite (rangeStepComplex T hT ⊤ hD).X₃ :=
    Finite.of_injective (fun x : Rep.subrepresentation M _ (map_le_comap T hT ⊤ hD) =>
      (x.1 : M)) fun _ _ h => Subtype.ext h
  have hcard2 : Nat.card (rangeStepComplex T hT ⊤ hD).X₂ = Nat.card M :=
    Nat.card_congr (Submodule.topEquiv (R := ULift.{u} ℤ) (M := M)).toEquiv
  have hcardM := card_X₂_eq_of_shortExact hSE
  have hdvd1 : Nat.card (rangeStepComplex T hT ⊤ hD).X₁ ∣ Nat.card M :=
    ⟨_, hcard2 ▸ hcardM⟩
  have hdvd3 : Nat.card (rangeStepComplex T hT ⊤ hD).X₃ ∣ Nat.card M :=
    ⟨_, (hcard2 ▸ hcardM).trans (mul_comm _ _)⟩
  have hSdvd : ∀ d, d ∣ Nat.card M → ∀ v : HeightOneSpectrum (𝓞 K),
      ((d : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun d hd v hv => by
    obtain ⟨e, he⟩ := hd
    exact hS v (by rw [he, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hv)
  have hmul := globalEulerRatio_shortExact ι hSE (hSdvd _ (hcard2 ▸ dvd_rfl))
  -- `M[m]` has order prime to `ℓ`, hence smaller
  have hker : globalEulerRatio ι (rangeStepComplex T hT ⊤ hD).X₁ = 1 := by
    have hk : ∀ x : (rangeStepComplex T hT ⊤ hD).X₁, m • x = 0 := fun x => Subtype.ext (by
      have h' : T x.1 = 0 := x.2.2
      rw [hTx] at h'
      exact h')
    have hndvd := not_dvd_card_of_nsmul hℓ hℓm hk
    have hlt : Nat.card (rangeStepComplex T hT ⊤ hD).X₁ < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd1) fun heq => hndvd ?_
      rw [heq, hn]
      exact hℓn
    exact ih _ hlt _ rfl (hSdvd _ hdvd1)
  -- `mM` is killed by `ℓ^a`
  have him : globalEulerRatio ι (rangeStepComplex T hT ⊤ hD).X₃ = 1 := by
    refine globalEulerRatio_eq_one_of_primary_of_base ι hbase hℓ ?_ _ (r := a) fun x => ?_
    · intro v hv
      exact hSdvd ℓ (hn ▸ hℓn) v hv
    · apply Subtype.ext
      obtain ⟨y, -, hy⟩ := x.2
      change (ℓ ^ a) • x.1 = 0
      rw [← hy, hTx, smul_smul, hnm, ← hn]
      exact card_nsmul_eq_zero'
  have htop : globalEulerRatio ι M = globalEulerRatio ι (rangeStepComplex T hT ⊤ hD).X₂ :=
    (globalEulerRatio_eq_of_iso ι _ (subrepresentationTopIso M hD)).symm
  rw [htop, hmul, hker, him, mul_one]

end AllModules

end

end Langlands.GaloisCohomology
