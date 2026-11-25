import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.RealCount
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Corollaries

/-!
# Tate's base case: assembly

In the situation of Tate's base case (`L ⊆ K_S` Galois over `K` of degree prime to `ℓ`, `μ_ℓ ⊆ L`,
`ℓ` odd or `L` totally complex, `M` killed by `ℓ` and trivial on `G_S(L)`), the formula
`globalEulerRatio ι M = 1` follows from the computations of the preceding files and the count of
`H²(G_S, M)` given by the nine-term sequence of Poitou–Tate, once `#Ш²_S(M) = ℓ^{d(A₁/ℓ)}`
(`baseCase_globalEulerRatio_of_card_sha`). With `d(X) = dim (X ⊗ Hom(μ_ℓ, M))^{Gal(L/K)}` and
`Aᵢ = Hⁱ(G_S(L), 𝒪_Sˣ)`, Tate's computation reads

`h⁰ - h¹ + h² = d(A₀[ℓ]) - d(A₀/ℓ) - d(A₁[ℓ]) + (#Ш² + ∑_{v ∈ S} h²(K_v) - h⁰(M'))
             = -(d(𝔽_ℓ[S_L]) + d(𝔽_ℓ[∞_L]) - d(𝔽_ℓ)) + d(A₁/ℓ) - d(A₁[ℓ]) + d(𝔽_ℓ[S_L]) - d(𝔽_ℓ)
             = -d(𝔽_ℓ[∞_L]) = ∑_{w real} h⁰(K_w, M) - #∞ · dim M.`
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local Representation Module Involution

universe u

noncomputable section

section Numeric

/-- The Euler characteristic ratio is `1` when the exponents of its factors, all powers of `ℓ`,
satisfy `a₀ - a₁ + a₂ = ∑ r_w - c · m`. -/
theorem div_eq_div_of_exponents {ι : Type*} [Fintype ι] {ℓ : ℕ} (hℓ : 0 < ℓ) (a₀ a₁ a₂ m c : ℕ)
    (r : ι → ℕ) (h : (a₀ : ℤ) - a₁ + a₂ = ∑ i, (r i : ℤ) - c * m) :
    ((ℓ ^ a₀ : ℕ) : ℚ) * ((ℓ ^ a₂ : ℕ) : ℚ) / ((ℓ ^ a₁ : ℕ) : ℚ) =
      (∏ i, ((ℓ ^ r i : ℕ) : ℚ)) / ((ℓ ^ m : ℕ) : ℚ) ^ c := by
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, div_eq_div_iff (pow_ne_zero _ hl0) (pow_ne_zero _ hl0),
    ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have h' : ((a₀ + a₂ + m * c : ℕ) : ℤ) = ((∑ i, r i + a₁ : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast h'

end Numeric

section Base

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ℓ : ℕ} [Fact ℓ.Prime]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
  (hcop : Nat.Coprime (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index ℓ)
  (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hMℓ : ∀ m : M, ℓ • m = 0)
  (hMP : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1)
  (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

omit [Finite S] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] in
include hcop in
/-- If `ℓ = 2` then `L` and hence `K` is totally complex: a real place of `K` below a complex place
of `L` has a stabilizer of order two in `Gal(L/K)`, of order prime to `2`. -/
theorem odd_or_isTotallyComplex [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] (hc : ℓ ≠ 2 ∨ IsTotallyComplex L) :
    Odd ℓ ∨ IsTotallyComplex K := by
  have hl : ℓ.Prime := Fact.out
  by_cases h2 : ℓ = 2
  · right
    subst h2
    have hTC : IsTotallyComplex L := hc.resolve_left (by simp)
    refine ⟨fun w => ?_⟩
    by_contra hw
    rw [InfinitePlace.not_isComplex_iff_isReal] at hw
    obtain ⟨w', rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := L) w
    have hram : ¬ InfinitePlace.IsUnramified K w' :=
      InfinitePlace.not_isUnramified_iff.2 ⟨hTC.isComplex w', hw⟩
    have hcard := InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two.1 hram
    have hdvd : 2 ∣ Nat.card (L ≃ₐ[K] L) :=
      hcard ▸ Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (L ≃ₐ[K] L) w')
    rw [card_gal_eq_index hL] at hdvd
    have := Nat.Coprime.coprime_dvd_left hdvd hcop
    norm_num at this
  · left
    exact hl.odd_of_ne_two h2

omit [Finite S] in
include hMℓ in
omit [Fact ℓ.Prime] [Finite M] in
/-- For `ℓ` odd, `H²(K_w, M) = 0` at a real place. -/
theorem card_cohomology_two_realLocalModule_eq_one (hodd : Odd ℓ) (w : InfinitePlace K)
    (hw : w.IsReal) : Nat.card (cohomology (realLocalModule ι M w) 2) = 1 := by
  rw [← Nat.card_congr (OrderTwo.h2EquivOfOrderTwo (realLocalModule ι M w)
    (eq_one_or_eq_closureConj w hw) (closureConj_ne_one w hw)).toEquiv]
  exact card_tateQuot_eq_one_of_odd hodd (fun m => hMℓ m)

omit [Finite S] in
omit [IsSmoothRep M] in
/-- The additive function of the base case on the permutation module of `Γ/H`. -/
theorem baseTwistFun_quotient (H : Subgroup (L ≃ₐ[K] L)) :
    (baseTwistFun hL hcop hζ M hMℓ hMP).toFun ((L ≃ₐ[K] L) ⧸ H → ZMod ℓ)
      (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) ((L ≃ₐ[K] L) ⧸ H)) =
      Module.finrank (ULift.{u} (ZMod ℓ))
        (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp H.subtype)) :=
  toFun_invariantsTensorULift_quotient (coprime_card_gal hL hcop) _ H

omit [Finite S] in
omit [IsSmoothRep M] in
theorem baseTwistFun_one :
    (baseTwistFun hL hcop hζ M hMℓ hMP).one =
      Module.finrank (ULift.{u} (ZMod ℓ)) (baseTwistRep hL hζ M hMℓ hMP).invariants :=
  one_invariantsTensorULift (coprime_card_gal hL hcop) _

/-- `d(A₁/ℓ)`, for `A₁ = H¹(G_S(L), 𝒪_Sˣ)`: the exponent of `#Ш²_S(M)` in the base case. -/
def baseShaExponent : ℤ :=
  haveI := finite_cohomology_one_res_maximalSUnits hL
  letI := conjAction (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)) (quotientGalEquiv hL) (maximalSUnitsModule K Ω S) 1
  (baseTwistFun hL hcop hζ M hMℓ hMP).toFun
    (ModN (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) ℓ)
    (modNRep (L ≃ₐ[K] L) _ ℓ)

include hS hcop hζ hMP in
/-- **Tate's base case from the count of `Ш²`.** If `#Ш²_S(M) = ℓ^s` with `s = d(A₁/ℓ)`, the global
Euler characteristic formula holds for `M`. -/
theorem baseCase_globalEulerRatio_of_card_sha
    (hc : ℓ ≠ 2 ∨ IsTotallyComplex L) (s : ℕ) (hsha : Nat.card (sha ι M 2) = ℓ ^ s)
    (hs : (s : ℤ) = baseShaExponent hL hcop hζ M hMℓ hMP) :
    globalEulerRatio ι M = 1 := by
  classical
  have hl : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hl.ne_zero⟩
  have : Finite (zmodRepOfTorsion ℓ M hMℓ) := inferInstanceAs (Finite M)
  have hSM := mem_of_natCard_mem_of_nsmul_eq_zero hS hMℓ
  -- the dimensions of `H⁰`, `H¹`, `H²` and of `M`
  have hcard : ∀ i ≤ 2, Nat.card (cohomology M i) =
      ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (cohomology (zmodRepOfTorsion ℓ M hMℓ) i) := fun i hi => by
    have := finite_cohomology_of_le_two M hSM i hi
    have : Finite (cohomology (zmodRepOfTorsion ℓ M hMℓ) i) := Finite.of_equiv _ (cohomologyZModEquiv ℓ M hMℓ i).toEquiv
    rw [Nat.card_congr (cohomologyZModEquiv ℓ M hMℓ i).toEquiv, natCard_eq_pow_finrank_zmod ℓ]
  have hcardM : Nat.card M = ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := natCard_eq_pow_finrank_zmod ℓ (zmodRepOfTorsion ℓ M hMℓ)
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, ∃ r : ℕ,
      Nat.card (cohomology (realLocalModule ι M w.1) 0) = ℓ ^ r := fun w => by
    have := finite_cohomology_zero (realLocalModule ι M w.1)
    exact exists_card_eq_pow_of_nsmul hl (r := 1) fun x => by
      rw [pow_one]
      exact nsmul_cohomology_eq_zero (realLocalModule ι M w.1) (fun m => hMℓ m) 0 x
  choose r hr using hreal
  rw [globalEulerRatio_eq_one_iff, ProfiniteCohomology.eulerCharacteristic_eq, hcard 0 (by norm_num),
    hcard 1 (by norm_num), hcard 2 (by norm_num), hcardM, Finset.prod_congr rfl fun w _ => by
      rw [hr w]]
  refine div_eq_div_of_exponents hl.pos _ _ _ _ _ r ?_
  -- Tate's computation
  have e0 := baseCase_finrank_zero hS hL hcop hζ M hMℓ hMP
  have e1 := baseCase_finrank_one hS hL hcop hζ M hMℓ hMP
  have eu := baseCase_units hL (baseTwistFun hL hcop hζ M hMℓ hMP)
  have ep := baseCase_picard hL (baseTwistFun hL hcop hζ M hMℓ hMP)
  rw [baseShaExponent] at hs
  -- the count of `H²` from Poitou–Tate
  have hoc := odd_or_isTotallyComplex hL hcop hc
  have hPT := card_cohomology_two_mul_card_dual_zero ι ℓ hS M hMℓ
  have hreal2 : ∏ w : {w : InfinitePlace K // w.IsReal},
      Nat.card (cohomology (realLocalModule ι M w.1) 2) = 1 :=
    Finset.prod_eq_one fun w _ => by
      rcases hoc with hodd | hTC
      · exact card_cohomology_two_realLocalModule_eq_one M hMℓ ι hodd w.1 w.2
      · exact absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (hTC.isComplex w.1))
  rw [hcard 2 (by norm_num), baseCase_card_dual_zero hS hL hcop hζ M hMℓ hMP, hsha, hreal2,
    mul_one, Finset.prod_congr rfl fun v _ => baseCase_card_local_two hS hL hcop hζ M hMℓ hMP ι v.1,
    Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add] at hPT
  have hPT' := Nat.pow_right_injective hl.two_le hPT
  -- the places above `S`
  have hdS := toFun_finitePlacesAbove hL ι (baseTwistFun hL hcop hζ M hMℓ hMP)
  rw [Finset.sum_congr rfl fun v _ => baseTwistFun_quotient hL hcop hζ M hMℓ hMP _] at hdS
  have hd1 := baseTwistFun_one hL hcop hζ M hMℓ hMP
  -- the infinite places
  have hdI := toFun_infinitePlaces hL ι (baseTwistFun hL hcop hζ M hMℓ hMP)
  rw [Finset.sum_congr rfl fun w _ => baseTwistFun_quotient hL hcop hζ M hMℓ hMP _] at hdI
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace K => w.IsReal)] at hdI
  have hdI' : (baseTwistFun hL hcop hζ M hMℓ hMP).toFun (InfinitePlace L → ZMod ℓ)
      (funPermRep (ZMod ℓ) (L ≃ₐ[K] L) (InfinitePlace L)) =
      ∑ w : {w : InfinitePlace K // w.IsReal}, (Module.finrank (ULift.{u} (ZMod ℓ))
        (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
          (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype)) : ℤ) +
      ∑ w : {w : InfinitePlace K // ¬ w.IsReal}, (Module.finrank (ULift.{u} (ZMod ℓ))
        (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
          (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype)) : ℤ) := by
    convert hdI
  have hN : Module.finrank (ULift.{u} (ZMod ℓ)) (homRep (zmodRepOfTorsion ℓ
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ))
      (zmodRepOfTorsion ℓ M hMℓ)) = Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := by
    have : Module.Finite (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := Module.Finite.of_finite
    have : Finite (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))))
    have : Module.Finite (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) := Module.Finite.of_finite
    change Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ) →ₗ[ULift.{u} (ZMod ℓ)] (zmodRepOfTorsion ℓ M hMℓ)) = _
    rw [Module.finrank_linearMap, finrank_zmodRepOfTorsion_rootsOfUnity hS, one_mul]
  have hcx : ∀ w : {w : InfinitePlace K // ¬ w.IsReal},
      Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype)) =
        Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := fun w => by
    have hb := stabilizer_infiniteBasePlace_eq_bot hL ι w.1
      (InfinitePlace.not_isReal_iff_isComplex.1 w.2)
    have hinv : Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype) = ⊤ := by
      rw [eq_top_iff]
      intro f _ g
      have : (g : L ≃ₐ[K] L) = 1 :=
        Subgroup.mem_bot.1 ((SetLike.ext_iff.1 hb g.1).1 g.2)
      change baseTwistRep hL hζ M hMℓ hMP (g : L ≃ₐ[K] L) f = f
      rw [this, map_one, Module.End.one_apply]
    rw [hinv, finrank_top, ← hN]
  have hrl : ∀ w : {w : InfinitePlace K // w.IsReal},
      (Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype)) : ℤ) +
        r w = Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := fun w => by
    have hodd : Odd ℓ := hoc.resolve_right fun hTC =>
      (InfinitePlace.not_isReal_iff_isComplex.2 (hTC.isComplex w.1)) w.2
    have h1 := pow_finrank_stabilizer_eq_card hL hζ M hMℓ hMP ι
      (finrank_zmodRepOfTorsion_rootsOfUnity hS) w.1 w.2
    have h2 := card_cohomology_zero_realLocalModule_eq M ι w.1 w.2
    have h3 := card_eq_card_fixedSub_mul hodd hMℓ (σ := (M.ρ (realConj ι w.1 w.2)).toAddMonoidHom)
      fun x => by
        change M.ρ (realConj ι w.1 w.2) (M.ρ (realConj ι w.1 w.2) x) = x
        rw [← Module.End.mul_apply, ← map_mul, realConj_mul_self, map_one, Module.End.one_apply]
    have h4 : ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) = ℓ ^ (r w + Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants
        ((baseTwistRep hL hζ M hMℓ hMP).comp
          (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype))) := by
      rw [← hcardM, h3, ← h2, hr w, ← h1, pow_add]
    have := Nat.pow_right_injective hl.two_le h4
    omega
  -- assembling
  have hsumr : ∑ w : {w : InfinitePlace K // w.IsReal}, (r w : ℤ) =
      Fintype.card {w : InfinitePlace K // w.IsReal} * Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) -
        ∑ w : {w : InfinitePlace K // w.IsReal}, (Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants
          ((baseTwistRep hL hζ M hMℓ hMP).comp
            (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype)) : ℤ) := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun w _ => (add_comm _ _).trans (hrl w), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hsumc : ∑ w : {w : InfinitePlace K // ¬ w.IsReal}, (Module.finrank (ULift.{u} (ZMod ℓ))
      (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w.1)).subtype)) : ℤ) =
      Fintype.card {w : InfinitePlace K // ¬ w.IsReal} * Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := by
    rw [Finset.sum_congr rfl fun w _ => congrArg (Nat.cast : ℕ → ℤ) (hcx w), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hcardInf : (Fintype.card (InfinitePlace K) : ℤ) =
      Fintype.card {w : InfinitePlace K // w.IsReal} +
        Fintype.card {w : InfinitePlace K // ¬ w.IsReal} := by
    have h1 := Fintype.card_subtype_compl (fun w : InfinitePlace K => w.IsReal)
    have h2 := Fintype.card_subtype_le (fun w : InfinitePlace K => w.IsReal)
    omega
  have hPTz := congrArg (Nat.cast : ℕ → ℤ) hPT'
  push_cast at hPTz hdS hdI hd1 ⊢
  rw [hcardInf]
  linear_combination e0 - e1 + hPTz - eu + hs + ep - hdS + hd1 - hdI' - hsumr - hsumc


end Base

section Statement

/-- **The count of `Ш²` in Tate's base case**: in the situation of the base case, with `L / K` Galois,
`#Ш²_S(M) = ℓ^s` for `s = d(A₁/ℓ)` (`baseShaExponent`), `A₁ = H¹(G_S(L), 𝒪_Sˣ)`. -/
def ShaTwoBaseCountStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ℓ : ℕ) [Fact ℓ.Prime],
    (∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (L : Type u) [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
    [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (hcop : Nat.Coprime (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index ℓ)
    (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ), (ℓ ≠ 2 ∨ IsTotallyComplex L) →
    ∀ (ι : PlaceEmbeddings K Ω) (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
      [IsSmoothRep M] [Finite M] (hMℓ : ∀ m : M, ℓ • m = 0)
      (hMP : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1),
      ∃ s : ℕ, Nat.card (sha ι M 2) = ℓ ^ s ∧ (s : ℤ) = baseShaExponent hL hcop hζ M hMℓ hMP

/-- **Tate's base case** from the nine-term sequence of Poitou–Tate and the count of `Ш²`. -/
theorem globalEulerCharacteristicBase_of_shaTwoBaseCount
    (hsha : ShaTwoBaseCountStatement.{u}) : GlobalEulerCharacteristicBaseStatement.{u} := by
  intro K Ω _ _ _ _ _ S _ ℓ _ hS L _ _ _ _ _ hL hN hcop hζ hc ι M _ _ hMℓ hMP
  have := isGalois_of_fixingOpenSubgroup_normal hL hN
  obtain ⟨s, h1, h2⟩ := hsha K Ω S ℓ hS L hL hcop hζ hc ι M hMℓ hMP
  exact baseCase_globalEulerRatio_of_card_sha hS hL hcop hζ M hMℓ hMP ι hc s h1 h2

end Statement

end

end Langlands.GaloisCohomology
