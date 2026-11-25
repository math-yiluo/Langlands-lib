import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.InfiniteCount

/-!
# The real places in Tate's base case

In the situation of Tate's base case with `ℓ` odd, let `w` be a real place of `K`, `c ∈ G_S` the
complex conjugation at `w` and `τ_w` its restriction to `L`. Then `c` acts on `μ_ℓ` by inversion
(`rootsOfUnity_realConj`), so a homomorphism `f : μ_ℓ → M` is fixed by `τ_w` exactly when its value
at a generator lies in `M^{c = -1}`, and `#M = #M^{c} · #M^{c = -1}` (`ℓ` odd). With
`H⁰(K_w, M) = M^c` this gives
`#H⁰(K_w, M) · ℓ^{dim N^{Stab(w̃_w)}} = #M` (`baseCase_card_real`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local Representation Module Involution

universe u

noncomputable section

section OddInvolution

variable {M : Type*} [AddCommGroup M] [Finite M] {σ : M →+ M}

omit [Finite M] in
/-- For an involution of a group killed by an odd number, `M^σ/(1 + σ)M` is trivial. -/
theorem card_tateQuot_eq_one_of_odd {ℓ : ℕ} (hℓ : Odd ℓ) (hM : ∀ m : M, ℓ • m = 0) :
    Nat.card (tateQuot σ) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
  obtain ⟨k, hk⟩ := hℓ
  have key : ∀ q : tateQuot σ, q = 0 := fun q => by
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [QuotientAddGroup.eq_zero_iff]
      refine AddSubgroup.mem_addSubgroupOf.2 (mem_traceSub.2 ⟨(k + 1) • (x : M), ?_⟩)
      have hx : σ (x : M) = x := mem_fixedSub.1 x.2
      rw [map_nsmul, hx, ← add_nsmul]
      have hl : ℓ • (x : M) = 0 := hM x
      rw [hk] at hl
      calc (k + 1 + (k + 1)) • (x : M) = (2 * k + 1) • (x : M) + (x : M) := by
            rw [← succ_nsmul]
            ring_nf
        _ = x := by rw [hl, zero_add]
  exact (key a).trans (key b).symm

omit [Finite M] in
/-- For an involution of a finite group killed by an odd number:
`#M = #M^σ · #M^{-σ}`. -/
theorem card_eq_card_fixedSub_mul {ℓ : ℕ} (hℓ : Odd ℓ) (hM : ∀ m : M, ℓ • m = 0)
    (hσ : ∀ x, σ (σ x) = x) :
    Nat.card M = Nat.card (fixedSub σ) * Nat.card (fixedSub (-σ)) := by
  have h := card_tateQuot_mul_card hσ
  have h1 : Nat.card (tateQuot σ) = 1 := card_tateQuot_eq_one_of_odd hℓ hM
  rw [h1, one_mul] at h
  exact h

end OddInvolution

section Real

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

/-- The complex conjugation of `G_S` at a real place `w`. -/
abbrev realConj (w : InfinitePlace K) (hw : w.IsReal) : GaloisGroupUnramifiedOutside K Ω S :=
  realLocalizationHom ι S w (closureConj w hw)

theorem realConj_mul_self (w : InfinitePlace K) (hw : w.IsReal) :
    realConj (S := S) ι w hw * realConj ι w hw = 1 := by
  rw [realConj, ← map_mul]
  rcases eq_one_or_eq_closureConj w hw (closureConj w hw * closureConj w hw) with h | h
  · rw [h, map_one]
  · exfalso
    have : closureConj w hw = 1 := by
      have h' := congrArg (fun g => (closureConj w hw)⁻¹ * g) h
      simpa using h'
    exact closureConj_ne_one w hw this

/-- Complex conjugation inverts the roots of unity of `K_S`. -/
theorem rootsOfUnity_realConj (w : InfinitePlace K) (hw : w.IsReal) (n : ℕ) (hn : 0 < n)
    (t : rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) n) :
    (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) n).ρ (realConj ι w hw) t = -t := by
  rw [rootsOfUnityModule_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  apply (ι.infinite w).toRingHom.injective
  change ι.infinite w (((realLocalizationHom ι S w (closureConj w hw))
      (((Additive.toMul t : rootsOfUnity n (maximalUnramifiedOutside K Ω S)) :
        (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) :
          maximalUnramifiedOutside K Ω S) : Ω) = ι.infinite w ((((Additive.toMul t)⁻¹ :
        rootsOfUnity n (maximalUnramifiedOutside K Ω S)) : (maximalUnramifiedOutside K Ω S)ˣ) :
          maximalUnramifiedOutside K Ω S)
  rw [realLocalizationHom_apply]
  let t' : rootsOfUnity n (maximalUnramifiedOutside K Ω S) :=
    Additive.toMul (α := rootsOfUnity n (maximalUnramifiedOutside K Ω S)) t
  let ζ : (AlgebraicClosure w.Completion)ˣ := Units.map
    ((ι.infinite w).comp (maximalUnramifiedOutside K Ω S).val : _ →* _)
    (t' : (maximalUnramifiedOutside K Ω S)ˣ)
  have hζ : ζ ^ n = 1 := by
    rw [← map_pow]
    have h1 : (t' : (maximalUnramifiedOutside K Ω S)ˣ) ^ n = 1 := (mem_rootsOfUnity n _).1 t'.2
    rw [h1, map_one]
  have := closureConj_apply_of_pow_eq_one w hw ζ hn hζ
  exact this.trans (by simp [ζ, t'])

end Real

section BaseReal

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] {ℓ : ℕ} [Fact ℓ.Prime]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  {L : Type u} [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
  (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hMℓ : ∀ m : M, ℓ • m = 0)
  (hMP : ∀ g ∈ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)), M.ρ g = 1)
  (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

omit [Finite S] [Finite M] in
/-- `H⁰(K_w, M) = M^c` at a real place. -/
theorem card_cohomology_zero_realLocalModule_eq (w : InfinitePlace K) (hw : w.IsReal) :
    Nat.card (cohomology (realLocalModule ι M w) 0) =
      Nat.card (fixedSub (M.ρ (realConj ι w hw)).toAddMonoidHom) := by
  rw [Nat.card_congr (zeroIso _).toLinearEquiv.toEquiv]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
  rw [mem_fixedSub, Representation.mem_invariants]
  constructor
  · intro h
    exact h (closureConj w hw)
  · intro h g
    rcases eq_one_or_eq_closureConj w hw g with rfl | rfl
    · change M.ρ (realLocalizationHom ι S w 1) m = m
      rw [map_one, map_one, Module.End.one_apply]
    · exact h

omit [Finite S] in
include hζ hMP in
omit [IsSmoothRep M] in
/-- At a real place, `ℓ^{dim N^{Stab(w̃_w)}} = #M^{c = -1}` (`ℓ` odd). -/
theorem pow_finrank_stabilizer_eq_card (hTr : Module.finrank (ULift.{u} (ZMod ℓ))
      (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
        (nsmul_galRootsOfUnity_eq_zero ℓ)) = 1)
    (w : InfinitePlace K) (hw : w.IsReal) :
    ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants
      ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w)).subtype)) =
      Nat.card (fixedSub (-(M.ρ (realConj ι w hw)).toAddMonoidHom)) := by
  have hl : ℓ.Prime := Fact.out
  let T := zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
    (nsmul_galRootsOfUnity_eq_zero ℓ)
  let Mk := zmodRepOfTorsion ℓ M hMℓ
  have : Finite Mk := inferInstanceAs (Finite M)
  have : Finite T := inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))))
  have : Finite (T →ₗ[ULift.{u} (ZMod ℓ)] Mk) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
      (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w)).subtype)) := Subtype.finite
  rw [← natCard_eq_pow_finrank_zmod ℓ]
  let b := Module.finBasisOfFinrankEq (ULift.{u} (ZMod ℓ)) T hTr
  have hc : b.coord 0 (b 0) = 1 := by simp
  have hT : ∀ y : T, y = b.coord 0 y • b 0 := fun y => by
    conv_lhs => rw [← b.sum_repr y]
    simp
  let c := realConj (S := S) ι w hw
  have hcc : c⁻¹ = c := inv_eq_of_mul_eq_one_right (realConj_mul_self ι w hw)
  -- the action of `τ_w` on `N = Hom(μ_ℓ, M)`
  have hτ : ∀ f : T →ₗ[ULift.{u} (ZMod ℓ)] Mk, ∀ t : T,
      (baseTwistRep hL hζ M hMℓ hMP (realConjRestrict hL ι w hw) f) t = -(Mk.ρ c (f t)) := by
    intro f t
    have e1 : realConjRestrict hL ι w hw = quotientGalEquiv hL (QuotientGroup.mk c) := rfl
    rw [e1, twistRep_apply, homRep_ρ_apply, LinearMap.comp_apply, LinearMap.comp_apply, hcc]
    have h2 : T.ρ c t = -t := rootsOfUnity_realConj ι w hw ℓ hl.pos t
    change Mk.ρ c (f (T.ρ c t)) = _
    rw [h2, map_neg, map_neg]
  have hmem : ∀ f : T →ₗ[ULift.{u} (ZMod ℓ)] Mk,
      f ∈ Representation.invariants ((baseTwistRep hL hζ M hMℓ hMP).comp
        (MulAction.stabilizer (L ≃ₐ[K] L) (infiniteBasePlace hL ι w)).subtype) ↔
        -(Mk.ρ c (f (b 0))) = f (b 0) := by
    intro f
    rw [Representation.mem_invariants]
    constructor
    · intro h
      have := h ⟨realConjRestrict hL ι w hw,
        (mem_stabilizer_infiniteBasePlace_iff hL ι w hw _).2 (Or.inr rfl)⟩
      rw [← hτ f (b 0)]
      exact LinearMap.congr_fun this (b 0)
    · intro h γ
      rcases (mem_stabilizer_infiniteBasePlace_iff hL ι w hw γ.1).1 γ.2 with h1 | h1
      · change baseTwistRep hL hζ M hMℓ hMP γ.1 f = f
        rw [h1, map_one, Module.End.one_apply]
      · change baseTwistRep hL hζ M hMℓ hMP γ.1 f = f
        rw [h1]
        ext t
        rw [hτ, hT t, map_smul, map_smul, ← smul_neg, h]
  refine Nat.card_congr
    { toFun := fun f => ⟨f.1 (b 0), mem_fixedSub.2 ((hmem f.1).1 f.2)⟩
      invFun := fun m => ⟨(b.coord 0).smulRight (show (Mk : Type u) from m.1), (hmem _).2 (by
        rw [LinearMap.smulRight_apply, hc, one_smul]
        exact mem_fixedSub.1 m.2)⟩
      left_inv := fun f => Subtype.ext (LinearMap.ext fun t => by
        rw [LinearMap.smulRight_apply]
        conv_rhs => rw [hT t]
        rw [map_smul])
      right_inv := fun m => Subtype.ext (by
        change (b.coord 0).smulRight (show (Mk : Type u) from m.1) (b 0) = m.1
        rw [LinearMap.smulRight_apply, hc, one_smul]) }

end BaseReal

end

end Langlands.GaloisCohomology
