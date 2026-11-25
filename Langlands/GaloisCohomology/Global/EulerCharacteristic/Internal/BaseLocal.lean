import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.LocalCount
import Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality

/-!
# The dual module and the local terms in Tate's base case: the counts

In the situation of `BaseDegrees.lean`, with `N = Hom(μ_ℓ, M)` as a representation of
`Γ = Gal(L/K)` (`twistRep`) and `D_v ⊆ Γ` the decomposition group at a finite place `v`:

* `#H⁰(G_S, M') = ℓ^{dim N^Γ}` for `M' = Hom(M, μ_ℓ)` (`baseCase_card_dual_zero`);
* `#H²(K_v, M) = ℓ^{dim N^{D_v}}` (`baseCase_card_local_two`), through local duality
  `#H²(K_v, M) = #H⁰(K_v, M^∨)` with the Cartier dual `M^∨ = Hom(M, K̄_vˣ)`, whose invariants are the
  `G_{K_v}`-homomorphisms `M → μ_ℓ(K̄_v) ≅ μ_ℓ(K_S)` (`homEquivLocalUnits`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local Representation Module

universe u

noncomputable section

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

attribute [local instance 2000] IsSepClosure.isGalois

/-- The roots of unity of `K_S` form a finite module. -/
instance finite_rootsOfUnityModule_maximal (n : ℕ) [NeZero n] :
    Finite (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) n) :=
  inferInstanceAs (Finite (Additive (rootsOfUnity n (maximalUnramifiedOutside K Ω S))))

/-- The representation `N = Hom(μ_ℓ, M)` of `Γ = Gal(L/K)` of the base case. -/
abbrev baseTwistRep :=
  twistRep (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (quotientGalEquiv hL) ℓ
    (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) M (nsmul_galRootsOfUnity_eq_zero ℓ) hMℓ
    (rootsOfUnity_res_trivial hL hζ) (res_apply_eq_of_trivial hL M hMP)

omit [Finite S] [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] [IsSmoothRep M] [Finite M] in
/-- The surjection `G_S → Gal(L/K)` through the quotient is the restriction. -/
theorem quotHom_quotientGalEquiv [IsGalois K L] [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
    Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal] :
    quotHom (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL) (quotientGalEquiv hL) =
      Galois.galRestrict hL :=
  MonoidHom.ext fun _ => rfl

include hS hcop in
omit [Finite S] in
/-- **The dual module.** `#H⁰(G_S, M') = ℓ^{dim N^Γ}` for `M' = Hom(M, μ_ℓ)`. -/
theorem baseCase_card_dual_zero :
    Nat.card (cohomology (PoitouTate.dual ℓ M) 0) =
      ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (baseTwistRep hL hζ M hMℓ hMP).invariants := by
  have hl : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hl.ne_zero⟩
  let T := rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ
  have h1 : Nat.card (cohomology (PoitouTate.dual ℓ M) 0) = Nat.card (M ⟶ T) :=
    Nat.card_congr ((zeroIso _).toLinearEquiv.toEquiv.trans
      (linHom.invariantsEquivRepHom M T).toEquiv)
  have h2 : Nat.card (M ⟶ T) = Nat.card (Rep.res (MonoidHom.id _) M ⟶ Rep.res (MonoidHom.id _) T) :=
    Nat.card_congr (Equiv.refl _)
  rw [h1, h2, card_hom_res_eq_pow (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
    (quotientGalEquiv hL) ℓ T M (nsmul_galRootsOfUnity_eq_zero ℓ) hMℓ (rootsOfUnity_res_trivial hL hζ)
    (res_apply_eq_of_trivial hL M hMP) (finrank_zmodRepOfTorsion_rootsOfUnity hS)
    (coprime_card_gal hL hcop) (MonoidHom.id _)]
  congr 1
  have hr : ((quotHom (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
      (quotientGalEquiv hL)).comp (MonoidHom.id _)).range = ⊤ := by
    rw [MonoidHom.comp_id, quotHom_quotientGalEquiv]
    exact MonoidHom.range_eq_top.2 (galRestrict_surjective hL)
  have : ∀ (σ : Representation (ULift.{u} (ZMod ℓ)) (L ≃ₐ[K] L)
      (homRep (zmodRepOfTorsion ℓ T (nsmul_galRootsOfUnity_eq_zero ℓ)) (zmodRepOfTorsion ℓ M hMℓ)))
      (H : Subgroup (L ≃ₐ[K] L)), H = ⊤ →
      Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants (σ.comp H.subtype)) =
        Module.finrank (ULift.{u} (ZMod ℓ)) σ.invariants := by
    rintro σ H rfl
    have hinv : Representation.invariants (σ.comp (⊤ : Subgroup (L ≃ₐ[K] L)).subtype) =
        σ.invariants := by
      ext n
      exact ⟨fun h g => h ⟨g, trivial⟩, fun h g => h g⟩
    rw [hinv]
  exact this _ _ hr

section Local

variable (ι : PlaceEmbeddings K Ω)

include hS hMℓ in
omit [Finite S] [IsSmoothRep M] [Finite M] in
/-- `Hom_{G_v}(M, μ_ℓ(K_S)) ≅ Hom_{G_v}(M, K̄_vˣ)`: the homomorphisms of a module killed by `ℓ` into
`K̄_vˣ` take values in `μ_ℓ(K̄_v)`, which is `ι_v(μ_ℓ(K_S))`. -/
theorem comp_rootsOfUnityLocalHom_bijective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Bijective (fun f : localModule ι M v ⟶
        localModule ι (PoitouTate.dualizingModule K Ω S ℓ) v =>
      f ≫ PoitouTate.rootsOfUnityLocalHom ι S ℓ v) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hinj := rootsOfUnityLocalHom_injective ι ℓ (S := S) v
  constructor
  · intro f f' h
    ext m
    exact hinj (congrArg (fun φ => φ.hom m) h)
  · intro g
    have htors : ∀ m, ℓ • g.hom m = 0 := fun m => by
      rw [← map_nsmul]
      have : ℓ • m = 0 := hMℓ m
      rw [this, map_zero]
    choose pre hpre using fun m => exists_rootsOfUnityLocalHom_eq ι ℓ hS v (g.hom m) (htors m)
    let f0 : localModule ι M v →+ localModule ι (PoitouTate.dualizingModule K Ω S ℓ) v :=
      { toFun := pre
        map_zero' := hinj (by rw [hpre, map_zero, map_zero])
        map_add' := fun a b => hinj (by rw [map_add, hpre, hpre, hpre, map_add]) }
    refine ⟨Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm f0, fun σ => LinearMap.ext fun m =>
      hinj ?_⟩, ?_⟩
    · change (PoitouTate.rootsOfUnityLocalHom ι S ℓ v).hom (pre ((localModule ι M v).ρ σ m)) =
        (PoitouTate.rootsOfUnityLocalHom ι S ℓ v).hom
          ((localModule ι (PoitouTate.dualizingModule K Ω S ℓ) v).ρ σ (pre m))
      rw [hpre, Rep.hom_comm_apply g, Rep.hom_comm_apply (PoitouTate.rootsOfUnityLocalHom ι S ℓ v),
        hpre]
    · ext m
      exact hpre m

include hS hcop in
omit [Finite S] in
/-- **The local terms.** `#H²(K_v, M) = ℓ^{dim N^{D_v}}` at a finite place `v`. -/
theorem baseCase_card_local_two (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (cohomology (localModule ι M v) 2) =
      ℓ ^ Module.finrank (ULift.{u} (ZMod ℓ)) (Representation.invariants
        ((baseTwistRep hL hζ M hMℓ hMP).comp (decompositionGroup hL ι v).subtype)) := by
  have hl : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hl.ne_zero⟩
  let T := PoitouTate.dualizingModule K Ω S ℓ
  let := Langlands.Global.FiniteCompletion.valuativeRel v
  let := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  have : Finite (localModule ι M v) := inferInstanceAs (Finite M)
  have : IsSmoothRep (localModule ι M v) := inferInstance
  have : IsSmoothRep (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι M v)) := isSmoothRep_cartierDual (localModule ι M v)
  -- local duality
  have hb := tatePairing_bijective (K := v.adicCompletion K)
    (Ksep := AlgebraicClosure (v.adicCompletion K)) (localModule ι M v)
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (show 2 + 0 = 2 from rfl)
  have e1 : cohomology (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι M v)) 0 ≃ (localModule ι M v ⟶ localModule ι T v) :=
    ((zeroIso _).toLinearEquiv.toEquiv.trans (linHom.invariantsEquivRepHom (localModule ι M v)
      (unitsModule (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)))).toEquiv).trans
      (Equiv.ofBijective _ (comp_rootsOfUnityLocalHom_bijective hS M hMℓ ι v)).symm
  have : Finite (localModule ι M v ⟶ localModule ι T v) := by
    have : Finite (localModule ι M v →ₗ[ULift.{u} ℤ] localModule ι T v) := by
      have : Finite (localModule ι M v) := inferInstanceAs (Finite M)
      have : Finite (localModule ι T v) :=
        inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))))
      exact Finite.of_injective _ DFunLike.coe_injective
    have : Finite (linHom (localModule ι M v).ρ (localModule ι T v).ρ).invariants := Subtype.finite
    exact Finite.of_equiv _ (linHom.invariantsEquivRepHom (localModule ι M v)
      (localModule ι T v)).toEquiv
  have : Finite (cohomology (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
      (localModule ι M v)) 0) := Finite.of_equiv _ e1.symm
  have h1 : Nat.card (cohomology (localModule ι M v) 2) =
      Nat.card (cohomology (cartierDual (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K))
        (localModule ι M v)) 0) :=
    (Nat.card_congr (Equiv.ofBijective _ hb)).trans (QZ.card_hom (G := cohomology _ 0))
  rw [h1, Nat.card_congr e1]
  refine (card_hom_res_eq_pow (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL)
    (quotientGalEquiv hL) ℓ T M (nsmul_galRootsOfUnity_eq_zero ℓ) hMℓ (rootsOfUnity_res_trivial hL hζ)
    (res_apply_eq_of_trivial hL M hMP) (finrank_zmodRepOfTorsion_rootsOfUnity hS)
    (coprime_card_gal hL hcop)
    (localizationHom ι S v : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
      GaloisGroupUnramifiedOutside K Ω S)).trans ?_
  rw [quotHom_quotientGalEquiv]
  rfl

end Local

end

end Langlands.GaloisCohomology
