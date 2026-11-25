import Langlands.GaloisCohomology.Global.Dimension.Statement
import Langlands.GaloisCohomology.Global.Units.HighDegree
import Langlands.GaloisCohomology.Global.Units.Kummer

/-!
# Proof: the `ℓ`-cohomological dimension of `G_S`

* `subsingleton_cohomology_three_rootsOfUnityModule`: `H³(G_S, μ_ℓ) = 0` when `S` contains the places
  above `ℓ` and `ℓ` is odd or `K` totally complex. In the Kummer sequence
  `0 → μ_ℓ → 𝒪_Sˣ → 𝒪_Sˣ → 0` of `K_S` the connecting map `H²(G_S, 𝒪_Sˣ) → H³(G_S, μ_ℓ)` vanishes
  because `H²(G_S, 𝒪_Sˣ)` is `ℓ`-divisible, and `H³(G_S, μ_ℓ) → H³(G_S, 𝒪_Sˣ)` is zero because its
  image is killed by `ℓ` and `H³(G_S, 𝒪_Sˣ)` has no `ℓ`-torsion.
* `subsingleton_cohomology_three_res_rootsOfUnityModule`: the same for every open subgroup of `G_S`,
  which is `G_{S_L}` of a finite extension `L ⊆ K_S` of `K`.
* `cd_galoisGroupUnramifiedOutside_le_two`: `cd_ℓ(G_S) ≤ 2`, through a pro-`ℓ` Sylow subgroup, which
  fixes `μ_ℓ`; `cohomologicalDimensionStatement` proves `CohomologicalDimensionStatement`.
* `eq_zero_of_cohomology_maximalSUnits_of_three_le`: `Hʳ(G_S, 𝒪_Sˣ)(ℓ) = 0` for `r ≥ 3` (same
  conditions on `ℓ`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory CategoryTheory.Limits Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain

universe u

noncomputable section

section RootsOfUnity

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- The module `μ_n` is killed by `n`. -/
theorem nsmul_rootsOfUnityModule_eq_zero (n : ℕ) (a : rootsOfUnityModule F E n) : n • a = 0 := by
  change Additive.ofMul ((Additive.toMul (α := rootsOfUnity n E) a) ^ n) =
    Additive.ofMul (1 : rootsOfUnity n E)
  congr 1
  exact Subtype.ext ((SubgroupClass.coe_pow _ n).trans
    ((mem_rootsOfUnity n _).1 (Additive.toMul a).2))

end RootsOfUnity

section Global

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- `μ_ℓ(K_S) ≅ ℤ/ℓ` when `S` contains the places above `ℓ`. -/
theorem nonempty_zmod_addEquiv_rootsOfUnity_maximal :
    Nonempty (ZMod ℓ ≃+ Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have : IsAlgClosed Ω := IsSepClosed.isAlgClosed_of_perfectField Ω
  have : NeZero (ℓ : Ω) := ⟨Nat.cast_ne_zero.2 hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω ℓ
  have hmem : ζ ∈ maximalUnramifiedOutside K Ω S :=
    mem_maximalUnramifiedOutside_of_pow_eq_one S hℓ.ne_zero (fun v hv h => hv (hS v h))
      hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : maximalUnramifiedOutside K Ω S) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := (maximalUnramifiedOutside K Ω S).val) hζ
      (maximalUnramifiedOutside K Ω S).val.toRingHom.injective
  have hcard := hζ'.card_rootsOfUnity
  have : Finite (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have : Nontrivial (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)
  obtain ⟨η, hη⟩ := exists_ne (1 : rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))
  have hη0 : Additive.ofMul η ≠ 0 := hη
  have hηp : ℓ • Additive.ofMul η = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)) (x := η)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  exact ⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hη0 hηp).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩

include hℓ hS in
/-- **`H³(G_S, μ_ℓ) = 0`** when `S` contains the places above `ℓ` and `ℓ` is odd or `K` is totally
complex. -/
theorem subsingleton_cohomology_three_rootsOfUnityModule (hK : ℓ ≠ 2 ∨ IsTotallyComplex K) :
    Subsingleton (cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 3) := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hnS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  have hX := sUnitsKummerSequence_shortExact S ℓ hnS (Ω := Ω)
  -- the connecting map `H²(G_S, 𝒪_Sˣ) → H³(G_S, μ_ℓ)` vanishes
  have hδ : ∀ y : cohomology (maximalSUnitsModule K Ω S) 2, (δ hX 2 3 rfl).hom y = 0 := by
    intro y
    obtain ⟨y', rfl⟩ := exists_prime_nsmul_eq_cohomology_two_maximalSUnits S hℓ hS hK y
    have e := congrArg (fun F => F.hom y') (comp_δ hX 2 3 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, ModuleCat.hom_zero] at e
    have hg : (coeffMap (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) ℓ).g 2).hom y' =
        ℓ • y' := by
      exact cohomologyMap_nsmul_id_apply _ ℓ 2 y'
    rw [← hg]
    exact e
  suffices hx : ∀ x : cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) 3,
      x = 0 from ⟨fun x y => (hx x).trans (hx y).symm⟩
  intro x
  have hfx : (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) ℓ) 3).hom x = 0 := by
    refine eq_zero_of_cohomology_three_maximalSUnits S hℓ hS _ (k := 1) ?_
    rw [pow_one, ← map_nsmul, nsmul_cohomology_eq_zero _ (nsmul_rootsOfUnityModule_eq_zero ℓ) 3 x,
      map_zero]
  obtain ⟨y, hy⟩ : ∃ y : cohomology (maximalSUnitsModule K Ω S) 2, (δ hX 2 3 rfl).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hX 2 3 rfl) x hfx
  rw [← hy]
  exact hδ y

include hℓ hS in
/-- `H³(U, μ_ℓ) = 0` for every open subgroup `U` of `G_S`: `U` is `G_{S_L}` of a finite extension
`L ⊆ K_S` of `K`, and `μ_ℓ(K_S)` is `μ_ℓ` of the maximal extension of `L` unramified outside the
places above `S`. -/
theorem subsingleton_cohomology_three_res_rootsOfUnityModule (hK : ℓ ≠ 2 ∨ IsTotallyComplex K)
    (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) 3) := by
  obtain ⟨L, _, hL, rfl⟩ := GaloisGroupUnramifiedOutside.exists_fixingOpenSubgroup_eq U
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L), ((ℓ : ℕ) : 𝓞 L) ∈ w.asIdeal →
      w ∈ finitePlacesAbove L S := fun w hw => by
    rw [mem_finitePlacesAbove_iff_under]
    refine hS _ ?_
    change algebraMap (𝓞 K) (𝓞 L) ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  have hKL : ℓ ≠ 2 ∨ IsTotallyComplex L := hK.imp id fun h => by
    have := h
    exact isTotallyComplex_of_algebra K L
  have hμ := subsingleton_cohomology_three_rootsOfUnityModule (Ω := Ω) (finitePlacesAbove L S) hℓ
    hSL hKL
  let e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL
  let ψ := MulEquiv.restrictRootsOfUnity (maximalUnramifiedOutsideEquiv hL).toRingEquiv.toMulEquiv ℓ
  let f : Rep.res e.symm.toMulEquiv.toMonoidHom
      (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) ⟶
      rootsOfUnityModule L (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) ℓ :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm (MulEquiv.toAdditive ψ).toAddMonoidHom,
      fun τ => LinearMap.ext fun x => by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Units.ext
        apply Subtype.ext
        exact (GaloisGroupUnramifiedOutside.coe_fixingOpenSubgroupEquiv_symm_apply hL τ _)⟩
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous f
    (MulEquiv.toAdditive ψ).bijective 3
  have hinj : Function.Injective
      (map ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩ f 3).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact hinj.subsingleton

include hℓ hS in
/-- **`cd_ℓ(G_S) ≤ 2`** when `S` contains the places above `ℓ` and `ℓ` is odd or `K` is totally
complex. -/
theorem cd_galoisGroupUnramifiedOutside_le_two (hK : ℓ ≠ 2 ∨ IsTotallyComplex K) :
    cd ℓ (GaloisGroupUnramifiedOutside K Ω S) ≤ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨P, hP⟩ := exists_isProSylow (G := GaloisGroupUnramifiedOutside K Ω S) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cd_eq_of_isProSylow hℓ hP]
  change cd ℓ P ≤ ((2 : ℕ) : ℕ∞)
  rw [cd_le_iff_of_isProPGroup hℓ hP.2.1 2]
  have hμ : Subsingleton (cohomology (Rep.res P.subtype
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) 3) := by
    suffices h : ∀ x : cohomology (Rep.res P.subtype
        (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)) 3, x = 0 from
      ⟨fun x y => (h x).trans (h y).symm⟩
    intro x
    obtain ⟨U, hU, hPU, y, rfl⟩ :=
      exists_resOfLE_eq (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) hP.1 3 x
    have := subsingleton_cohomology_three_res_rootsOfUnityModule S hℓ hS hK ⟨U, hU⟩
    rw [Subsingleton.elim y 0, map_zero]
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity_maximal (Ω := Ω) S hℓ hS
  have hfix : ∀ (σ : P) (x : Additive (rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S))),
      (Rep.res P.subtype (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine apply_eq_of_isProPGroup hℓ hP.2.1 σ.2 ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ _).1 (Additive.toMul x).2, Units.val_one]
  let ψ : Rep.trivial (ULift.{u} ℤ) P (ULift.{u} (ZMod ℓ)) ⟶
      Rep.res P.subtype (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{u} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom),
      fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩
  let ψ' : Rep.res P.subtype (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) ⟶
      Rep.trivial (ULift.{u} ℤ) P (ULift.{u} (ZMod ℓ)) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      ((AddEquiv.ulift : ULift.{u} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp
        e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change ULift.up (e.symm ((Rep.res P.subtype
          (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)).ρ σ x)) = ULift.up (e.symm x)
        rw [hfix]⟩
  have hcomp : ψ ≫ ψ' = 𝟙 _ := by
    ext x
    change e.symm (e x.down) = x.down
    exact e.symm_apply_apply x.down
  have hinj : Function.Injective (coeffMap ψ 3).hom := fun x y h => by
    have h' := congrArg (coeffMap ψ' 3).hom h
    rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← coeffMap_comp, hcomp,
      coeffMap_id, ModuleCat.id_apply, ModuleCat.id_apply] at h'
  exact hinj.subsingleton

end Global

/-- **`CohomologicalDimensionStatement` holds.** -/
theorem cohomologicalDimensionStatement : CohomologicalDimensionStatement.{u} :=
  fun _ _ _ _ _ _ _ S _ hℓ hS hK => cd_galoisGroupUnramifiedOutside_le_two S hℓ hS hK

section SUnits

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K))) {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

include hℓ hS in
/-- **`Hʳ(G_S, 𝒪_Sˣ)(ℓ) = 0` for `r ≥ 3`** when `S` contains the places above `ℓ` and `ℓ` is odd or
`K` is totally complex: multiplication by `ℓ` is injective on `Hʳ(G_S, 𝒪_Sˣ)` because
`Hʳ(G_S, μ_ℓ) = 0`. -/
theorem eq_zero_of_cohomology_maximalSUnits_of_three_le (hK : ℓ ≠ 2 ∨ IsTotallyComplex K) {r : ℕ}
    (hr : 3 ≤ r) (x : cohomology (maximalSUnitsModule K Ω S) r) {k : ℕ} (hx : ℓ ^ k • x = 0) :
    x = 0 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hnS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K) ∉ v.asIdeal := fun v hv h => hv (hS v h)
  have hX := sUnitsKummerSequence_shortExact S ℓ hnS (Ω := Ω)
  have hμ : Subsingleton (cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) r) :=
    cohomologicalDimensionStatement.subsingleton_cohomology_of_three_le S hℓ.ne_zero hS
      (hK.imp hℓ.odd_of_ne_two id) (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_rootsOfUnityModule_eq_zero ℓ) hr
  have h1 : ∀ y : cohomology (maximalSUnitsModule K Ω S) r, ℓ • y = 0 → y = 0 := by
    intro y hy
    have hg : (coeffMap (sUnitsKummerSequence S (maximalUnramifiedOutside K Ω S) ℓ).g r).hom y = 0 :=
      (cohomologyMap_nsmul_id_apply _ ℓ r y).trans hy
    obtain ⟨z, hz⟩ : ∃ z : cohomology (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) r,
        (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) ℓ) r).hom z = y :=
      (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₂ hX r) y hg
    rw [← hz, Subsingleton.elim z 0, map_zero]
  have key : ∀ (j : ℕ) (y : cohomology (maximalSUnitsModule K Ω S) r), ℓ ^ j • y = 0 → y = 0 := by
    intro j
    induction j with
    | zero =>
      intro y hy
      rwa [pow_zero, one_smul] at hy
    | succ j ih =>
      intro y hy
      exact ih y (h1 _ (by rw [smul_smul, ← pow_succ']; exact hy))
  exact key k x hx

end SUnits

end

end Langlands.GaloisCohomology
