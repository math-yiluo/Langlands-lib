import Langlands.Cohomology.Profinite.Dimension.Subgroup
import Langlands.Cohomology.Profinite.Dimension.Sylow
import Langlands.Cohomology.Profinite.Duality.Main
import Langlands.GaloisCohomology.Local.Finiteness

/-!
# Cohomological dimension of a local field, vanishing and finiteness

For a nonarchimedean local field `K` and a prime `ℓ` invertible in `K`,
`cd_ℓ Gal(Ksep/K) ≤ 2` (`cd_le_two`). The proof: a pro-`ℓ` Sylow subgroup `P` acts trivially on
`μ_ℓ ≅ ℤ/ℓ`, so `H³(P, ℤ/ℓ)` is a direct summand of `H³(P, μ_ℓ)`, which is a limit of the groups
`H³(U, μ_ℓ)` of open subgroups `U ⊇ P`; these vanish by the Kummer sequence and `H³(U, Ksepˣ) = 0`.

Consequences: for `n` invertible in `K` and a smooth `n`-torsion module `M`, `Hʳ(U, M) = 0` for
every open subgroup `U` and `r ≥ 3` (`subsingleton_cohomology_of_three_le`); for a finite smooth
module `M` of order invertible in `K`, every `Hʳ(Gal(Ksep/K), M)` is finite (`finite_cohomology`).
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology ClassFieldTheory.Local

/-- If `n • x = 0` and every `ℓ`-primary component with `ℓ ∣ n` vanishes, then `x = 0`. -/
theorem eq_zero_of_primaryComponent_eq_bot {M : Type*} [AddCommGroup M] :
    ∀ (n : ℕ), n ≠ 0 → (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → AddCommGroup.primaryComponent M ℓ = ⊥) →
      ∀ x : M, n • x = 0 → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn h x hx
  rcases eq_or_ne n 1 with rfl | h1
  · rwa [one_nsmul] at hx
  set ℓ := n.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime h1
  obtain ⟨n', hn'⟩ : ℓ ∣ n := Nat.minFac_dvd n
  have hn'0 : n' ≠ 0 := fun h0 => hn (by rw [hn', h0, mul_zero])
  have hy : n' • x = 0 := by
    refine (primaryComponent_eq_bot_iff.1 (h ℓ hℓ ⟨n', hn'⟩)) (n' • x) ⟨1, ?_⟩
    rw [pow_one, smul_smul, ← hn', hx]
  refine ih n' ?_ hn'0 (fun q hq hqn => h q hq (hqn.trans ⟨ℓ, by rw [hn', mul_comm]⟩)) x hy
  rw [hn']
  exact lt_mul_left (Nat.pos_of_ne_zero hn'0) hℓ.one_lt

section Sylow

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem rootsOfUnityFixing_normal {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsIntegral F E] (n : ℕ) [NeZero n] :
    ((rootsOfUnityFixing F E n : OpenSubgroup Gal(E/F)) : Subgroup Gal(E/F)).Normal := by
  constructor
  intro σ hσ τ
  refine Subgroup.mem_iInf.2 fun x => ?_
  have h1 := Subgroup.mem_iInf.1 hσ ((rootsOfUnityModule F E n).ρ τ⁻¹ x)
  change (rootsOfUnityModule F E n).ρ (τ * σ * τ⁻¹) x = x
  change (rootsOfUnityModule F E n).ρ σ ((rootsOfUnityModule F E n).ρ τ⁻¹ x) =
    (rootsOfUnityModule F E n).ρ τ⁻¹ x at h1
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h1,
    Representation.self_inv_apply]

/-- `rootsOfUnityFixing` as an open normal subgroup. -/
def rootsOfUnityFixingNormal (n : ℕ) [NeZero n] : OpenNormalSubgroup Gal(Ksep/K) :=
  { rootsOfUnityFixing K Ksep n with isNormal' := rootsOfUnityFixing_normal n }

/-- A pro-`ℓ` subgroup of `Gal(E/F)` fixes the `ℓ`-th roots of unity of `E`. -/
theorem apply_eq_of_isProPGroup {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsIntegral F E] [CompactSpace Gal(E/F)] [TotallyDisconnectedSpace Gal(E/F)] {ℓ : ℕ}
    (hℓ : ℓ.Prime) {P : Subgroup Gal(E/F)} (hP : IsProPGroup ℓ P) {σ : Gal(E/F)} (hσ : σ ∈ P)
    {ζ : E} (hζ : ζ ^ ℓ = 1) : σ ζ = ζ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  let W : OpenNormalSubgroup Gal(E/F) :=
    { rootsOfUnityFixing F E ℓ with isNormal' := rootsOfUnityFixing_normal ℓ }
  have : ((rootsOfUnityFixing F E ℓ : OpenSubgroup Gal(E/F)) : Subgroup Gal(E/F)).Normal :=
    rootsOfUnityFixing_normal ℓ
  obtain ⟨k, hk⟩ := (isProPGroup_subgroup_iff_isPGroup_map.1 hP W)
    ⟨QuotientGroup.mk' (W : Subgroup Gal(E/F)) σ, Subgroup.mem_map_of_mem _ hσ⟩
  have hmem : σ ^ ℓ ^ k ∈ rootsOfUnityFixing F E ℓ := by
    have h := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, ← map_pow] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hfixk : (σ ^ ℓ ^ k) ζ = ζ := apply_eq_of_mem_rootsOfUnityFixing hmem hζ
  have hu : IsUnit ζ := IsUnit.of_pow_eq_one hζ hℓ.ne_zero
  obtain ⟨m, hm⟩ := map_rootsOfUnity_eq_pow_self σ
    (⟨hu.unit, (mem_rootsOfUnity ℓ _).2 (Units.ext (by simpa using hζ))⟩ : rootsOfUnity ℓ E)
  have hm' : σ ζ = ζ ^ m := hm
  have hpow : ∀ j : ℕ, (σ ^ j) ζ = ζ ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hm', ← pow_mul, ← pow_succ']
  have hmodpow : ∀ a : ℕ, ζ ^ a = ζ ^ (a % ℓ) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a ℓ, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hmod : m ^ ℓ ^ k % ℓ = m % ℓ := by
    have h := ZMod.pow_card_pow (p := ℓ) (n := k) (m : ZMod ℓ)
    rw [← Nat.cast_pow] at h
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  calc σ ζ = ζ ^ m := hm'
    _ = ζ ^ (m ^ ℓ ^ k) := by rw [hmodpow m, hmodpow (m ^ ℓ ^ k), hmod]
    _ = (σ ^ ℓ ^ k) ζ := (hpow _).symm
    _ = ζ := hfixk

variable (K Ksep) in
/-- For `ℓ` prime and invertible in `K`, `μ_ℓ(Ksep) ≅ ℤ/ℓ`. -/
theorem nonempty_zmod_addEquiv_rootsOfUnity {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) :
    Nonempty (ZMod ℓ ≃+ Additive (rootsOfUnity ℓ Ksep)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard := natCard_rootsOfUnity_of_ne_zero K Ksep hℓK
  have : Finite (rootsOfUnity ℓ Ksep) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have : Nontrivial (rootsOfUnity ℓ Ksep) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity ℓ Ksep)
  have hζ0 : Additive.ofMul ζ ≠ 0 := hζ
  have hζp : ℓ • Additive.ofMul ζ = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity ℓ Ksep) (x := ζ)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  exact ⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hζ0 hζp).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩

end Sylow

namespace Local

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- **Cohomological dimension 2**: for a prime `ℓ` invertible in `K`, `cd_ℓ Gal(Ksep/K) ≤ 2`. -/
theorem cd_le_two {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : (ℓ : K) ≠ 0) : cd ℓ Gal(Ksep/K) ≤ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨P, hP⟩ := exists_isProSylow (G := Gal(Ksep/K)) (p := ℓ)
  have : CompactSpace P := isCompact_iff_compactSpace.1 hP.1.isCompact
  rw [← cd_eq_of_isProSylow hℓ hP]
  change cd ℓ P ≤ ((2 : ℕ) : ℕ∞)
  rw [cd_le_iff_of_isProPGroup hℓ hP.2.1 2]
  have hμ : Subsingleton (cohomology (Rep.res P.subtype (rootsOfUnityModule K Ksep ℓ)) 3) := by
    suffices h : ∀ x : cohomology (Rep.res P.subtype (rootsOfUnityModule K Ksep ℓ)) 3, x = 0 from
      ⟨fun x y => (h x).trans (h y).symm⟩
    intro x
    obtain ⟨U, hU, hPU, y, rfl⟩ := exists_resOfLE_eq (rootsOfUnityModule K Ksep ℓ) hP.1 3 x
    have := subsingleton_cohomology_three_res_rootsOfUnityModule K Ksep hℓK ⟨U, hU⟩
    rw [Subsingleton.elim y 0, map_zero]
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ksep hℓ hℓK
  have hfix : ∀ (σ : P) (x : Additive (rootsOfUnity ℓ Ksep)),
      (Rep.res P.subtype (rootsOfUnityModule K Ksep ℓ)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine apply_eq_of_isProPGroup hℓ hP.2.1 σ.2 ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity ℓ _).1 (Additive.toMul x).2, Units.val_one]
  let ψ : Rep.trivial (ULift.{u} ℤ) P (ULift.{u} (ZMod ℓ)) ⟶
      Rep.res P.subtype (rootsOfUnityModule K Ksep ℓ) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      (e.toAddMonoidHom.comp (AddEquiv.ulift : ULift.{u} (ZMod ℓ) ≃+ ZMod ℓ).toAddMonoidHom),
      fun σ => LinearMap.ext fun x => (hfix σ _).symm⟩
  let ψ' : Rep.res P.subtype (rootsOfUnityModule K Ksep ℓ) ⟶
      Rep.trivial (ULift.{u} ℤ) P (ULift.{u} (ZMod ℓ)) :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
      ((AddEquiv.ulift : ULift.{u} (ZMod ℓ) ≃+ ZMod ℓ).symm.toAddMonoidHom.comp
        e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change ULift.up (e.symm ((Rep.res P.subtype (rootsOfUnityModule K Ksep ℓ)).ρ σ x)) =
          ULift.up (e.symm x)
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

/-- For `n` invertible in `K` and a smooth `n`-torsion module `M` of an open subgroup `U`,
`Hʳ(U, M) = 0` for `r ≥ 3`. -/
theorem subsingleton_cohomology_res_of_three_le {n : ℕ} (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K)))
    [IsSmoothRep M] (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) :
    Subsingleton (cohomology M r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have htors : IsAddTorsion M := fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn0, hM m⟩
  suffices h : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  refine eq_zero_of_primaryComponent_eq_bot n hn0 (fun ℓ hℓ hℓn => ?_) x
    (nsmul_cohomology_eq_zero M hM r x)
  have hℓK : (ℓ : K) ≠ 0 := fun h0 => hn (by
    obtain ⟨c, hc⟩ := hℓn
    rw [hc, Nat.cast_mul, h0, zero_mul])
  refine primaryComponent_cohomology_eq_bot_of_cd_lt (p := ℓ) M htors ?_
  calc cd ℓ (U : Subgroup Gal(Ksep/K)) ≤ cd ℓ Gal(Ksep/K) := cd_openSubgroup_le ℓ U
    _ ≤ 2 := cd_le_two K Ksep hℓ hℓK
    _ < r := by exact_mod_cast (show 2 < r by omega)

/-- For `n` invertible in `K` and a smooth `n`-torsion module `M` of `Gal(Ksep/K)`,
`Hʳ(Gal(Ksep/K), M) = 0` for `r ≥ 3`. -/
theorem subsingleton_cohomology_of_three_le {n : ℕ} (hn : (n : K) ≠ 0)
    (M : Rep.{u} IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] (hM : ∀ m : M, n • m = 0)
    {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) :=
  have := subsingleton_cohomology_res_of_three_le K Ksep hn ⊤
    (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hM hr
  (bijective_res_top M r).1.subsingleton

/-- For an open subgroup `U` and a finite smooth module `M` of `U` killed by `n` invertible in `K`,
every `Hʳ(U, M)` is finite. -/
theorem finite_cohomology_res {n : ℕ} (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) : Finite (cohomology M r) := by
  rcases le_or_gt r 2 with hr | hr
  · exact finite_cohomology_res_of_le_two K Ksep hn U M hM r hr
  · have := subsingleton_cohomology_res_of_three_le K Ksep hn U M hM (r := r) hr
    exact Finite.of_subsingleton

/-- **Finiteness**: for a finite smooth module `M` whose order is invertible in `K`, every
`Hʳ(Gal(Ksep/K), M)` is finite. -/
theorem finite_cohomology (M : Rep.{u} IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) (r : ℕ) : Finite (cohomology M r) := by
  have : Finite (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) :=
    inferInstanceAs (Finite M)
  have := finite_cohomology_res K Ksep hM ⊤
    (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M)
    (fun _ => card_nsmul_eq_zero') r
  exact Finite.of_injective _ (bijective_res_top M r).1

/-- The groups `Gal(Ksep/K)` and its open subgroups have finite cohomology (in the sense of the
abstract Euler characteristic) for the modules of order invertible in `K`. -/
theorem hasFiniteCohomology_res (U : OpenSubgroup Gal(Ksep/K)) :
    HasFiniteCohomology (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K)) (fun m => (m : K) ≠ 0) :=
  fun A _ _ hA => ⟨finite_cohomology_res K Ksep hA U A (fun _ => card_nsmul_eq_zero'),
    fun _ hq => subsingleton_cohomology_res_of_three_le K Ksep hA U A
      (fun _ => card_nsmul_eq_zero') hq⟩

theorem hasFiniteCohomology :
    HasFiniteCohomology (ULift.{u} ℤ) Gal(Ksep/K) (fun m => (m : K) ≠ 0) :=
  fun A _ _ hA => ⟨finite_cohomology K Ksep A hA,
    fun _ hq => subsingleton_cohomology_of_three_le K Ksep hA A (fun _ => card_nsmul_eq_zero') hq⟩

end Local

end Langlands.GaloisCohomology
