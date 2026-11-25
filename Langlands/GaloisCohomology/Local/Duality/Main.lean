import Langlands.GaloisCohomology.Local.Duality.Pairing
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Main

/-!
# Local Tate duality

The counting hypothesis `CardCohomologyOneLe` of `Pairing.lean`, `|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|`
for every open subgroup `U` of `Gal(Ksep/K)` and every `n` invertible in `K`, is proved from the
local Euler characteristic formula: by Shapiro's lemma the Euler characteristic of a finite module
of `U` depends only on its order, so `χ(U, μ_n) = χ(U, ℤ/n)`; with `|H²(U, μ_n)| = n = |H⁰(U, ℤ/n)|`
the inequality becomes `|H⁰(U, μ_n)| ≤ |H²(U, ℤ/n)|`. If `μ_n(E) = μ_m` (`E` the fixed field of
`U`), then `ℤ/m ≅ μ_m` as `U`-modules, so `|H²(U, ℤ/m)| = |H²(U, μ_m)| = m`, and
`H²(U, ℤ/n) → H²(U, ℤ/m)` is onto because `H³(U, ℤ/(n/m)) = 0`.

This gives local Tate duality unconditionally (`tatePairing_bijective`,
`tatePairing_flip_bijective`).
-/

noncomputable section

open CategoryTheory

universe u

namespace Langlands.GaloisCohomology.Local

open Langlands.ProfiniteCohomology ClassFieldTheory.Local ValuativeRel

section Counting

variable (K Ksep : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The Euler characteristic of a finite module of an open subgroup `U` of order invertible in
`K` depends only on its order (Shapiro's lemma and the Euler characteristic formula for
`Gal(Ksep/K)`). -/
theorem eulerCharacteristic_res_eq (U : OpenSubgroup Gal(Ksep/K))
    (B : Rep (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep B] [Finite B]
    (hB : (Nat.card B : K) ≠ 0) :
    eulerCharacteristic B = (Nat.card (𝒪[K] ⧸ Ideal.span
      {((Nat.card B ^ (U : Subgroup Gal(Ksep/K)).index : ℕ) : 𝒪[K])}) : ℚ)⁻¹ := by
  have hfin : Finite (Gal(Ksep/K) ⧸ (U : Subgroup Gal(Ksep/K))) :=
    Subgroup.finite_quotient_of_finiteIndex
  have hc := card_coind U B
  have hB' : (Nat.card (Rep.coind (U : Subgroup Gal(Ksep/K)).subtype B) : K) ≠ 0 := by
    rw [hc, Nat.cast_pow]
    exact pow_ne_zero _ hB
  rw [← eulerCharacteristic_coind U B, Local.eulerCharacteristic_eq K Ksep _ hB', hc]

variable {K Ksep}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem card_cohomology_zero_zmodRep (U : Subgroup Gal(Ksep/K)) (n : ℕ) [NeZero n] :
    Nat.card (cohomology (zmodRep.{u} U n) 0) = n := by
  rw [Nat.card_congr (zeroIso (zmodRep.{u} U n)).toLinearEquiv.toEquiv]
  have htop : (zmodRep.{u} U n).ρ.invariants = ⊤ := by
    ext x
    simp only [Submodule.mem_top, iff_true]
    exact fun g => rfl
  change Nat.card ((zmodRep.{u} U n).ρ.invariants) = n
  rw [htop, Nat.card_congr (Submodule.topEquiv).toEquiv, Nat.card_ulift, Nat.card_zmod]

/-- The subgroup of `Ksepˣ` of the `n`-th roots of unity fixed by `U`. -/
def fixedRootsOfUnity (n : ℕ) (U : Subgroup Gal(Ksep/K)) : Subgroup Ksepˣ where
  carrier := {u | u ∈ rootsOfUnity n Ksep ∧ ∀ σ ∈ U, σ (u : Ksep) = u}
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, fun σ hσ => by
    rw [Units.val_mul, map_mul, ha.2 σ hσ, hb.2 σ hσ]⟩
  one_mem' := ⟨one_mem _, fun σ _ => by rw [Units.val_one, map_one]⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, fun σ hσ => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha.2 σ hσ]⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- `H⁰(U, μ_n)` has as many elements as the group of `n`-th roots of unity fixed by `U`. -/
theorem card_cohomology_zero_rootsOfUnity (n : ℕ) (U : Subgroup Gal(Ksep/K)) :
    Nat.card (cohomology (Rep.res U.subtype (rootsOfUnityModule K Ksep n)) 0) =
      Nat.card (fixedRootsOfUnity (K := K) n U) := by
  rw [Nat.card_congr (zeroIso _).toLinearEquiv.toEquiv]
  change Nat.card ((Rep.res U.subtype (rootsOfUnityModule K Ksep n)).ρ.invariants) = _
  have hmem : ∀ a : Additive (rootsOfUnity n Ksep),
      a ∈ (Rep.res U.subtype (rootsOfUnityModule K Ksep n)).ρ.invariants ↔
        ((a.toMul : rootsOfUnity n Ksep) : Ksepˣ) ∈ fixedRootsOfUnity (K := K) n U := by
    intro a
    rw [Representation.mem_invariants]
    constructor
    · intro h
      refine ⟨(a.toMul).2, fun σ hσ => ?_⟩
      have h1 := congrArg (fun b : Additive (rootsOfUnity n Ksep) =>
        (((b.toMul : rootsOfUnity n Ksep) : Ksepˣ) : Ksep)) (h ⟨σ, hσ⟩)
      simpa [Rep.res, rootsOfUnityModule_ρ_apply, coe_galRootsOfUnityHom_apply] using h1
    · intro h g
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      change (((galRootsOfUnityHom K Ksep n (g : Gal(Ksep/K)) a.toMul : rootsOfUnity n Ksep) :
        Ksepˣ) : Ksep) = _
      rw [coe_galRootsOfUnityHom_apply]
      exact h.2 g g.2
  refine Nat.card_congr ⟨fun a => ⟨((Additive.toMul (a.1 : Additive (rootsOfUnity n Ksep)) :
      rootsOfUnity n Ksep) : Ksepˣ), (hmem a.1).1 a.2⟩,
    fun u => ⟨Additive.ofMul ⟨u.1, u.2.1⟩, (hmem _).2 u.2⟩, fun a => ?_, fun u => ?_⟩
  · rfl
  · rfl

end Counting

section ZModSequence

variable (G : Type u) [Group G] {m k n : ℕ} (h : m * k = n)

/-- Multiplication by `m`, `ℤ/k → ℤ/n` for `n = mk`. -/
def zmodMulHom : ZMod k →+ ZMod n :=
  ZMod.lift k ⟨zmultiplesHom (ZMod n) (m : ZMod n), by
    rw [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_comm, h,
      ZMod.natCast_self]⟩

/-- Multiplication by `m`, `ℤ/k → ℤ/n` for `n = mk`, on `ULift`. -/
def zmodMulAdd : ULift.{u} (ZMod k) →+ ULift.{u} (ZMod n) :=
  ((AddEquiv.ulift (α := ZMod n)).symm.toAddMonoidHom.comp (zmodMulHom h)).comp
    (AddEquiv.ulift (α := ZMod k)).toAddMonoidHom

/-- Reduction `ℤ/n → ℤ/m` for `n = mk`. -/
def zmodReduceAdd : ULift.{u} (ZMod n) →+ ULift.{u} (ZMod m) :=
  ((AddEquiv.ulift (α := ZMod m)).symm.toAddMonoidHom.comp
    (ZMod.castHom (h ▸ dvd_mul_right m k) (ZMod m)).toAddMonoidHom).comp
    (AddEquiv.ulift (α := ZMod n)).toAddMonoidHom

theorem zmodMulAdd_up_int (c : ℤ) :
    zmodMulAdd h (ULift.up (c : ZMod k)) = ULift.up (c • (m : ZMod n)) := by
  apply ULift.ext
  change zmodMulHom h (c : ZMod k) = _
  rw [zmodMulHom, ZMod.lift_coe, zmultiplesHom_apply]

theorem zmodMulAdd_up (a : ℕ) :
    zmodMulAdd h (ULift.up (a : ZMod k)) = ULift.up ((m * a : ℕ) : ZMod n) := by
  have := zmodMulAdd_up_int h (a : ℤ)
  rw [Int.cast_natCast, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_comm] at this
  exact this

theorem zmodReduceAdd_up (x : ZMod n) :
    zmodReduceAdd h (ULift.up x) = ULift.up (ZMod.castHom (h ▸ dvd_mul_right m k) (ZMod m) x) :=
  rfl

/-- The short exact sequence `0 → ℤ/k → ℤ/n → ℤ/m → 0` of trivial modules, `n = mk`. -/
abbrev zmodSequence : ShortComplex (Rep.{u} (ULift.{u} ℤ) G) where
  X₁ := zmodRep.{u} G k
  X₂ := zmodRep.{u} G n
  X₃ := zmodRep.{u} G m
  f := Rep.ofHom ⟨uliftIntLinearMap (zmodMulAdd h), fun _ => rfl⟩
  g := Rep.ofHom ⟨uliftIntLinearMap (zmodReduceAdd h), fun _ => rfl⟩
  zero := by
    ext ⟨a⟩
    change (zmodReduceAdd.{u} h (zmodMulAdd.{u} h (ULift.up a))).down = (0 : ZMod m)
    rw [← ZMod.intCast_zmod_cast a, zmodMulAdd_up_int, zmodReduceAdd_up]
    change ZMod.castHom (h ▸ dvd_mul_right m k) (ZMod m) (_ • (m : ZMod n)) = 0
    rw [map_zsmul, map_natCast, ZMod.natCast_self, smul_zero]

theorem zmodSequence_shortExact (hm : m ≠ 0) (hk : k ≠ 0) : (zmodSequence G h).ShortExact where
  exact := by
    refine shortComplex_exact_of_forall_exists _ fun x hx => ?_
    obtain ⟨x⟩ := x
    have : NeZero n := ⟨by rw [← h]; exact mul_ne_zero hm hk⟩
    have hx' : ((x.val : ℕ) : ZMod m) = 0 := by
      have h1 := congrArg ULift.down hx
      change ZMod.castHom (h ▸ dvd_mul_right m k) (ZMod m) x = 0 at h1
      rwa [← ZMod.natCast_zmod_val x, map_natCast] at h1
    obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).1 hx'
    refine ⟨(ULift.up (c : ZMod k) : zmodRep.{u} G k), ?_⟩
    change zmodMulAdd h (ULift.up (c : ZMod k)) = ULift.up x
    rw [zmodMulAdd_up, ← hc, ZMod.natCast_zmod_val]
  mono_f := by
    have : NeZero k := ⟨hk⟩
    refine (Rep.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    obtain ⟨a⟩ := x
    change zmodMulAdd h (ULift.up a) = 0 at hx
    rw [← ZMod.natCast_zmod_val a, zmodMulAdd_up] at hx
    have h1 : ((m * a.val : ℕ) : ZMod n) = 0 := congrArg ULift.down hx
    rw [ZMod.natCast_eq_zero_iff, ← h] at h1
    have h2 : k ∣ a.val := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm)).1 h1
    have h3 : a.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt a)
    apply ULift.ext
    change a = 0
    rwa [ZMod.val_eq_zero] at h3
  epi_g := by
    refine (Rep.epi_iff_surjective _).2 fun y => ?_
    obtain ⟨z⟩ := y
    obtain ⟨x, hx⟩ := ZMod.ringHom_surjective (ZMod.castHom (h ▸ dvd_mul_right m k) (ZMod m)) z
    exact ⟨(ULift.up x : zmodRep.{u} G n), congrArg ULift.up hx⟩

end ZModSequence

section Counting'

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem finite_fixedRootsOfUnity (n : ℕ) [NeZero n] (U : Subgroup Gal(Ksep/K)) :
    Finite (fixedRootsOfUnity (K := K) n U) :=
  Finite.of_injective (fun s : fixedRootsOfUnity (K := K) n U =>
    (⟨s.1, s.2.1⟩ : rootsOfUnity n Ksep)) fun a b hab => Subtype.ext
      (show (a : Ksepˣ) = b from congrArg (fun x : rootsOfUnity n Ksep => (x : Ksepˣ)) hab)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
/-- The `n`-th roots of unity fixed by `U` are the `m`-th roots of unity, `m` their number. -/
theorem fixedRootsOfUnity_eq (n : ℕ) [NeZero n] (U : Subgroup Gal(Ksep/K)) :
    fixedRootsOfUnity (K := K) n U =
      rootsOfUnity (Nat.card (fixedRootsOfUnity (K := K) n U)) Ksep := by
  have := finite_fixedRootsOfUnity (K := K) n U
  have hle : fixedRootsOfUnity (K := K) n U ≤
      rootsOfUnity (Nat.card (fixedRootsOfUnity (K := K) n U)) Ksep := fun u hu => by
    rw [mem_rootsOfUnity]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨u, hu⟩ : fixedRootsOfUnity (K := K) n U)))
  exact Subgroup.eq_of_le_of_card_ge hle (card_rootsOfUnity _ _)

/-- `|H⁰(U, μ_n)| ≤ |H²(U, ℤ/n)|`. -/
theorem card_cohomology_zero_le_card_cohomology_two {n : ℕ} (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) :
    Nat.card (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) 0) ≤
      Nat.card (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 2) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have : NeZero n := ⟨hn0⟩
  rw [card_cohomology_zero_rootsOfUnity]
  set S := fixedRootsOfUnity (K := K) n (U : Subgroup Gal(Ksep/K)) with hSdef
  set m := Nat.card S with hmdef
  have hfinS := finite_fixedRootsOfUnity (K := K) n (U : Subgroup Gal(Ksep/K))
  have hS : S = rootsOfUnity m Ksep := fixedRootsOfUnity_eq n _
  have hmn : m ∣ n := by
    have hle : S ≤ rootsOfUnity n Ksep := fun u hu => hu.1
    have h1 := Subgroup.card_dvd_of_le hle
    have : IsSepClosed Ksep := IsSepClosure.sep_closed K
    have : NeZero (n : Ksep) := ⟨by
      rw [← map_natCast (algebraMap K Ksep)]
      exact (map_ne_zero _).mpr hn⟩
    rwa [HasEnoughRootsOfUnity.natCard_rootsOfUnity Ksep n] at h1
  obtain ⟨k, hk⟩ := hmn
  have hm0 : m ≠ 0 := Nat.card_pos.ne'
  have hk0 : k ≠ 0 := by rintro rfl; exact hn0 (by rw [hk, mul_zero])
  have hm : (m : K) ≠ 0 := fun h0 => hn (by rw [hk, Nat.cast_mul, h0, zero_mul])
  have hkK : (k : K) ≠ 0 := fun h0 => hn (by rw [hk, Nat.cast_mul, h0, mul_zero])
  have : NeZero m := ⟨hm0⟩
  -- `H²(U, ℤ/m) ≅ H²(U, μ_m) ≅ ℤ/m`
  have h2m : Nat.card (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) m) 2) = m := by
    obtain ⟨e⟩ := nonempty_addEquiv_rootsOfUnityModule (K := K) (Ksep := Ksep) hm
    have htriv : ∀ (g : (U : Subgroup Gal(Ksep/K))) (a : Additive (rootsOfUnity m Ksep)),
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep m)).ρ g a = a := by
      intro g a
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      change (((galRootsOfUnityHom K Ksep m (g : Gal(Ksep/K)) a.toMul : rootsOfUnity m Ksep) :
        Ksepˣ) : Ksep) = _
      rw [coe_galRootsOfUnityHom_apply]
      have ha : ((a.toMul : rootsOfUnity m Ksep) : Ksepˣ) ∈ S := by
        rw [hS]
        exact (a.toMul).2
      exact ha.2 g g.2
    let e2 := cohomologyAddEquivOfEquiv
      (A := Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep m))
      (A' := zmodRep.{u} (U : Subgroup Gal(Ksep/K)) m) (e.trans AddEquiv.ulift.symm)
      (fun g a => by rw [htriv g a]; rfl) 2
    rw [← Nat.card_congr e2.toEquiv, Nat.card_congr (rootsOfUnityInvariant hm U).toEquiv,
      Nat.card_zmod]
  -- `H²(U, ℤ/n) → H²(U, ℤ/m)` is onto since `H³(U, ℤ/k) = 0`
  have hSES := zmodSequence_shortExact (U : Subgroup Gal(Ksep/K)) hk.symm hm0 hk0
  have hsurj : Function.Surjective (coeffMap (zmodSequence (U : Subgroup Gal(Ksep/K))
      hk.symm).g 2).hom := by
    intro y
    have : Subsingleton (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) k) 3) :=
      subsingleton_cohomology_res_of_three_le K Ksep hkK U _
        (fun a => by
          obtain ⟨a⟩ := a
          apply ULift.ext
          change k • a = 0
          rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]) le_rfl
    exact (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₃ hSES 2 3 rfl) y
      (Subsingleton.elim _ _)
  have hfin : Finite (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 2) :=
    finite_cohomology_res K Ksep hn U _ (fun a => by
      obtain ⟨a⟩ := a
      apply ULift.ext
      change n • a = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]) 2
  calc m = Nat.card (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) m) 2) := h2m.symm
    _ ≤ Nat.card (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 2) :=
      Nat.card_le_card_of_surjective _ hsurj

end Counting'

section Duality

variable (K Ksep : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- The counting hypothesis of `Pairing.lean` holds: `|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|`. -/
theorem cardCohomologyOneLe : CardCohomologyOneLe K Ksep := by
  intro n hn U
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have : NeZero n := ⟨hn0⟩
  set A := Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)
  set Z := zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n
  obtain ⟨e⟩ := nonempty_addEquiv_rootsOfUnityModule (K := K) (Ksep := Ksep) hn
  have : Finite A := Finite.of_equiv _ e.toEquiv.symm
  have hcardA : Nat.card A = n := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  have hcardZ : Nat.card Z = n := by
    change Nat.card (ULift (ZMod n)) = n
    rw [Nat.card_ulift, Nat.card_zmod]
  have hnA : ∀ a : A, n • a = 0 :=
    nsmul_res_rootsOfUnityModule_eq_zero hn (U : Subgroup Gal(Ksep/K))
  have hnZ : ∀ a : Z, n • a = 0 := fun a => by
    obtain ⟨a⟩ := a
    apply ULift.ext
    change n • a = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hχ : eulerCharacteristic A = eulerCharacteristic Z := by
    rw [eulerCharacteristic_res_eq K Ksep U A (by rw [hcardA]; exact hn),
      eulerCharacteristic_res_eq K Ksep U Z (by rw [hcardZ]; exact hn), hcardA, hcardZ]
  rw [ProfiniteCohomology.eulerCharacteristic_eq, ProfiniteCohomology.eulerCharacteristic_eq] at hχ
  have hfA : ∀ r, Finite (cohomology A r) := finite_cohomology_res K Ksep hn U A hnA
  have hfZ : ∀ r, Finite (cohomology Z r) := finite_cohomology_res K Ksep hn U Z hnZ
  have hpA : ∀ r, 0 < Nat.card (cohomology A r) := fun r => by
    have := hfA r
    exact Nat.card_pos
  have hpZ : ∀ r, 0 < Nat.card (cohomology Z r) := fun r => by
    have := hfZ r
    exact Nat.card_pos
  have hA2 : Nat.card (cohomology A 2) = n := by
    rw [Nat.card_congr (rootsOfUnityInvariant hn U).toEquiv, Nat.card_zmod]
  have hZ0 : Nat.card (cohomology Z 0) = n := card_cohomology_zero_zmodRep _ n
  have hle := card_cohomology_zero_le_card_cohomology_two hn U
  rw [hA2, hZ0] at hχ
  -- `|H⁰(A)| · |H¹(Z)| = |H²(Z)| · |H¹(A)|`
  have key : Nat.card (cohomology A 0) * Nat.card (cohomology Z 1) =
      Nat.card (cohomology Z 2) * Nat.card (cohomology A 1) := by
    have h1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := by exact_mod_cast (hpA 1).ne'
    have h2 : (Nat.card (cohomology Z 1) : ℚ) ≠ 0 := by exact_mod_cast (hpZ 1).ne'
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    rw [div_eq_div_iff h1 h2] at hχ
    have : (n : ℚ) * (Nat.card (cohomology A 0) * Nat.card (cohomology Z 1)) =
        n * (Nat.card (cohomology Z 2) * Nat.card (cohomology A 1)) := by
      linear_combination hχ
    exact_mod_cast mul_left_cancel₀ hn' this
  have h3 : Nat.card (cohomology Z 2) * Nat.card (cohomology A 1) ≤
      Nat.card (cohomology Z 2) * Nat.card (cohomology Z 1) := by
    rw [← key]
    exact Nat.mul_le_mul_right _ hle
  exact Nat.le_of_mul_le_mul_left h3 (hpZ 2)

/-- **Local Tate duality** (Tate, Poitou). For a finite smooth module `M` of order invertible in
`K`, the Tate pairing `Hʳ(M) × Hˢ(M') → ℚ/ℤ`, `r + s = 2`, `M'` the Cartier dual, is perfect: it
identifies `Hʳ(M)` with the dual of `Hˢ(M')`. -/
theorem tatePairing_bijective (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (tatePairing K Ksep M h) :=
  tatePairing_bijective_of_card (cardCohomologyOneLe K Ksep) M hM h

/-- **Local Tate duality**, the other side: the Tate pairing identifies `Hˢ(M')` with the dual of
`Hʳ(M)`. -/
theorem tatePairing_flip_bijective (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M]
    [Finite M] (hM : (Nat.card M : K) ≠ 0) {r s : ℕ} (h : r + s = 2) :
    Function.Bijective (tatePairing K Ksep M h).flip :=
  tatePairing_flip_bijective_of_card (cardCohomologyOneLe K Ksep) M hM h

end Duality

end Langlands.GaloisCohomology.Local
