import Langlands.Shimura.Unitary.HarrisDividingLevelFree

/-!
# The points at two distinct primes

For distinct primes `ℓ` and `p`, the finite places of `ℚ` whose prime ideal contains `ℓ p` are the
place `v_ℓ` over `ℓ` and the place `v_p` over `p`. So the published points over
`∏_{v ∣ ℓ p} ℚ_v` are `σ(ℚ_ℓ) × σ(ℚ_p)` (`pairPointsEquiv`), with components the published local
maps `dividingLocalMap`. Through this identification, the subgroup `pairLevel K_ℓ C_p` of
`HarrisDividingLevelFree` is Harris's `K_ℓ × C_p` (1999, (4.5)) (`pairLevel_eq_comap`).
-/

noncomputable section

open Langlands.Global
open scoped NumberField

set_option autoImplicit false

universe v

namespace Langlands.Shimura.DefiniteForms

section Places

variable {ℓ p : ℕ}

/-- A finite place of `ℚ` contains `ℓ p` exactly when it contains `ℓ` or `p`. -/
theorem natCast_mul_mem_asIdeal_iff (w : FinitePlace ℚ) :
    ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal ↔ (ℓ : 𝓞 ℚ) ∈ w.asIdeal ∨ (p : 𝓞 ℚ) ∈ w.asIdeal := by
  rw [Nat.cast_mul]
  exact w.isPrime.mul_mem_iff_mem_or_mem

/-- No finite place of `ℚ` contains two distinct primes. -/
theorem not_natCast_mem_and_natCast_mem (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
    (w : FinitePlace ℚ) : ¬((ℓ : 𝓞 ℚ) ∈ w.asIdeal ∧ (p : 𝓞 ℚ) ∈ w.asIdeal) := by
  rintro ⟨h1, h2⟩
  have hcop : IsCoprime ((ℓ : ℤ) : 𝓞 ℚ) ((p : ℤ) : 𝓞 ℚ) :=
    (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hℓ hp).mpr hℓp)).map
      (Int.castRingHom (𝓞 ℚ))
  simp only [Int.cast_natCast] at hcop
  obtain ⟨a, b, hab⟩ := hcop
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ a h1) (Ideal.mul_mem_left _ b h2)

variable (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
  (vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal})
  (vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

variable (p) in
/-- The place over `ℓ`, as a place dividing `ℓ p`. -/
abbrev ellPlace : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} :=
  dividingPlaceOfDvd vℓ (dvd_mul_right ℓ p)

variable (ℓ) in
/-- The place over `p`, as a place dividing `ℓ p`. -/
abbrev primePlace : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} :=
  dividingPlaceOfDvd vp (dvd_mul_left p ℓ)

variable (p) in
/-- Among the places dividing `ℓ p`, the place over `ℓ` is the only one containing `ℓ`. -/
abbrev ellPlaceUnique :
    Unique {w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} //
      (ℓ : 𝓞 ℚ) ∈ w.1.asIdeal} where
  default := ⟨ellPlace p vℓ, vℓ.2⟩
  uniq w := Subtype.ext (Subtype.ext ((existsUnique_finitePlace_natCast_mem ℓ hℓ).unique w.2 vℓ.2))

/-- Among the places dividing `ℓ p`, the place over `p` is the only one not containing `ℓ`. -/
abbrev primePlaceUnique :
    Unique {w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} //
      ¬(ℓ : 𝓞 ℚ) ∈ w.1.asIdeal} where
  default := ⟨primePlace ℓ vp, fun h =>
    not_natCast_mem_and_natCast_mem hℓ hp hℓp vp.1 ⟨h, vp.2⟩⟩
  uniq w := Subtype.ext (Subtype.ext ((existsUnique_finitePlace_natCast_mem p hp).unique
    (((natCast_mul_mem_asIdeal_iff w.1.1).1 w.1.2).resolve_left w.2) vp.2))

open Classical in
/-- For distinct primes `ℓ` and `p`, the product of the completions of `ℚ` at the places dividing
`ℓ p` is `ℚ_ℓ × ℚ_p`, through evaluation at the two places. -/
def pairCompletionEquiv :
    (Π w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ w.1) ≃A[ℚ]
      FiniteCompletion ℚ vℓ.1 × FiniteCompletion ℚ vp.1 :=
  letI := ellPlaceUnique p hℓ vℓ
  letI := primePlaceUnique hℓ hp hℓp vp
  { ((RingEquiv.piEquivPiSubtypeProd
        (fun w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =>
          (ℓ : 𝓞 ℚ) ∈ w.1.asIdeal)
        (fun w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =>
          FiniteCompletion ℚ w.1)).trans
      ((RingEquiv.piUnique _).prodCongr (RingEquiv.piUnique _))).toRatAlgEquiv with
    continuous_toFun := (continuous_apply _).prodMk (continuous_apply _)
    continuous_invFun := by
      exact ((Homeomorph.piEquivPiSubtypeProd
        (fun w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =>
          (ℓ : 𝓞 ℚ) ∈ w.1.asIdeal)
        (fun w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =>
          FiniteCompletion ℚ w.1)).trans
        ((Homeomorph.piUnique _).prodCongr (Homeomorph.piUnique _))).symm.continuous }

@[simp]
theorem pairCompletionEquiv_apply
    (x : Π w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}, FiniteCompletion ℚ w.1) :
    pairCompletionEquiv hℓ hp hℓp vℓ vp x = (x (ellPlace p vℓ), x (primePlace ℓ vp)) :=
  rfl

end Places

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
  (vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal})
  (vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

/-- For distinct primes `ℓ` and `p`, `σ(∏_{v ∣ ℓ p} ℚ_v) ≃ₜ* σ(ℚ_ℓ) × σ(ℚ_p)`. -/
def pairPointsEquiv :
    σ.DividingPoints (ℓ * p) ≃ₜ*
      σ.Points (FiniteCompletion ℚ vℓ.1) × σ.Points (FiniteCompletion ℚ vp.1) :=
  (σ.pointsContinuousEquiv (pairCompletionEquiv hℓ hp hℓp vℓ vp)).trans
    (σ.prodPointsContinuousEquiv _ _)

/-- The components of `pairPointsEquiv` are the published local maps at the two places. -/
theorem pairPointsEquiv_apply (u : σ.DividingPoints (ℓ * p)) :
    pairPointsEquiv σ hℓ hp hℓp vℓ vp u =
      (σ.dividingLocalMap (ℓ * p) (ellPlace p vℓ) u,
        σ.dividingLocalMap (ℓ * p) (primePlace ℓ vp) u) := by
  have h1 : (AlgHom.fst ℚ (FiniteCompletion ℚ vℓ.1) (FiniteCompletion ℚ vp.1)).comp
      (pairCompletionEquiv hℓ hp hℓp vℓ vp).toAlgEquiv.toAlgHom =
        Pi.evalAlgHom ℚ (fun w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =>
          FiniteCompletion ℚ w.1) (ellPlace p vℓ) :=
    AlgHom.ext fun _ => rfl
  have h2 : (AlgHom.snd ℚ (FiniteCompletion ℚ vℓ.1) (FiniteCompletion ℚ vp.1)).comp
      (pairCompletionEquiv hℓ hp hℓp vℓ vp).toAlgEquiv.toAlgHom =
        Pi.evalAlgHom ℚ (fun w : {v : FinitePlace ℚ // ((ℓ * p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =>
          FiniteCompletion ℚ w.1) (primePlace ℓ vp) :=
    AlgHom.ext fun _ => rfl
  have e : pairPointsEquiv σ hℓ hp hℓp vℓ vp u =
      σ.prodPointsContinuousEquiv _ _
        (σ.pointsContinuousEquiv (pairCompletionEquiv hℓ hp hℓp vℓ vp) u) := rfl
  rw [e, AlgebraInvolution.prodPointsContinuousEquiv_apply,
    AlgebraInvolution.pointsContinuousEquiv_apply, σ.pointsMap_apply_apply,
    σ.pointsMap_apply_apply, h1, h2]
  rfl

/-- Through `pairPointsEquiv`, `pairLevel K_ℓ C_p` is `K_ℓ × C_p`. -/
theorem pairLevel_eq_comap (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))) :
    pairLevel σ (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp =
      (Kℓ.prod Cp).comap (pairPointsEquiv σ hℓ hp hℓp vℓ vp).toMonoidHom := by
  ext u
  change _ ↔ pairPointsEquiv σ hℓ hp hℓp vℓ vp u ∈ Kℓ.prod Cp
  rw [pairPointsEquiv_apply]
  exact Iff.rfl

/-- Harris's (4.5) for `K_ℓ × C_p`, read through `pairPointsEquiv`: the subgroup of
`σ(∏_{v ∣ ℓ p} ℚ_v)` corresponding to `K_ℓ × C_p` acts without fixed points on
`GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}`. -/
theorem harrisDividingLevelFree_iff (hn : ℓ * p ≠ 0)
    (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1)))
    (L : Subgroup (σ.PrimeToPoints (ℓ * p))) :
    HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L ↔
      DividingLevelFree σ (ℓ * p) hn
        ((Kℓ.prod Cp).comap (pairPointsEquiv σ hℓ hp hℓp vℓ vp).toMonoidHom) L := by
  rw [HarrisDividingLevelFree, pairLevel_eq_comap σ hℓ hp hℓp vℓ vp]

end Langlands.Shimura.DefiniteForms
