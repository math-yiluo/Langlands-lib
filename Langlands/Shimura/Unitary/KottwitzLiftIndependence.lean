import Langlands.Shimura.Unitary.KottwitzDualTorus
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Independence of Kottwitz's polynomial from the lift of an unramified character

Over an algebraically closed field, two points of the dual torus `T̂` with the same pairing
with the Frobenius-invariant cocharacters are twisted conjugate in `Ĝ`. Hence two lifts
`t̂` of the same unitarily normalized character give the same polynomial `P`.
See the paired Markdown.
-/

noncomputable section

open NumberField

namespace Langlands.Shimura.KottwitzDual

universe u v w uL uV uΩ

/-! ### Homomorphisms vanishing on fixed points are coboundaries -/

section Coboundary

/-- If `u : M → A` vanishes on the fixed points of `φ` and `A` is divisible, then
`u = y - y ∘ φ` for some `y : M → A`. -/
theorem exists_coboundary_of_map_fixed {M A : Type*} [AddCommGroup M] [AddCommGroup A]
    [DivisibleBy A ℤ] (φ : M →+ M) (u : M →+ A) (hu : ∀ x, φ x = x → u x = 0) :
    ∃ y : M →+ A, ∀ x, u x = y x - y (φ x) := by
  set ψ : M →+ M := AddMonoidHom.id M - φ with hψ
  have hψx : ∀ x, ψ x = x - φ x := fun x => rfl
  have hker : ψ.ker ≤ u.ker := fun x hx => by
    rw [AddMonoidHom.mem_ker, hψx, sub_eq_zero] at hx
    exact hu x hx.symm
  let g : ψ.range →+ A := (QuotientAddGroup.lift ψ.ker u hker).comp
    (QuotientAddGroup.quotientKerEquivRange ψ).symm.toAddMonoidHom
  obtain ⟨y, hy⟩ := (Module.Baer.of_divisible A).extension_property_addMonoidHom
    ψ.range.subtype Subtype.val_injective g
  refine ⟨y, fun x => ?_⟩
  have h1 := DFunLike.congr_fun hy ⟨ψ x, x, rfl⟩
  have h2 : (QuotientAddGroup.quotientKerEquivRange ψ).symm ⟨ψ x, x, rfl⟩ =
      (x : M ⧸ ψ.ker) := (AddEquiv.symm_apply_eq _).mpr rfl
  simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, g,
    AddEquiv.coe_toAddMonoidHom, h2, QuotientAddGroup.lift_mk] at h1
  rw [← map_sub, ← hψx, h1]

variable {Ω : Type uΩ} [Field Ω] [IsAlgClosed Ω]

theorem units_zpow_surjective {z : ℤ} (hz : z ≠ 0) :
    Function.Surjective fun a : Ωˣ => a ^ z := fun b => by
  have hm : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (b : Ω) hm
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact b.ne_zero (by rw [← hx, zero_pow hm.ne'])
  have hv : Units.mk0 x hx0 ^ z.natAbs = b := Units.ext (by simp [hx])
  rcases Int.natAbs_eq z with h | h
  · exact ⟨Units.mk0 x hx0, by simp only; rw [h, zpow_natCast, hv]⟩
  · exact ⟨(Units.mk0 x hx0)⁻¹, by simp only; rw [h, zpow_neg, zpow_natCast, inv_pow, inv_inv, hv]⟩

variable (Ω) in
/-- For `Ω` algebraically closed, `Ωˣ` is a divisible group. -/
@[instance_reducible]
def unitsDivisibleBy : DivisibleBy (Additive Ωˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Ωˣ) ℤ fun {z} hz b => by
    obtain ⟨v, hv⟩ := units_zpow_surjective (Ω := Ω) hz (Additive.toMul b)
    exact ⟨Additive.ofMul v, by simp only [← ofMul_zpow, hv, ofMul_toMul]⟩

end Coboundary

/-! ### Coordinates of characters of `X_*(T)` -/

section Coordinates

variable {S : Type u} [Fintype S] {n : ℕ} {L : Type v} [Field L]

theorem cocharPairing_inv (t : Lˣ × (S → Fin n → Lˣ)) (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing t⁻¹ a = (cocharPairing t a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← cocharPairing_mul, inv_mul_cancel, cocharPairing_one]

/-- The pairing with `t̂` as a homomorphism `X_*(T) → Lˣ`, written additively. -/
def cocharPairingHom (t : Lˣ × (S → Fin n → Lˣ)) : (ℤ × (S → Fin n → ℤ)) →+ Additive Lˣ where
  toFun a := Additive.ofMul (cocharPairing t a)
  map_zero' := by rw [cocharPairing_zero]; rfl
  map_add' a b := by rw [cocharPairing_add]; rfl

/-- The multiplier cocharacter `(1, 0)`. -/
def multCochar : ℤ × (S → Fin n → ℤ) := (1, 0)

theorem cocharPairing_multCochar (t : Lˣ × (S → Fin n → Lˣ)) :
    cocharPairing t multCochar = t.1 := by
  simp [cocharPairing, multCochar]

variable [DecidableEq S]

/-- The coordinate cocharacter at `(τ, k)`. -/
def posCochar (τ : S) (k : Fin n) : ℤ × (S → Fin n → ℤ) := (0, Pi.single τ (Pi.single k 1))

theorem cochar_decomp (a : ℤ × (S → Fin n → ℤ)) :
    a = a.1 • multCochar + ∑ τ, ∑ k, a.2 τ k • posCochar τ k := by
  refine Prod.ext ?_ (funext fun τ => funext fun k => ?_)
  · simp [multCochar, posCochar, Prod.fst_sum]
  · simp [multCochar, posCochar, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem cocharPairing_posCochar (t : Lˣ × (S → Fin n → Lˣ)) (τ : S) (k : Fin n) :
    cocharPairing t (posCochar τ k) = t.2 τ k := by
  simp only [cocharPairing, posCochar, zpow_zero, one_mul]
  rw [Finset.prod_eq_single τ (fun τ' _ h => by simp [h]) (by simp)]
  rw [Finset.prod_eq_single k (fun k' _ h => by simp [h]) (by simp)]
  simp

/-- A point of `T̂` is determined by its pairing with `X_*(T)`. -/
theorem cocharPairing_injective {t t' : Lˣ × (S → Fin n → Lˣ)}
    (h : ∀ a, cocharPairing t a = cocharPairing t' a) : t = t' := by
  refine Prod.ext ?_ (funext fun τ => funext fun k => ?_)
  · rw [← cocharPairing_multCochar t, ← cocharPairing_multCochar t', h]
  · rw [← cocharPairing_posCochar t, ← cocharPairing_posCochar t', h]

/-- The point of `T̂` with given pairing `y : X_*(T) → Lˣ`. -/
def coordsOfHom (y : (ℤ × (S → Fin n → ℤ)) →+ Additive Lˣ) : Lˣ × (S → Fin n → Lˣ) :=
  (Additive.toMul (y multCochar), fun τ k => Additive.toMul (y (posCochar τ k)))

theorem cocharPairing_coordsOfHom (y : (ℤ × (S → Fin n → ℤ)) →+ Additive Lˣ)
    (a : ℤ × (S → Fin n → ℤ)) :
    cocharPairing (coordsOfHom y) a = Additive.toMul (y a) := by
  conv_rhs => rw [cochar_decomp a]
  simp only [map_add, map_sum, map_zsmul, toMul_add, toMul_sum, toMul_zsmul, cocharPairing,
    coordsOfHom]

omit [Fintype S] [DecidableEq S] in
/-- `torusElement` as a homomorphism `T̂ → Ĝ`. -/
def torusElementHom : (Lˣ × (S → Fin n → Lˣ)) →* DualGroup S n L where
  toFun := torusElement
  map_one' := torusElement_one
  map_mul' := torusElement_mul

omit [Fintype S] [DecidableEq S] in
theorem torusElement_inv (t : Lˣ × (S → Fin n → Lˣ)) :
    torusElement t⁻¹ = (torusElement t)⁻¹ :=
  map_inv torusElementHom t

end Coordinates

/-! ### Twisted coboundaries on the dual torus -/

section TwistedConj

variable {S : Type u} [Fintype S] {n : ℕ} {Ω : Type uΩ} [Field Ω] [IsAlgClosed Ω]

/-- Over an algebraically closed field, a point `u` of `T̂` that pairs trivially with every
`G`-invariant cocharacter is a twisted coboundary `y σ(y)⁻¹`. -/
theorem exists_eq_twistedCoboundary (G : CMPerm S) (u : Ωˣ × (S → Fin n → Ωˣ))
    (hu : ∀ a, cocharPullback n G a = a → cocharPairing u a = 1) :
    ∃ y : Ωˣ × (S → Fin n → Ωˣ), u = y * (torusTwist G y)⁻¹ := by
  classical
  have := unitsDivisibleBy Ω
  obtain ⟨y, hy⟩ := exists_coboundary_of_map_fixed (cocharPullback n G) (cocharPairingHom u)
    (fun a ha => by
      change Additive.ofMul (cocharPairing u a) = 0
      rw [hu a ha]
      rfl)
  refine ⟨coordsOfHom y, cocharPairing_injective fun a => ?_⟩
  rw [cocharPairing_mul, cocharPairing_inv, cocharPairing_torusTwist, cocharPairing_coordsOfHom,
    cocharPairing_coordsOfHom]
  have h := congrArg Additive.toMul (hy a)
  rw [toMul_sub, div_eq_mul_inv] at h
  exact h

/-- Two points of `T̂` with the same pairing with the `G`-invariant cocharacters are
`σ`-twisted conjugate in `Ĝ`. -/
theorem exists_torusElement_eq_twistedConj (G : CMPerm S) (t t' : Ωˣ × (S → Fin n → Ωˣ))
    (h : ∀ a, cocharPullback n G a = a → cocharPairing t' a = cocharPairing t a) :
    ∃ y : DualGroup S n Ω,
      torusElement t' = y * torusElement t * ((dualAction S n Ω G) y)⁻¹ := by
  obtain ⟨y, hy⟩ := exists_eq_twistedCoboundary G (t' * t⁻¹) fun a ha => by
    rw [cocharPairing_mul, cocharPairing_inv, h a ha, mul_inv_cancel]
  refine ⟨torusElement y, ?_⟩
  have ht' : t' = y * t * (torusTwist G y)⁻¹ := by
    rw [mul_right_comm, ← hy, inv_mul_cancel_right]
  rw [dualAction_apply, dualEndo_torusElement, ht', torusElement_mul, torusElement_mul,
    torusElement_inv]

end TwistedConj

/-! ### Independence of the lift -/

section Lifts

open KottwitzUnramified Langlands.Global.AdelicFunctoriality

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [Algebra.IsQuadraticExtension E K]
  [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
  {σ : SecondKindInvolution E K A} {n : ℕ} {p : ℕ} [Fact p.Prime]

variable (E K n p) in
/-- Every cocharacter of `T` (in the embedding coordinates of `Φ`) that is invariant under
the Frobenius permutation attached to `θ` comes from a `ℚ_p`-rational cocharacter. -/
def FrobeniusInvariantsRational (θ : ℂ →+* PadicAlgCl p) {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (hΦ : IsCMSection E K Φ) : Prop :=
  ∀ a : ℤ × ((E →+* ℝ) → Fin n → ℤ), cocharPullback n (frobeniusCMPerm hΦ θ) a = a →
    ∃ m : localCocharacters E K (rationalPrimePlace p) n, embeddingCochar θ Φ m = a

variable {c : UnramifiedChart σ (rationalPrimePlace p) n} {θ : ℂ →+* PadicAlgCl p}
  {Φ : (E →+* ℝ) → (K →+* ℂ)} {hΦ : IsCMSection E K Φ}

/-- Over an algebraically closed field, two normalized lifts of the same character give the
same Kottwitz polynomial, provided the Frobenius-invariant cocharacters are rational. -/
theorem kottwitzPolynomialOf_eq_of_isNormalizedLift {Ω : Type uΩ} [Field Ω] [IsAlgClosed Ω]
    (hrat : FrobeniusInvariantsRational E K n p θ hΦ) (nfun : (K →+* ℂ) → ℕ)
    (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    {s : SqrtPrime (rationalPrimePlace p) Ω} {ξ : c.torus →* Ωˣ}
    {t t' : Ωˣ × ((E →+* ℝ) → Fin n → Ωˣ)}
    (ht : IsNormalizedLift c θ (Φ := Φ) s ξ t) (ht' : IsNormalizedLift c θ (Φ := Φ) s ξ t')
    (z : Ωˣ) :
    kottwitzPolynomialOf θ hΦ nfun hconj z t' = kottwitzPolynomialOf θ hΦ nfun hconj z t := by
  obtain ⟨y, hy⟩ := exists_torusElement_eq_twistedConj (frobeniusCMPerm hΦ θ) t t'
    fun a ha => by
      obtain ⟨m, rfl⟩ := hrat a ha
      rw [ht m, ht' m]
  rw [kottwitzPolynomialOf, kottwitzPolynomialOf, hy, kottwitzCharpoly_twistedConj]

theorem twoRhoPairing_add {S : Type*} [Fintype S] {n : ℕ} (a b : ℤ × (S → Fin n → ℤ)) :
    twoRhoPairing (a + b) = twoRhoPairing a + twoRhoPairing b := by
  simp only [twoRhoPairing, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

variable (θ Φ) in
/-- `embeddingCochar` as a homomorphism of lattices. -/
def embeddingCocharHom :
    localCocharacters E K (rationalPrimePlace p) n →+ ℤ × ((E →+* ℝ) → Fin n → ℤ) where
  toFun := embeddingCochar θ Φ
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Over an algebraically closed field, every unramified character has a normalized lift,
provided `embeddingCochar` is injective. -/
theorem exists_isNormalizedLift {Ω : Type uΩ} [Field Ω] [IsAlgClosed Ω]
    (hinj : Function.Injective (embeddingCochar (n := n) (p := p) (E := E) (K := K) θ Φ))
    (s : SqrtPrime (rationalPrimePlace p) Ω) (ξ : c.torus →* Ωˣ) :
    ∃ t, IsNormalizedLift c θ (Φ := Φ) s ξ t := by
  classical
  have := unitsDivisibleBy Ω
  let χ : localCocharacters E K (rationalPrimePlace p) n →+ Additive Ωˣ :=
    { toFun := fun m => Additive.ofMul (ξ (c.cocharHom (Multiplicative.ofAdd m)) *
        s.1 ^ twoRhoPairing (embeddingCochar θ Φ m))
      map_zero' := by
        simp only [ofAdd_zero, map_one, one_mul]
        rw [show embeddingCochar θ Φ (0 : localCocharacters E K (rationalPrimePlace p) n) = 0
          from rfl]
        simp [twoRhoPairing]
      map_add' := fun m m' => by
        have he : embeddingCochar θ Φ (m + m') =
            embeddingCochar θ Φ m + embeddingCochar θ Φ m' := rfl
        rw [← ofMul_mul, ofAdd_add, map_mul c.cocharHom, map_mul ξ, he, twoRhoPairing_add,
          zpow_add]
        congr 1
        ac_rfl }
  obtain ⟨y, hy⟩ := (Module.Baer.of_divisible (Additive Ωˣ)).extension_property_addMonoidHom
    (embeddingCocharHom θ Φ) hinj χ
  refine ⟨coordsOfHom y, fun m => ?_⟩
  rw [cocharPairing_coordsOfHom]
  exact congrArg Additive.toMul (DFunLike.congr_fun hy m)

variable [Module.Finite ℚ A] {L : Type uL} [Field L]

/-- Over an algebraically closed field, Kottwitz's polynomial of `π` is determined by the
parameter: `P` satisfies the relation exactly when, for some parameter `ξ` of `π`, `P` is
the polynomial of every normalized lift of `ξ`. -/
theorem isKottwitzPolynomialOver_iff_forall_lift {Ω : Type uΩ} [Field Ω] [IsAlgClosed Ω]
    [Algebra L Ω] (hrat : FrobeniusInvariantsRational E K n p θ hΦ)
    (hinj : Function.Injective (embeddingCochar (n := n) (p := p) (E := E) (K := K) θ Φ))
    (nfun : (K →+* ℂ) → ℕ) (hconj : ∀ i, nfun i + nfun (ComplexEmbedding.conjugate i) = n)
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ (rationalPrimePlace p)))
    (s : SqrtPrime (rationalPrimePlace p) Ω) (P : Polynomial Ω) :
    IsKottwitzPolynomialOver c θ hΦ nfun hconj π Ω s P ↔
      ∃ ξ : c.torus →* Ωˣ, c.HasPrincipalSeriesParameter π ξ ∧
        ∀ t, IsNormalizedLift c θ (Φ := Φ) s ξ t →
          P = kottwitzPolynomialOf θ hΦ nfun hconj s.1 t := by
  constructor
  · rintro ⟨ξ, t, hξ, ht, rfl⟩
    exact ⟨ξ, hξ, fun t' ht' =>
      kottwitzPolynomialOf_eq_of_isNormalizedLift hrat nfun hconj ht' ht s.1⟩
  · rintro ⟨ξ, hξ, hP⟩
    obtain ⟨t, ht⟩ := exists_isNormalizedLift hinj s ξ
    exact ⟨ξ, t, hξ, ht, hP t ht⟩

end Lifts

end Langlands.Shimura.KottwitzDual
