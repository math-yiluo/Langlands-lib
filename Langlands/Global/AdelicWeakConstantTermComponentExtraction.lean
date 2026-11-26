import Langlands.Global.AdelicLeadingCuspidalPairing
import Langlands.Global.AdelicWeakConstantTermPairingPolynomials
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicEisensteinPositiveParametersProof
import Mathlib.GroupTheory.CosetCover
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Levi pairings with the components of a weak constant term

Delorme 2023, §3.4: the pairing (3.7) of a square-integrable inducing form `φ ∈ A^2_P` with a
unitary component `c λ` of a constant-term decomposition (3.2) is a finite linear combination of
pairings of `φ` with the whole weak constant term at translated points of the positive split
component.

* `StandardParabolicFamily.exists_positiveSplitComponent_parameterPower_ne`: one point of the
  positive split component separates finitely many complex parameters.
* `StandardParabolicFamily.positivePairingIntegrable`: the second entries whose pairing with `φ`
  is integrable at every positive split-component point; it is stable under the translations of
  the positive split component and hence under polynomials in one of them.
* `StandardParabolicFamily.pairingIntegrable_component_of_sum`: integrability for a finite sum of
  functions with distinct normalized exponents gives integrability for each summand.
* `WeakConstantTermPairingIntegrableStatement`: absolute convergence of (3.7) for the whole weak
  constant term of a log-square-integrable automorphic form (stated, not proved here).
* `weakConstantTermComponentPairingIntegrable_of_weakConstantTerm`: that statement implies
  `WeakConstantTermComponentPairingIntegrableStatement`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory TensorProduct Polynomial
open scoped CategoryTheory.MonObj TensorProduct Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarishChandraSchwartz

namespace AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F]

/-- The character logarithm of a power: `H(x^k) = k H(x)`. -/
theorem characterLog_pow {H : GroupScheme (Spec (CommRingCat.of F))}
    (x : AdelicGroupPoints F H) (k : ℕ) :
    characterLog F H (x ^ k) = k • characterLog F H x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, characterLog_mul, ih, succ_nsmul]

/-- `(x^k)^λ = (x^λ)^k`. -/
theorem parameterPower_pow {H : GroupScheme (Spec (CommRingCat.of F))}
    (lam : ComplexCharacterParameter F H) (x : AdelicGroupPoints F H) (k : ℕ) :
    parameterPower F H lam (x ^ k) = parameterPower F H lam x ^ k := by
  rw [parameterPower, parameterPower, characterLog_pow, map_nsmul, nsmul_eq_mul,
    Complex.exp_nat_mul]

end AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (J : StandardIndex F G 𝓕.i 𝓕.ν)

attribute [local instance] positiveSplitComponentCommGroup

/-- A split-component equivariant function transforms by `δ_P^{1/2}` under the positive split
component of `P`. -/
theorem splitComponentEquivariant_apply {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ)
    {x : AdelicGroupPoints F (𝓕.P J)} (hx : x ∈ 𝓕.positiveSplitComponent J)
    (g : AdelicGroupPoints F G) :
    φ (map F (𝓕.P J) G (𝓕.p J) x * g) = 𝓕.halfModulus J x * φ g := by
  obtain ⟨t, ht, rfl⟩ := hx
  have ha : map F (𝓕.A J).toGrp (𝓕.M J) (𝓕.a J) t ∈
      RestrictionSplitCentre.canonicalSubgroup F (𝓕.M J) := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup
      (𝓕.isCompatible J).splitComponent]
    exact ⟨t, ht, rfl⟩
  let x := map F (𝓕.A J).toGrp (𝓕.P J) (𝓕.a J ≫ 𝓕.l J) t
  change φ (map F (𝓕.P J) G (𝓕.p J) x * g) = 𝓕.halfModulus J x * φ g
  simpa only [x, halfModulus, map_comp_apply_of_hom] using hφ _ ha g

/-! ### A point of the positive split component separating finitely many exponents -/

/-- For a parameter `λ` and finitely many parameters different from `λ`, some point `a` of the
positive split component has `a^μ ≠ a^λ` for all of them. -/
theorem exists_positiveSplitComponent_parameterPower_ne
    (lam : ComplexCharacterParameter F (𝓕.P J))
    (s : Finset (ComplexCharacterParameter F (𝓕.P J))) (hs : lam ∉ s) :
    ∃ a : 𝓕.positiveSplitComponent J, ∀ mu ∈ s,
      parameterPower F (𝓕.P J) mu a.val ≠ parameterPower F (𝓕.P J) lam a.val := by
  classical
  let r : ParabolicRootPresentation (𝓕.p J) (𝓕.l J) (𝓕.a J) :=
    ⟨⟨𝓕.T, 𝓕.i, 𝓕.ν, J.val, 𝓕.f J⟩, 𝓕.isCompatible J⟩
  obtain ⟨hlog, hinj⟩ := eisensteinPositiveParameters F G (𝓕.P J) (𝓕.M J) (𝓕.A J)
    (𝓕.p J) (𝓕.l J) (𝓕.a J) r
  let S := 𝓕.positiveSplitComponent J
  let χ (mu : ComplexCharacterParameter F (𝓕.P J)) : S →* ℂˣ :=
    (parameterCharacter F (𝓕.P J) (mu - lam)).comp S.subtype
  by_contra hcon
  push Not at hcon
  have hcover : ⋃ mu ∈ s, (1 : S) • ((χ mu).ker : Set S) = Set.univ := by
    refine Set.eq_univ_of_forall fun a => ?_
    obtain ⟨mu, hmu, heq⟩ := hcon a
    refine Set.mem_iUnion₂.mpr ⟨mu, hmu, ?_⟩
    rw [one_smul]
    change χ mu a = 1
    apply Units.ext
    change parameterPower F (𝓕.P J) (mu - lam) a.val = 1
    have hsplit : parameterPower F (𝓕.P J) mu a.val =
        parameterPower F (𝓕.P J) (mu - lam) a.val * parameterPower F (𝓕.P J) lam a.val := by
      rw [← parameterPower_add, sub_add_cancel]
    rw [heq] at hsplit
    have hne : parameterPower F (𝓕.P J) lam a.val ≠ 0 := Complex.exp_ne_zero _
    have := mul_right_cancel₀ hne (hsplit.symm.trans (one_mul _).symm)
    exact this
  obtain ⟨mu, hmu, hfin⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcover
  have hn : (χ mu).ker.index ≠ 0 := hfin.index_ne_zero
  set n := (χ mu).ker.index with hndef
  -- every `n`-th power lies in the kernel
  have hpow (a : S) : parameterPower F (𝓕.P J) (mu - lam) (a.val ^ n) = 1 := by
    have h := (χ mu).ker.pow_index_mem a
    rw [MonoidHom.mem_ker] at h
    have h' := congrArg Units.val h
    rw [parameterPower_pow]
    simpa [χ] using h'
  -- hence the character is trivial on the positive split component
  have htriv (a : S) : parameterPower F (𝓕.P J) (mu - lam) a.val =
      parameterPower F (𝓕.P J) 0 a.val := by
    obtain ⟨b, hb⟩ := hlog (((n : ℝ)⁻¹) • characterLog F (𝓕.P J) a.val)
    change characterLog F (𝓕.P J) b.val = _ at hb
    have hlogpow : characterLog F (𝓕.P J) (b.val ^ n) = characterLog F (𝓕.P J) a.val := by
      rw [characterLog_pow, hb, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]
    have h1 := hpow b
    simp only [parameterPower] at h1 ⊢
    rw [hlogpow] at h1
    rw [h1, map_zero, LinearMap.zero_apply, Complex.exp_zero]
  have heq : mu - lam = 0 := hinj (funext htriv)
  exact hs (sub_eq_zero.mp heq ▸ hmu)

/-! ### Integrability of the pairing at every positive point -/

section Pairing

variable (K : Subgroup (AdelicGroupPoints F G))
  (meas : Measure (K × NormOneRationalQuotient F (𝓕.M J)))
  (φ : AdelicGroupPoints F G → ℂ)

/-- The second entries `ψ` for which the Levi pairing integrand
`(k, m) ↦ φ(x m k) conj ψ(x m k)` with the first entry `φ` is integrable for `meas` at every point
`x` of the positive split component. The integrand is conjugate-linear in `ψ`, so these entries
form a complex subspace. -/
def positivePairingIntegrable : Submodule ℂ (AdelicGroupPoints F G → ℂ) where
  carrier := {ψ | ∀ x ∈ 𝓕.positiveSplitComponent J,
    Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ ψ) meas}
  zero_mem' := by
    intro x _
    have h0 : 𝓕.squareIntegrablePairingIntegrand K J x φ 0 = 0 := by
      funext z
      simp [squareIntegrablePairingIntegrand]
    rw [h0]
    exact integrable_zero _ _ _
  add_mem' := by
    intro ψ ψ' hψ hψ' x hx
    have hadd : 𝓕.squareIntegrablePairingIntegrand K J x φ (ψ + ψ') =
        𝓕.squareIntegrablePairingIntegrand K J x φ ψ +
          𝓕.squareIntegrablePairingIntegrand K J x φ ψ' := by
      funext z
      simp only [squareIntegrablePairingIntegrand, Pi.add_apply, map_add, mul_add]
    rw [hadd]
    exact (hψ x hx).add (hψ' x hx)
  smul_mem' := by
    intro c ψ hψ x hx
    have hsmul : 𝓕.squareIntegrablePairingIntegrand K J x φ (c • ψ) =
        fun z => (starRingEnd ℂ) c * 𝓕.squareIntegrablePairingIntegrand K J x φ ψ z := by
      funext z
      simp only [squareIntegrablePairingIntegrand, Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    rw [hsmul]
    exact (hψ x hx).const_mul _

variable {𝓕 J K meas φ}

/-- Translation by a point of the positive split component preserves integrability of the
pairing at every positive point: the translated pairing at `x` is a multiple of the pairing
at `a x`. -/
theorem positivePairingIntegrable_translate
    (hφ : IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ) (a : 𝓕.positiveSplitComponent J)
    {ψ : AdelicGroupPoints F G → ℂ} (hψ : ψ ∈ 𝓕.positivePairingIntegrable J K meas φ) :
    𝓕.splitComponentRepresentation J a ψ ∈ 𝓕.positivePairingIntegrable J K meas φ := by
  intro x hx
  have hax : a.val * x ∈ 𝓕.positiveSplitComponent J := mul_mem a.property hx
  have hne : 𝓕.halfModulus J a.val ≠ 0 := Complex.exp_ne_zero _
  have heq : 𝓕.squareIntegrablePairingIntegrand K J x φ (𝓕.splitComponentRepresentation J a ψ) =
      fun z => (𝓕.halfModulus J a.val)⁻¹ *
        𝓕.squareIntegrablePairingIntegrand K J (a.val * x) φ ψ z := by
    funext z
    set y := map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
      (z.1 : AdelicGroupPoints F G) with hy
    have hpt : map F (𝓕.P J) G (𝓕.p J) (a.val * x) * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (z.1 : AdelicGroupPoints F G) =
        map F (𝓕.P J) G (𝓕.p J) a.val * (map F (𝓕.P J) G (𝓕.p J) x * y) := by
      rw [map_mul, hy]
      simp only [mul_assoc]
    have hpt' : map F (𝓕.P J) G (𝓕.p J) x * map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
        ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (z.1 : AdelicGroupPoints F G) = map F (𝓕.P J) G (𝓕.p J) x * y := by
      rw [hy, mul_assoc]
    simp only [squareIntegrablePairingIntegrand]
    rw [hpt, hpt', 𝓕.splitComponentEquivariant_apply J hφ a.property]
    rw [mul_assoc (𝓕.halfModulus J a.val), inv_mul_cancel_left₀ hne]
    rfl
  rw [heq]
  exact (hψ _ hax).const_mul _

/-- A polynomial in a translation by a point of the positive split component preserves
integrability of the pairing at every positive point. -/
theorem positivePairingIntegrable_aeval
    (hφ : IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ) (a : 𝓕.positiveSplitComponent J)
    (q : ℂ[X]) {ψ : AdelicGroupPoints F G → ℂ}
    (hψ : ψ ∈ 𝓕.positivePairingIntegrable J K meas φ) :
    aeval (𝓕.splitComponentRepresentation J a) q ψ ∈ 𝓕.positivePairingIntegrable J K meas φ := by
  have hpow (i : ℕ) : ((𝓕.splitComponentRepresentation J a) ^ i) ψ ∈
      𝓕.positivePairingIntegrable J K meas φ := by
    induction i with
    | zero => simpa using hψ
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact positivePairingIntegrable_translate hφ a ih
  rw [aeval_eq_sum_range, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)

end Pairing

/-! ### Extraction of a component -/

/-- **Extraction of a component.** Let `φ` transform by `δ_P^{1/2}` under the split component,
and let `ψ = ∑_{μ ∈ s} c μ` with each `c μ` of normalized exponent `μ`. If the Levi pairing of
`φ` with `ψ` is integrable at every point of the positive split component, then so is the
pairing of `φ` with each `c λ`, `λ ∈ s`. -/
theorem pairingIntegrable_component_of_sum
    (K : Subgroup (AdelicGroupPoints F G))
    (meas : Measure (K × NormOneRationalQuotient F (𝓕.M J)))
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant (𝓕.p J) (𝓕.l J) φ)
    (s : Finset (ComplexCharacterParameter F (𝓕.P J)))
    (c : ComplexCharacterParameter F (𝓕.P J) → AdelicGroupPoints F G → ℂ)
    (hc : ∀ mu ∈ s, 𝓕.HasExponent J mu (c mu))
    (hint : ∀ x ∈ 𝓕.positiveSplitComponent J,
      Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ (∑ mu ∈ s, c mu)) meas)
    {lam : ComplexCharacterParameter F (𝓕.P J)} (hlam : lam ∈ s) :
    ∀ x ∈ 𝓕.positiveSplitComponent J,
      Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ (c lam)) meas := by
  classical
  let ρ := halfModulusParameter F (𝓕.P J)
  -- a point separating the exponents
  obtain ⟨a, ha⟩ := 𝓕.exists_positiveSplitComponent_parameterPower_ne J (lam + ρ)
    ((s.erase lam).image (· + ρ)) (by
      intro h
      obtain ⟨mu, hmu, he⟩ := Finset.mem_image.mp h
      exact (Finset.ne_of_mem_erase hmu) (add_right_cancel he))
  let T := 𝓕.splitComponentRepresentation J a
  let α (mu : ComplexCharacterParameter F (𝓕.P J)) : ℂ := parameterPower F (𝓕.P J) (mu + ρ) a.val
  have hα (mu) (hmu : mu ∈ s.erase lam) : α mu ≠ α lam :=
    ha (mu + ρ) (Finset.mem_image.mpr ⟨mu, hmu, rfl⟩)
  -- each component is killed by a power of `T - α μ`
  have hkill (mu) (hmu : mu ∈ s) : ∃ k : ℕ, aeval T ((X - C (α mu)) ^ k) (c mu) = 0 := by
    have hgen := 𝓕.mem_jointGenEigenspace_of_hasUnnormalizedExponent J
      ((𝓕.hasExponent_iff J mu (c mu)).mp (hc mu hmu))
    obtain ⟨k, hk⟩ := (mem_jointGenEigenspace.mp hgen) a
    refine ⟨k, ?_⟩
    rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
    exact hk
  choose! k hk using hkill
  let L : ℂ[X] := (X - C (α lam)) ^ k lam
  let R : ℂ[X] := ∏ mu ∈ s.erase lam, (X - C (α mu)) ^ k mu
  have hcop : IsCoprime L R := by
    refine IsCoprime.prod_right fun mu hmu => ?_
    exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hα mu hmu).symm).isUnit).pow
  obtain ⟨u, v, huv⟩ := hcop
  -- the component is `v(T) R(T)` applied to the sum
  have hR (mu) (hmu : mu ∈ s.erase lam) : aeval T R (c mu) = 0 := by
    change aeval T (∏ mu ∈ s.erase lam, (X - C (α mu)) ^ k mu) (c mu) = 0
    rw [← Finset.prod_erase_mul _ _ hmu, map_mul, Module.End.mul_apply,
      hk mu (Finset.mem_of_mem_erase hmu), map_zero]
  have hcomp : aeval T (v * R) (∑ mu ∈ s, c mu) = c lam := by
    rw [map_sum, ← Finset.add_sum_erase _ _ hlam]
    have hrest : ∑ mu ∈ s.erase lam, aeval T (v * R) (c mu) = 0 := by
      refine Finset.sum_eq_zero fun mu hmu => ?_
      rw [map_mul, Module.End.mul_apply, hR mu hmu, map_zero]
    rw [hrest, add_zero]
    have hvR : v * R = 1 - u * L := by rw [← huv]; ring
    rw [hvR, map_sub, map_one, map_mul, LinearMap.sub_apply, Module.End.one_apply,
      Module.End.mul_apply, hk lam hlam, map_zero, sub_zero]
  have hmem : (∑ mu ∈ s, c mu) ∈ 𝓕.positivePairingIntegrable J K meas φ := hint
  have := positivePairingIntegrable_aeval hφ a (v * R) hmem
  rw [hcomp] at this
  exact this

end StandardParabolicFamily

/-- **Absolute convergence of the Levi pairing with the weak constant term** (Delorme 2023,
§3.4, (3.7)). For a log-square-integrable automorphic form `Φ` and a compatible family of
standard parabolics whose minimal member satisfies `P_∅(𝔸) K = G(𝔸)`, let `ψ = Φ_P^w` be a
weak constant term of `Φ` along `P = P_J` and `φ ∈ A^2_P`. Then the Levi pairing integrand
`(k, m) ↦ φ(x m k) conj ψ(x m k)` is integrable on `K × M(F) \ M(𝔸)^1` for the product of the
Haar probability of `K` and the norm-one quotient measure, at every point `x` of the positive
split component. -/
def WeakConstantTermPairingIntegrableStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
      (Φ : AdelicGroupPoints F G → ℂ),
    IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (J : StandardIndex F G 𝓕.i 𝓕.ν) (ψ : AdelicGroupPoints F G → ℂ),
    𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ ψ →
    ∀ (φ : AdelicGroupPoints F G → ℂ),
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ →
    ∀ x ∈ 𝓕.positiveSplitComponent J,
      Integrable (𝓕.squareIntegrablePairingIntegrand K J x φ ψ)
        (𝓕.squareIntegrablePairingMeasure K hK.isCompact J)

/-- Integrability of the pairings with the whole weak constant term gives the integrability of
the pairings with each of its unitary components. -/
theorem weakConstantTermComponentPairingIntegrable_of_weakConstantTerm
    (h : WeakConstantTermPairingIntegrableStatement) :
    WeakConstantTermComponentPairingIntegrableStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J s c hdec lam hlam hre
    φ hφ
  classical
  have hW : 𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho J Φ
      (𝓕.unitaryExponentSum J s c) := ⟨s, c, hdec, rfl⟩
  have hsum := h F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK Φ hΦ J _ hW φ hφ
  unfold StandardParabolicFamily.unitaryExponentSum at hsum
  exact 𝓕.pairingIntegrable_component_of_sum J K _ hφ.2.1 _ c
    (fun mu hmu => hdec.exponent mu (Finset.mem_filter.mp hmu).1) hsum
    (Finset.mem_filter.mpr ⟨hlam, hre⟩)

end Langlands.Global
