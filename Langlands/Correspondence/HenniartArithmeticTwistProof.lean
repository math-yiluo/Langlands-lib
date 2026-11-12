import Langlands.LocalFactor.Euler.Scaling
import Langlands.Correspondence.HenniartExtensionInputs
import Langlands.Correspondence.BlockPairEpsilon
import Langlands.Correspondence.AssemblyBlockPairEuler

/-!
# Unramified twists of arithmetic pair factors

Deligne (1973), (3.5.3) and (5.5.1)–(5.5.2): twisting the two members of a pair of
continuous irreducible Weil classes by the unramified characters with values `z`
and `z'` at geometric Frobenius substitutes `X ↦ z z' X` in the pair L-factor and
multiplies every epsilon certificate `c q^(-ms)` by `(z z') ^ m`.

The L-factor law is the scaling of the Frobenius operator on the inertia
invariants of the tensor product. The epsilon law needs no property of the
local-constant system beyond equivalence invariance: the spectral epsilon value
at `s` is the system evaluated at the spectral twist by `s`, and the bottom-field
restriction of the unramified character with value `t` at geometric Frobenius is
the spectral character at `s₀` with `q^(-s₀) = t`.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation Polynomial
open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

universe uK uW

/-! ### Weil–Deligne pairs -/

section TensorTwists

universe uk uG uA uB

variable {𝕜 : Type uk} [Field 𝕜] {G : Type uG} [Group G]

/-- Vanishing monodromy is invariant under equivalence of pairs. -/
theorem monodromy_eq_zero_of_equiv {ν : G →* 𝕜ˣ}
    {A : WeilDeligneRepresentation.{uk, uG, uA} 𝕜 G ν}
    {B : WeilDeligneRepresentation.{uk, uG, uB} 𝕜 G ν}
    (f : WeilDeligneRepresentation.Equiv A B) (hA : A.monodromy = 0) : B.monodromy = 0 := by
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := f.representationEquiv.toLinearEquiv.surjective v
  have h := LinearMap.congr_fun f.comm_monodromy w
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hA, LinearMap.zero_apply, map_zero] at h
  rw [LinearMap.zero_apply]
  exact h.symm

/-- Twisting the two factors of a zero-monodromy tensor by `χ` and `χ'` is
twisting the first factor by `χ χ'` and the second by the trivial character. -/
def tensorTwistMulEquiv {ν : G →* 𝕜ˣ} (A : FiniteRepresentation.{uk, uG, uA} 𝕜 G)
    (B : FiniteRepresentation.{uk, uG, uB} 𝕜 G) (χ χ' : G →* 𝕜ˣ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ A))
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ' B)))
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist (χ * χ') A))
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist 1 B))) :=
  WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv ν
    (A := WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ A))
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ' B)))
    (B := WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist (χ * χ') A))
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist 1 B)))
    (WeilDeligneRepresentation.tensor_monodromy_eq_zero rfl rfl)
    (WeilDeligneRepresentation.tensor_monodromy_eq_zero rfl rfl)
    (((FiniteRepresentation.tensorTwistEquiv χ χ' A B).trans
      (FiniteRepresentation.twistEquivOfEq (mul_one (χ * χ')).symm _)).trans
      (FiniteRepresentation.tensorTwistEquiv (χ * χ') 1 A B).symm)

/-- A zero-monodromy tensor is equivalent to the tensor of the trivial twists. -/
def tensorTwistOneEquiv {ν : G →* 𝕜ˣ} (A : FiniteRepresentation.{uk, uG, uA} 𝕜 G)
    (B : FiniteRepresentation.{uk, uG, uB} 𝕜 G) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.zeroMonodromy ν A)
        (WeilDeligneRepresentation.zeroMonodromy ν B))
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist 1 A))
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist 1 B))) :=
  WeilDeligneRepresentation.tensorEquiv
    (WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv ν
      (A := WeilDeligneRepresentation.zeroMonodromy ν A)
      (B := WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist 1 A)) rfl rfl
      (FiniteRepresentation.twistOneEquiv A).symm)
    (WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv ν
      (A := WeilDeligneRepresentation.zeroMonodromy ν B)
      (B := WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist 1 B)) rfl rfl
      (FiniteRepresentation.twistOneEquiv B).symm)

/-- Untwisting both factors by `α` and `β` and twisting the tensor by `ρ` with
`ρ α β = 1` recovers the tensor, by the identity map. -/
def tensorTwistCancelEquiv (A : FiniteRepresentation.{uk, uG, uA} 𝕜 G)
    (B : FiniteRepresentation.{uk, uG, uB} 𝕜 G) {α β ρ : G →* 𝕜ˣ}
    (h : ∀ g, ρ g * (α g * β g) = 1) :
    FiniteRepresentation.Equiv (FiniteRepresentation.tensor A B)
      (FiniteRepresentation.twist ρ (FiniteRepresentation.tensor
        (FiniteRepresentation.twist α A) (FiniteRepresentation.twist β B))) :=
  Representation.Equiv.mk (LinearEquiv.refl 𝕜 _)
    (fun g => TensorProduct.ext' fun (a : (A : Type uA)) (b : (B : Type uB)) => by
      change A.representation g a ⊗ₜ[𝕜] B.representation g b =
        (ρ g : 𝕜) • (((α g : 𝕜) • A.representation g a) ⊗ₜ[𝕜]
          ((β g : 𝕜) • B.representation g b))
      rw [TensorProduct.smul_tmul_smul, smul_smul, ← Units.val_mul, ← Units.val_mul, h g,
        Units.val_one, one_smul])

/-- Two successive twists by characters with product one cancel. -/
def zeroTwistCancelEquiv {ν : G →* 𝕜ˣ} (A : FiniteRepresentation.{uk, uG, uA} 𝕜 G)
    {χ η : G →* 𝕜ˣ} (h : ∀ g, η g * χ g = 1) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.zeroMonodromy ν
        (FiniteRepresentation.twist η (FiniteRepresentation.twist χ A)))
      (WeilDeligneRepresentation.zeroMonodromy ν A) where
  representationEquiv := Representation.Equiv.mk (LinearEquiv.refl 𝕜 _) (fun g => by
    apply LinearMap.ext
    intro v
    change (η g : 𝕜) • ((χ g : 𝕜) • A.representation g v) = A.representation g v
    rw [smul_smul, ← Units.val_mul, h g, Units.val_one, one_smul])
  comm_monodromy := rfl

end TensorTwists

/-! ### Unramified characters of the local Weil group -/

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartArithmeticTwistFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The inclusion of the subgroup fixing the bottom intermediate field. -/
abbrev baseInclusion : weilSubgroup K (baseExtension K) →* localWeilGroup K :=
  (weilSubgroup K (baseExtension K)).subtype

/-- The same inclusion as a continuous homomorphism. -/
def baseInclusionContinuous : weilSubgroup K (baseExtension K) →ₜ* localWeilGroup K where
  toMonoidHom := baseInclusion K
  continuous_toFun := continuous_subtype_val

theorem localUnramifiedCharacter_inertia (z : ℂˣ) (i : localInertia K) :
    (localUnramifiedCharacter K z).toMonoidHom i = 1 := by
  have hi : localDegree K i = 1 := i.property
  change z ^ (localDegree K i).toAdd = 1
  rw [hi, toAdd_one, zpow_zero]

theorem localUnramifiedCharacter_frobenius (z : ℂˣ) :
    (localUnramifiedCharacter K z).toMonoidHom (localGeometricFrobenius K) = z := by
  change z ^ (localDegree K (localGeometricFrobenius K)).toAdd = z
  rw [localGeometricFrobenius_degree, toAdd_ofAdd, zpow_one]

/-- For every complex unit `t` there is `s₀` with `q^(-s₀) = t`, in both the
spectral and the epsilon-monomial normalizations. -/
theorem exists_spectralExponent (t : ℂˣ) :
    ∃ s₀ : ℂ,
      Complex.exp (-s₀ * (Real.log (CommonClosureSpectral.baseCardinality K) : ℂ)) = t ∧
        (K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s₀) = t := by
  set q := K.canonicalTopologicalData.residueCardinality
  have hq : (1 : ℝ) < q := by exact_mod_cast K.canonicalTopologicalData.residueCardinality_gt_one
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq
  set L := Real.log q
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hlogq : Complex.log (q : ℂ) = (L : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hq0.le]
  have hexp : Complex.exp (-(-(Complex.log t) / L) * (L : ℂ)) = t := by
    rw [neg_div, neg_neg, div_mul_cancel₀ _ hL, Complex.exp_log t.ne_zero]
  refine ⟨-(Complex.log t) / L, hexp, ?_⟩
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  rw [Complex.cpow_def_of_ne_zero hq', hlogq, mul_comm]
  exact hexp

/-! ### Bottom-field restriction data of twisted classes -/

/-- Restricting the zero-monodromy pair of a twist is twisting the restriction. -/
def restrictTwistEquiv (A₀ : LocalWeilRepresentation.{uK, uW} K) (χ : localWeilGroup K →* ℂˣ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (baseInclusion K)
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
          (FiniteRepresentation.twist χ A₀)))
      (WeilDeligneRepresentation.twist (χ.comp (baseInclusion K))
        (WeilDeligneRepresentation.restrict (baseInclusion K)
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A₀))) where
  representationEquiv := Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl)
  comm_monodromy := rfl

/-- A bottom-field restriction datum of a zero-monodromy class, twisted by the
restriction of `χ`, is a datum of the twisted class. -/
theorem isBaseRestriction_twist (A₀ : LocalWeilRepresentation.{uK, uW} K)
    (χ : localWeilGroup K →* ℂˣ) {P : Pair.{uK, uW} K (baseExtension K)}
    (h : IsBaseRestriction K (WeilDeligneRepresentation.classOf
      (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A₀)) P) :
    IsBaseRestriction K (WeilDeligneRepresentation.classOf
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
          (FiniteRepresentation.twist χ A₀)))
      (WeilDeligneRepresentation.twist (χ.comp (baseInclusion K)) P) := by
  obtain ⟨f⟩ := IsBaseRestriction.nonempty_equiv K rfl h
  exact ⟨_, rfl, ⟨(restrictTwistEquiv K A₀ χ).trans (WeilDeligneRepresentation.twistEquiv _ f)⟩⟩

/-- A bottom-field restriction datum of a zero-monodromy class has zero monodromy. -/
theorem monodromy_eq_zero_of_isBaseRestriction (A₀ : LocalWeilRepresentation.{uK, uW} K)
    {P : Pair.{uK, uW} K (baseExtension K)}
    (h : IsBaseRestriction K (WeilDeligneRepresentation.classOf
      (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A₀)) P) :
    P.monodromy = 0 := by
  obtain ⟨f⟩ := IsBaseRestriction.nonempty_equiv K rfl h
  exact monodromy_eq_zero_of_equiv f rfl

/-! ### The epsilon law -/

/-- If the restrictions of `α`, `β` and the spectral character at `s₀` multiply to
one, then the pair epsilon value of `(A, B)` at `s` is that of `(α A, β B)` at
`s + s₀`, for pairs with zero monodromy. -/
theorem conditionalPairEpsilonValue_spectralShift (eC : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{uK, uW} K) (hε : NonabelianSystem.IsSystem K eC ε)
    (E : Extension K) (ψ' : AdditiveCharacter K E) (μ : HaarMeasure K E)
    (A B : Pair.{uK, uW} K E) (hA : A.toFiniteRepresentation.IsContinuous)
    (hB : B.toFiniteRepresentation.IsContinuous) (hA0 : A.monodromy = 0) (hB0 : B.monodromy = 0)
    (α β : weilSubgroup K E →ₜ* ℂˣ)
    (hαA : (WeilDeligneRepresentation.twist α.toMonoidHom A).toFiniteRepresentation.IsContinuous)
    (hβB : (WeilDeligneRepresentation.twist β.toMonoidHom B).toFiniteRepresentation.IsContinuous)
    (s₀ : ℂ) (h : ∀ w, CommonClosureSpectral.character K E s₀ w * (α w * β w) = 1)
    (Φ : GeometricFrobenius K E) (s : ℂ) :
    CommonClosureGamma.conditionalPairEpsilonValue K eC ε hε E ψ' μ A B hA hB Φ s =
      CommonClosureGamma.conditionalPairEpsilonValue K eC ε hε E ψ' μ
        (WeilDeligneRepresentation.twist α.toMonoidHom A)
        (WeilDeligneRepresentation.twist β.toMonoidHom B) hαA hβB Φ (s + s₀) := by
  set ρ := CommonClosureSpectral.character K E s₀
  set T := WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.twist α.toMonoidHom A)
    (WeilDeligneRepresentation.twist β.toMonoidHom B)
  have hT : T.toFiniteRepresentation.IsContinuous :=
    CommonClosureGamma.tensor_isContinuous K E _ _ hαA hβB
  have hT0 : T.monodromy = 0 := WeilDeligneRepresentation.tensor_monodromy_eq_zero hA0 hB0
  have hρT : (WeilDeligneRepresentation.twist ρ.toMonoidHom T).toFiniteRepresentation.IsContinuous :=
    FiniteRepresentation.isContinuous_twist ρ hT
  have hclass : underlyingClass K E (WeilDeligneRepresentation.twist ρ.toMonoidHom T) hρT =
      CommonClosureSpectral.virtualTwist K E s₀ (underlyingClass K E T hT) :=
    (SpectralTwist.virtual_ofRepresentation _ _ _ s₀ ⟨T.toFiniteRepresentation, hT⟩).symm
  change conditionalEpsilonValue K eC ε hε E ψ' μ (WeilDeligneRepresentation.tensor A B)
      (CommonClosureGamma.tensor_isContinuous K E A B hA hB) Φ s =
    conditionalEpsilonValue K eC ε hε E ψ' μ T hT Φ (s + s₀)
  rw [conditionalEpsilonValue_eq_of_equiv K eC ε hε E ψ' μ _ hρT
      (WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv _
        (WeilDeligneRepresentation.tensor_monodromy_eq_zero hA0 hB0) hT0
        (tensorTwistCancelEquiv A.toFiniteRepresentation B.toFiniteRepresentation
          (α := α.toMonoidHom) (β := β.toMonoidHom) (ρ := ρ.toMonoidHom) h)) Φ s,
    conditionalEpsilonValue_of_monodromy_zero K eC ε hε E ψ' μ _ hρT hT0 Φ s,
    conditionalEpsilonValue_of_monodromy_zero K eC ε hε E ψ' μ _ hT hT0 Φ (s + s₀), hclass]
  change ε E ψ' μ (CommonClosureSpectral.virtualTwist K E s
      (CommonClosureSpectral.virtualTwist K E s₀ (underlyingClass K E T hT))) =
    ε E ψ' μ (CommonClosureSpectral.virtualTwist K E (s + s₀) (underlyingClass K E T hT))
  rw [CommonClosureSpectral.virtualTwist_add]

/-- The epsilon monomial at `s + s₀` with `q^(-s₀) = t` is the monomial at `s`
with coefficient multiplied by `t ^ m`. -/
theorem epsilonMonomial_add (c t : ℂˣ) (m : ℤ) (s s₀ : ℂ)
    (ht : (K.canonicalTopologicalData.residueCardinality : ℂ) ^ (-s₀) = t) :
    RankinSelberg.epsilonMonomial K.canonicalTopologicalData.residueCardinality c m (s + s₀) =
      RankinSelberg.epsilonMonomial K.canonicalTopologicalData.residueCardinality
        (c * t ^ m) m s := by
  have hq : (K.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one
      K.canonicalTopologicalData.residueCardinality_gt_one).ne'
  unfold RankinSelberg.epsilonMonomial RankinSelberg.spectralPoint
  rw [neg_add, Complex.cpow_add _ _ hq, ht, mul_zpow]
  push_cast
  ring

/-! ### Twisted classes -/

theorem localUnramifiedCharacter_inv_mul (u : ℂˣ) (g : localWeilGroup K) :
    (localUnramifiedCharacter K u⁻¹).toMonoidHom g * (localUnramifiedCharacter K u).toMonoidHom g =
      1 := by
  change u⁻¹ ^ (localDegree K g).toAdd * u ^ (localDegree K g).toAdd = 1
  rw [← mul_zpow, inv_mul_cancel, one_zpow]

/-- The L-factor law on zero-monodromy representatives. -/
theorem arithmeticPairLFactor_unramifiedTwist (A₀ B₀ : LocalWeilRepresentation.{uK, uW} K)
    (z z' : ℂˣ) (P : ℂ[X])
    (h : arithmeticPairLFactor K
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A₀))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom B₀)) =
      (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹) :
    arithmeticPairLFactor K
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (FiniteRepresentation.twist (localUnramifiedCharacter K z).toMonoidHom A₀)))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (FiniteRepresentation.twist (localUnramifiedCharacter K z').toMonoidHom B₀))) =
      (algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C ((z : ℂ) * z') * X)))⁻¹ := by
  set ν := (localNormCharacter K).toMonoidHom
  set χ := (localUnramifiedCharacter K z).toMonoidHom
  set χ' := (localUnramifiedCharacter K z').toMonoidHom
  set M := (FiniteRepresentation.invariants (localInertia K)
    (FiniteRepresentation.tensor A₀ (FiniteRepresentation.twist 1 B₀))).representation
      (localGeometricFrobenius K)
  have h1 : ∀ i : localInertia K, (1 : localWeilGroup K →* ℂˣ) i = 1 := fun _ => rfl
  have hχχ' : ∀ i : localInertia K, (χ * χ') i = 1 := fun i => by
    rw [MonoidHom.mul_apply, localUnramifiedCharacter_inertia, localUnramifiedCharacter_inertia,
      mul_one]
  have horig : arithmeticPairLFactor K
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy ν A₀))
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy ν B₀)) =
      LocalFactor.rationalFactor M := by
    change LocalFactor.WeilDeligne.rationalLFactor
      (WeilDeligneRepresentation.tensor (WeilDeligneRepresentation.zeroMonodromy ν A₀)
        (WeilDeligneRepresentation.zeroMonodromy ν B₀)) (localInertia K)
          (localGeometricFrobenius K) = _
    rw [LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv (localInertia K)
        (tensorTwistOneEquiv A₀ B₀) (localGeometricFrobenius K),
      LocalFactor.WeilDeligne.rationalLFactor_zeroTensorTwist 1 (localInertia K) h1
        (localGeometricFrobenius K) A₀ (FiniteRepresentation.twist 1 B₀), MonoidHom.one_apply,
      Units.val_one, one_smul]
  have htwist : arithmeticPairLFactor K
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy ν
        (FiniteRepresentation.twist χ A₀)))
      (WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.zeroMonodromy ν
        (FiniteRepresentation.twist χ' B₀))) =
      LocalFactor.rationalFactor ((((χ * χ') (localGeometricFrobenius K) : ℂˣ) : ℂ) • M) := by
    change LocalFactor.WeilDeligne.rationalLFactor
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ A₀))
        (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.twist χ' B₀)))
      (localInertia K) (localGeometricFrobenius K) = _
    rw [LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv (localInertia K)
        (tensorTwistMulEquiv A₀ B₀ χ χ') (localGeometricFrobenius K),
      LocalFactor.WeilDeligne.rationalLFactor_zeroTensorTwist (χ * χ') (localInertia K) hχχ'
        (localGeometricFrobenius K) A₀ (FiniteRepresentation.twist 1 B₀)]
  rw [horig] at h
  have hP : LocalFactor.eulerPolynomial M = P :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ) (inv_injective h)
  rw [htwist, LocalFactor.rationalFactor, eulerPolynomial_smul, hP, MonoidHom.mul_apply,
    Units.val_mul, localUnramifiedCharacter_frobenius, localUnramifiedCharacter_frobenius]

/-- The epsilon law on zero-monodromy representatives. -/
theorem isArithmeticPairEpsilonFactor_unramifiedTwist (eC : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{uK, uW} K) (hε : NonabelianSystem.IsSystem K eC ε)
    (ψ : NontrivialAdditiveCharacter K) (A₀ B₀ : LocalWeilRepresentation.{uK, uW} K)
    (z z' c : ℂˣ) (m : ℤ)
    (h : IsArithmeticPairEpsilonFactor K eC ε hε ψ
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom A₀))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom B₀)) c m) :
    IsArithmeticPairEpsilonFactor K eC ε hε ψ
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (FiniteRepresentation.twist (localUnramifiedCharacter K z).toMonoidHom A₀)))
        (WeilDeligneRepresentation.classOf
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter K).toMonoidHom
            (FiniteRepresentation.twist (localUnramifiedCharacter K z').toMonoidHom B₀)))
        (c * (z * z') ^ m) m := by
  obtain ⟨⟨ψ₁, μ₁, A, B, ⟨hψ₁, hμ₁, hAr, hBr⟩, hAc, hBc⟩, hΦ, hall⟩ := h
  set ι := baseInclusionContinuous K
  refine ⟨⟨ψ₁, μ₁, WeilDeligneRepresentation.twist ((localUnramifiedCharacter K z).comp ι).toMonoidHom A,
    WeilDeligneRepresentation.twist ((localUnramifiedCharacter K z').comp ι).toMonoidHom B,
    ⟨hψ₁, hμ₁, isBaseRestriction_twist K A₀ _ hAr, isBaseRestriction_twist K B₀ _ hBr⟩,
    FiniteRepresentation.isContinuous_twist _ hAc, FiniteRepresentation.isContinuous_twist _ hBc⟩,
    hΦ, ?_⟩
  rintro ψ' μ A' B' ⟨hψ', hμ', hA'r, hB'r⟩ hA'c hB'c Φ s
  obtain ⟨s₀, hs₀, hq₀⟩ := exists_spectralExponent K (z * z')
  set α := (localUnramifiedCharacter K z⁻¹).comp ι
  set β := (localUnramifiedCharacter K z'⁻¹).comp ι
  have hA'0 := monodromy_eq_zero_of_isBaseRestriction K _ hA'r
  have hB'0 := monodromy_eq_zero_of_isBaseRestriction K _ hB'r
  have hρ (w : weilSubgroup K (baseExtension K)) :
      CommonClosureSpectral.character K (baseExtension K) s₀ w =
        (z * z') ^ (localDegree K w.val).toAdd := by
    apply Units.ext
    rw [CommonClosureSpectral.character_apply, hs₀, Units.val_zpow_eq_zpow_val]
  have hcancel (w : weilSubgroup K (baseExtension K)) :
      CommonClosureSpectral.character K (baseExtension K) s₀ w * (α w * β w) = 1 := by
    rw [hρ w]
    change (z * z') ^ (localDegree K w.val).toAdd *
      (z⁻¹ ^ (localDegree K w.val).toAdd * z'⁻¹ ^ (localDegree K w.val).toAdd) = 1
    rw [← mul_zpow, ← mul_zpow, mul_mul_mul_comm, mul_inv_cancel, mul_inv_cancel, one_mul,
      one_zpow]
  have hA''r := isBaseRestriction_twist K
    (FiniteRepresentation.twist (localUnramifiedCharacter K z).toMonoidHom A₀)
    (localUnramifiedCharacter K z⁻¹).toMonoidHom hA'r
  have hB''r := isBaseRestriction_twist K
    (FiniteRepresentation.twist (localUnramifiedCharacter K z').toMonoidHom B₀)
    (localUnramifiedCharacter K z'⁻¹).toMonoidHom hB'r
  rw [(WeilDeligneRepresentation.classOf_eq_iff _ _).2
    ⟨zeroTwistCancelEquiv A₀ (localUnramifiedCharacter_inv_mul K z)⟩] at hA''r
  rw [(WeilDeligneRepresentation.classOf_eq_iff _ _).2
    ⟨zeroTwistCancelEquiv B₀ (localUnramifiedCharacter_inv_mul K z')⟩] at hB''r
  have hαA : (WeilDeligneRepresentation.twist α.toMonoidHom A').toFiniteRepresentation.IsContinuous :=
    FiniteRepresentation.isContinuous_twist α hA'c
  have hβB : (WeilDeligneRepresentation.twist β.toMonoidHom B').toFiniteRepresentation.IsContinuous :=
    FiniteRepresentation.isContinuous_twist β hB'c
  have h1 := conditionalPairEpsilonValue_spectralShift K eC ε hε _ ψ' μ A' B' hA'c hB'c hA'0 hB'0
    α β hαA hβB s₀ hcancel Φ s
  have h2 := hall ψ' μ (WeilDeligneRepresentation.twist α.toMonoidHom A')
    (WeilDeligneRepresentation.twist β.toMonoidHom B') ⟨hψ', hμ', hA''r, hB''r⟩ hαA hβB Φ (s + s₀)
  rw [h1, h2, epsilonMonomial_add K c (z * z') m s s₀ hq₀]

/-! ### The statement -/

/-- Deligne (1973), (3.5.3) and (5.5.1)–(5.5.2), for the actual arithmetic pair
factors: unramified twists act on pair L-factors by `X ↦ z z' X` and on epsilon
certificates by `(z z') ^ m`. -/
theorem arithmeticPairUnramifiedTwist :
    ArithmeticPairUnramifiedTwistStatement.{uK, uW} := by
  intro p _ K eC ε hε ψ r n σ τ z z'
  obtain ⟨cσ, hσ⟩ := σ
  obtain ⟨cτ, hτ⟩ := τ
  obtain ⟨⟨A₀, hA₀⟩, rfl⟩ := Quotient.exists_rep cσ
  obtain ⟨⟨B₀, hB₀⟩, rfl⟩ := Quotient.exists_rep cτ
  exact ⟨fun P h => arithmeticPairLFactor_unramifiedTwist K A₀ B₀ z z' P h,
    fun c m h => isArithmeticPairEpsilonFactor_unramifiedTwist K eC ε hε ψ A₀ B₀ z z' c m h⟩

end Langlands.Henniart.Extension
