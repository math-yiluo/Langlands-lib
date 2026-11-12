import Langlands.Shimura.Unitary.KottwitzPrincipalSeries
import Langlands.Representation.Unramified.HeckeOperators
import Langlands.Shimura.LevelHecke

/-! # Unramified base-change Satake parameters of Kottwitz's unitary similitude groups -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField TensorProduct

set_option linter.unusedSectionVars false

universe u v w uL uV

namespace Langlands.Shimura.KottwitzUnramified

open Langlands.Global.AdelicFunctoriality

/-- The multiset of values of a family indexed by `Fin n`, as an element of `Sym α n`. -/
def symOfFn {α : Type*} {n : ℕ} (f : Fin n → α) : Sym α n :=
  ⟨(List.ofFn f : Multiset α), by simp⟩

theorem symOfFn_comp_perm {α : Type*} {n : ℕ} (f : Fin n → α) (e : Equiv.Perm (Fin n)) :
    symOfFn (f ∘ e) = symOfFn f := by
  apply Sym.ext
  change (List.ofFn (f ∘ e) : Multiset α) = (List.ofFn f : Multiset α)
  rw [← Fin.univ_val_map, ← Fin.univ_val_map, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

theorem symOfFn_map {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    (symOfFn f).map g = symOfFn (g ∘ f) := by
  apply Sym.ext
  simp [symOfFn, List.map_ofFn]

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]
variable [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
variable {σ : SecondKindInvolution E K A} {p : HeightOneSpectrum (𝓞 ℚ)} {n : ℕ}
variable (c : UnramifiedChart σ p n)
variable {L : Type uL} [Field L]

section Parameters

/-- The base-change Satake parameter at a place `w ∣ p` of `K`: the multiset of the
unitarily normalized position values `ξ(λ_{w,k}(p)) · s^{f_w (n - 1 - 2k)}`. -/
def UnramifiedChart.baseChangeParameter (s : SqrtPrime p L) (ξ : c.torus →* Lˣ)
    (w : FinitePlacesAbove K p) : Sym Lˣ n :=
  symOfFn (c.positionValue s ξ w)

/-- Weyl-equivalent characters have the same base-change parameters. -/
theorem UnramifiedChart.baseChangeParameter_of_weylEquivalent {s : SqrtPrime p L}
    {ξ ξ' : c.torus →* Lˣ} (h : c.WeylEquivalent s ξ ξ') (w : FinitePlacesAbove K p) :
    c.baseChangeParameter s ξ' w = c.baseChangeParameter s ξ w := by
  obtain ⟨τ, hτ⟩ := h
  have hf : c.positionValue s ξ' w = c.positionValue s ξ w ∘ (τ.1 w) :=
    funext fun k => c.positionValue_of_weyl τ hτ w k
  rw [UnramifiedChart.baseChangeParameter, UnramifiedChart.baseChangeParameter, hf,
    symOfFn_comp_perm]

theorem positionCocharacter_placeConj (w : FinitePlacesAbove K p) (k : Fin n) :
    positionCocharacter E p n (placeConj (E := E) p w) (Fin.rev k) =
      -positionCocharacter E p n w k := by
  classical
  apply Subtype.ext
  refine Prod.ext ?_ (by simp [positionCocharacter])
  funext w' j
  change (positionCocharacter E p n (placeConj (E := E) p w) (Fin.rev k)).1.1 w' j =
    -((positionCocharacter E p n w k).1.1 w' j)
  rw [positionCocharacter_coord, positionCocharacter_coord, placeConj_placeConj, Fin.rev_rev]
  ring

/-- The normalized position values at the conjugate place are the inverses:
`positionValue (w̄) (rev k) = (positionValue w k)⁻¹`. -/
theorem UnramifiedChart.positionValue_placeConj (s : SqrtPrime p L) (ξ : c.torus →* Lˣ)
    (w : FinitePlacesAbove K p) (k : Fin n) :
    c.positionValue s ξ (placeConj (E := E) p w) (Fin.rev k) = (c.positionValue s ξ w k)⁻¹ := by
  rw [UnramifiedChart.positionValue, UnramifiedChart.positionValue,
    positionCocharacter_placeConj, ofAdd_neg, map_inv, map_inv, inertiaDegree_placeConj,
    rev_val_cast, mul_inv, ← zpow_neg]
  congr 2
  ring

/-- Conjugate self-duality: the base-change parameter at `w̄` consists of the inverses of
the base-change parameter at `w`. -/
theorem UnramifiedChart.baseChangeParameter_placeConj (s : SqrtPrime p L) (ξ : c.torus →* Lˣ)
    (w : FinitePlacesAbove K p) :
    c.baseChangeParameter s ξ (placeConj (E := E) p w) =
      (c.baseChangeParameter s ξ w).map (fun z => z⁻¹) := by
  have hf : c.positionValue s ξ (placeConj (E := E) p w) =
      (fun z => z⁻¹) ∘ c.positionValue s ξ w ∘ Fin.revPerm := by
    funext k
    have h := c.positionValue_placeConj s ξ w (Fin.rev k)
    rw [Fin.rev_rev] at h
    simp [h]
  rw [UnramifiedChart.baseChangeParameter, UnramifiedChart.baseChangeParameter, hf,
    symOfFn_map]
  change symOfFn (((fun z => z⁻¹) ∘ c.positionValue s ξ w) ∘ Fin.revPerm) = _
  rw [symOfFn_comp_perm]

/-- Clozel's normalization (5.3): `r_v^T(Frob_v) = q_v^{(1-n)/2} t_v`, read at the place `w`
with `q_w^{1/2} = s^{f_w}`. -/
def UnramifiedChart.clozelParameter (s : SqrtPrime p L) (ξ : c.torus →* Lˣ) (w : FinitePlacesAbove K p) :
    Sym Lˣ n :=
  (c.baseChangeParameter s ξ w).map
    (fun z => z * s.1 ^ ((inertiaDegree w : ℤ) * (1 - (n : ℤ))))

/-- `t` is a base-change Satake parameter of `π` at `w`, with values in an extension `Ω` of
the coefficient field `L` of `π`: it is the base-change parameter of some principal-series
parameter `ξ : T →* Ωˣ` of `π`, for the chosen square root `s` of `p` in `Ω`. -/
def UnramifiedChart.IsBaseChangeParameterOf [Module.Finite ℚ A]
    (π : SmoothRep.{uL, w, uV} L (LocalPoints σ p)) {Ω : Type*} [Field Ω] [Algebra L Ω]
    (s : SqrtPrime p Ω) (w : FinitePlacesAbove K p) (t : Sym Ωˣ n) : Prop :=
  ∃ ξ : c.torus →* Ωˣ, c.HasPrincipalSeriesParameter π ξ ∧ c.baseChangeParameter s ξ w = t

/-- If any two principal-series parameters of `π` are Weyl equivalent (the uniqueness part
of the Satake parametrization), the base-change parameter of `π` at `w` is unique. -/
theorem UnramifiedChart.IsBaseChangeParameterOf.unique [Module.Finite ℚ A]
    {π : SmoothRep.{uL, w, uV} L (LocalPoints σ p)} {Ω : Type*} [Field Ω] [Algebra L Ω]
    {s : SqrtPrime p Ω} {w : FinitePlacesAbove K p} {t t' : Sym Ωˣ n}
    (huniq : ∀ ξ ξ' : c.torus →* Ωˣ, c.HasPrincipalSeriesParameter π ξ →
      c.HasPrincipalSeriesParameter π ξ' → c.WeylEquivalent s ξ ξ')
    (h : c.IsBaseChangeParameterOf π s w t) (h' : c.IsBaseChangeParameterOf π s w t') :
    t = t' := by
  obtain ⟨ξ, hξ, rfl⟩ := h
  obtain ⟨ξ', hξ', rfl⟩ := h'
  exact (c.baseChangeParameter_of_weylEquivalent (huniq ξ ξ' hξ hξ') w).symm

end Parameters

section Complex

variable (p) in
/-- The positive square root of `p` in `ℂ`, Kottwitz's choice over `ℂ` (the unitary
correspondence). -/
def complexSqrtPrime : SqrtPrime p ℂ :=
  ⟨Units.mk0 ((Real.sqrt (residuePrime p : ℝ) : ℝ) : ℂ) (by
    have : (0 : ℝ) < Real.sqrt (residuePrime p : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero residuePrime_ne_zero))
    exact_mod_cast this.ne'), by
    simp only [Units.val_mk0]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]⟩

/-- The base-change Satake parameter at `w`, for complex coefficients and the positive
square root of `p`, as an element of the published `Langlands.Unramified.Eigenvalues n`. -/
def UnramifiedChart.baseChangeEigenvalues (ξ : c.torus →* ℂˣ) (w : FinitePlacesAbove K p) :
    Langlands.Unramified.Eigenvalues n :=
  c.baseChangeParameter (complexSqrtPrime p) ξ w

end Complex

section SplitNormalization

variable [Module.Finite ℚ A]

variable (E p n) in
/-- The cocharacter `Σ_{k < i} λ_{w,k}`: at a split place its point is
`diag(p, …, p, 1, …, 1)` (with `i` entries `p`) in the `GL_n(K_w)` factor. -/
def partialCocharacter (w : FinitePlacesAbove K p) (i : ℕ) : localCocharacters E K p n :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < i), positionCocharacter E p n w k

/-- The normalization of the base-change parameters at the split places, for a compact
open level `Kp` equal to the chart's level: on the `K_p`-fixed vectors of a representation
with principal-series parameter `ξ`, the double-coset operator of
`diag(p^{(i)}, 1^{(n-i)})` in the `GL_n(K_w)` factor acts by
`q_w^{i(n-i)/2} e_i(t)`, where `t` is the base-change parameter at `w` and `e_i` the
`i`-th elementary symmetric function. This is the convention of the published
`Langlands.Unramified.HasSphericalHeckeSpectrum`. -/
def UnramifiedChart.SplitPlaceHeckeNormalization (Kp : Shimura.CompactOpenLevel (LocalPoints σ p)) :
    Prop :=
  Kp.subgroup = c.level →
    ∀ (π : SmoothRep.{0, w, uV} ℂ (LocalPoints σ p)) (ξ : c.torus →* ℂˣ),
      c.HasPrincipalSeriesParameter π (Ω := ℂ) ξ →
        ∀ (w : FinitePlacesAbove K p), placeConj (E := E) p w ≠ w →
          ∀ (i : ℕ), i ≤ n → ∀ v : fixedVectors π.representation Kp.subgroup,
            LevelHecke.heckeOperator π.representation Kp Kp
                (c.cocharHom (Multiplicative.ofAdd (partialCocharacter E p n w i))).1 v =
              (((complexSqrtPrime p).1 : ℂ) ^ (inertiaDegree w * (i * (n - i))) *
                Langlands.Unramified.elementaryCoefficient
                  (c.baseChangeEigenvalues ξ w) i) • v

end SplitNormalization

end Langlands.Shimura.KottwitzUnramified
