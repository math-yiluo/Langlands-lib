import Langlands.Representation.Archimedean.ComplexGenericParameterReduction
import Langlands.Representation.Archimedean.PrincipalSeriesStability

/-!
# Reduction of the complex Langlands quotient statement

`ComplexLanglandsQuotientStatement` (Knapp 1994, Theorem 4, quotient form) says that every
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module receives a nonzero intertwining map from the
`U(n)`-finite functions of the principal series of `n` complex characters whose exponents
have non-increasing real parts. This file splits it into three statements:

* `ComplexLanglandsSubrepresentationStatement` (Langlands classification, subrepresentation
  form; Wallach 1979, Theorems 4.18 and 6.7): every irreducible admissible module has a
  nonzero intertwining map into the `U(n)`-finite functions of the principal series of `n`
  characters whose exponents have *non-decreasing* real parts;
* `ComplexContragredientStatement`: every irreducible admissible module `V` has an irreducible
  admissible `U(n)`-finite contragredient `W` with an invariant pairing `W × V → ℂ` that
  separates the points of `V` and represents every `U(n)`-finite linear functional on `W`;
* `ComplexStandardDualityStatement`: the `U(n)`-finite functions of the principal series of
  pointwise inverse characters carry an invariant pairing, nondegenerate in the second
  argument (integration over `U(n)`).

`complexLanglandsQuotientReduction` proves that the three imply the target: dualize, embed
the contragredient, and transpose the embedding along the two pairings.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

section Embedding

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `B` is a `(𝔤, K)`-intertwining map from `(ρ, π)` into the `U(n)`-finite functions of the
standard module of `ds`: it carries `ρ(k)` for `k ∈ U(n)` to right translation by `k`, and
`π(1 ⊗ X)` for a real direction `X ∈ 𝔤𝔩_n(ℂ)` to the right derivative along `X`. -/
def IsComplexStandardEmbedding (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List ComplexCharacterData)
    (B : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) : Prop :=
  (∀ (k : unitaryCompact ℂ n) (v : V),
    (B (ρ ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ v) :
        Langlands.GeneralLinear n ℂ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (k : Langlands.GeneralLinear n ℂ) (B v : Langlands.GeneralLinear n ℂ → ℂ)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℂ) (v : V),
    (B (π (1 ⊗ₜ X) v) : Langlands.GeneralLinear n ℂ → ℂ) =
      rightDerivative (matrixModel ℂ n) X (B v : Langlands.GeneralLinear n ℂ → ℂ)

end Embedding

/-- Langlands classification of irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-modules,
subrepresentation form (Wallach 1979, Theorems 4.18 and 6.7, for `GL_n(ℂ)`, whose minimal
parabolic subgroup is the upper triangular Borel subgroup): every irreducible admissible
module `(ρ, π)` has a nonzero intertwining map into the `U(n)`-finite functions of the
standard module of some list of `n` complex characters whose exponents have non-decreasing
real parts, `Re t₁ ≤ Re t₂ ≤ ⋯ ≤ Re t_n`. -/
def ComplexLanglandsSubrepresentationStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ ds : List ComplexCharacterData, ds.length = n ∧
        ds.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re) ∧
        ∃ B : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
          B ≠ 0 ∧ IsComplexStandardEmbedding n ρ π ds B

/-- The `U(n)`-finite contragredient of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module
(the `K`-finite contragredient `Hom_ℂ(V, ℂ)_K` of Knapp–Vogan 1995, Chapter II, remark after
(2.42); for admissible `V` it is again irreducible and admissible, and `V` is its
`K`-finite dual): every irreducible admissible module `(ρ, π)` on `V` has an
irreducible admissible module `(ρ', π')` on some `W` and a bilinear pairing `P : W × V → ℂ`
that is `U(n)`-invariant, `P(ρ'(k) w, ρ(k) v) = P(w, v)`, and `𝔤`-invariant,
`P(π'(Y) w, v) + P(w, π(Y) v) = 0`, separates the points of `V`, and represents every
`U(n)`-finite linear functional on `W`, for the dual representation `ℓ ↦ ℓ ∘ ρ'(k)⁻¹`, as
`P(·, v)` for some `v ∈ V`. -/
def ComplexContragredientStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W)
        (ρ' : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) W)
        (π' : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W),
        IsComplexGKModule n ρ' π' ∧ IsIrreducibleGKModule ρ' π' ∧ IsAdmissibleGKModule ρ' ∧
        ∃ P : W →ₗ[ℂ] V →ₗ[ℂ] ℂ,
          (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (w : W) (v : V),
            P (ρ' k w) (ρ k v) = P w v) ∧
          (∀ (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) (w : W) (v : V),
            P (π' Y w) v + P w (π Y v) = 0) ∧
          (∀ v : V, (∀ w : W, P w v = 0) → v = 0) ∧
          ∀ ℓ : Module.Dual ℂ W, FiniteVectors.IsFiniteVector (Representation.dual ρ') ℓ →
            ∃ v : V, ∀ w : W, ℓ w = P w v

/-- Duality of complex principal series (the standard pairing `⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk`
of principal series induced from inverse characters): if the position
characters of `ds` and `ds'` are pointwise inverse, there is a bilinear pairing `Q` of the
`U(n)`-finite functions of their standard modules that is invariant under right translation
by `U(n)`, `Q(R(k) f, R(k) h) = Q(f, h)`, and under right derivatives,
`Q(R(X) f, h) + Q(f, R(X) h) = 0`, and nondegenerate in the second argument: for every
`h ≠ 0` some `f` has `Q(f, h) ≠ 0`. -/
def ComplexStandardDualityStatement : Prop :=
  ∀ (n : ℕ) (ds ds' : List ComplexCharacterData),
    (∀ (i : ℕ) (z : ℂˣ),
      complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1) →
      ∃ Q : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
          kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n) →ₗ[ℂ] ℂ,
        (∀ (k : unitaryCompact ℂ n)
            (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
            (h : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n))
            (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
                (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
              kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
            (hh : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
                (k : Langlands.GeneralLinear n ℂ) (h : Langlands.GeneralLinear n ℂ → ℂ) ∈
              kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
          Q ⟨_, hf⟩ ⟨_, hh⟩ = Q f h) ∧
        (∀ (X : Matrix (Fin n) (Fin n) ℂ)
            (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
            (h : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n))
            (hf : rightDerivative (matrixModel ℂ n) X (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
              kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
            (hh : rightDerivative (matrixModel ℂ n) X (h : Langlands.GeneralLinear n ℂ → ℂ) ∈
              kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
          Q ⟨_, hf⟩ h + Q f ⟨_, hh⟩ = 0) ∧
        ∀ h : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n),
          h ≠ 0 → ∃ f, Q f h ≠ 0

/-- The three statements above imply `ComplexLanglandsQuotientStatement`. -/
def ComplexLanglandsQuotientReductionStatement : Prop :=
  ComplexLanglandsSubrepresentationStatement.{uV} → ComplexContragredientStatement.{uV} →
    ComplexStandardDualityStatement → ComplexLanglandsQuotientStatement.{uV}

/-! ## Proof of the reduction -/

/-- The inverse `z ↦ (z/‖z‖)^{-l} ‖z‖^{-2t}` of the complex character
`z ↦ (z/‖z‖)^l ‖z‖^{2t}`. -/
def complexCharacterDataInv (d : ComplexCharacterData) : ComplexCharacterData where
  character := d.character⁻¹
  weight := -d.weight
  exponent := -d.exponent
  character_eq z := by
    change (((d.character z)⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val, d.character_eq z, zpow_neg, mul_neg, Complex.cpow_neg,
      mul_inv]

/-- The position characters of the inverse list are the pointwise inverses. -/
theorem complexPositionCharacter_map_inv_mul :
    ∀ (ds : List ComplexCharacterData) (i : ℕ) (z : ℂˣ),
      complexPositionCharacter (ds.map complexCharacterDataInv) i z *
        complexPositionCharacter ds i z = 1
  | [], _, _ => by simp [complexPositionCharacter]
  | d :: _, 0, z => by
      change (((d.character z)⁻¹ : ℂˣ) : ℂ) * (d.character z : ℂ) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  | _ :: ds, p + 1, z => complexPositionCharacter_map_inv_mul ds p z

/-- Proof of the reduction. Let `W` be the contragredient of `V` with pairing `P` and embed
`W` into the standard module of `ds'` by `B`. With `ds` the list of inverse characters and
`Q` the duality pairing, the functional `w ↦ Q(f, B w)` is `U(n)`-finite for each
`U(n)`-finite `f`, so it is `P(·, A f)` for a unique `A f ∈ V`. The map `A` intertwines by
the invariance of `P`, `Q` and `B`, and it is nonzero because `B` is nonzero and `Q` is
nondegenerate in its second argument. -/
theorem complexLanglandsQuotientReduction : ComplexLanglandsQuotientReductionStatement.{uV} := by
  intro hS1 hS2 hS3 n V _ _ ρ π hgk hirr hadm
  obtain ⟨W, _, _, ρ', π', hgk', hirr', hadm', P, hPK, hPg, hPnd, hPfin⟩ :=
    hS2 n V ρ π hgk hirr hadm
  obtain ⟨ds', hlen', hord', B, hB0, hBK, hBX⟩ := hS1 n W ρ' π' hgk' hirr' hadm'
  set ds := ds'.map complexCharacterDataInv with hds
  obtain ⟨Q, hQK, hQX, hQnd⟩ := hS3 n ds ds' (complexPositionCharacter_map_inv_mul ds')
  -- The functionals `w ↦ Q(f, B w)`.
  set Λ := Q.compl₂ B with hΛ
  have hΛapp : ∀ f w, Λ f w = Q f (B w) := fun f w => rfl
  -- Invariance of `Λ` under `U(n)`.
  have hΛK : ∀ (k : unitaryCompact ℂ n)
      (f : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))
      (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
          (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)) (w : W),
      Λ ⟨_, hf⟩ (ρ' ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ w) =
        Λ f w := by
    intro k f hf w
    have hh : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (k : Langlands.GeneralLinear n ℂ) (B w : Langlands.GeneralLinear n ℂ → ℂ) ∈
          kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n) := by
      rw [← hBK k w]
      exact (B _).2
    have e : B (ρ' ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ w) =
        ⟨_, hh⟩ := Subtype.ext (hBK k w)
    rw [hΛapp, hΛapp, e]
    exact hQK k f (B w) hf hh
  -- `Λ f` is `U(n)`-finite.
  have hfin : ∀ f, FiniteVectors.IsFiniteVector (Representation.dual ρ') (Λ f) := by
    intro f
    set S : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
      Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
          (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ)) with hS
    have hSfin : FiniteDimensional ℂ S := (mem_kFiniteVectors_iff _ _ _).mp f.2.2
    set S' := S.comap
      (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)).subtype with hS'
    have hS'fin : FiniteDimensional ℂ S' := by
      refine Module.Finite.of_injective
        ((kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)).subtype.restrict
          (p := S') (q := S) fun x hx => hx) ?_
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : S => (z : Langlands.GeneralLinear n ℂ → ℂ)) hxy))
    have hT : FiniteDimensional ℂ (S'.map Λ) := Module.Finite.map S' Λ
    refine Submodule.finiteDimensional_of_le (S₂ := S'.map Λ) ?_
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, rfl⟩
    set kc : unitaryCompact ℂ n := ⟨Unitary.toUnits u⁻¹, (u⁻¹).2⟩ with hkc
    have hu : (⟨((kc : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), kc.2⟩ :
        Matrix.unitaryGroup (Fin n) ℂ) = u⁻¹ := Subtype.ext rfl
    have hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        ((kc⁻¹ : unitaryCompact ℂ n) : Langlands.GeneralLinear n ℂ)
          (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) :=
      rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 (kc⁻¹).2
    set g : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) := ⟨_, hg⟩
      with hgdef
    have hRg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (kc : Langlands.GeneralLinear n ℂ) (g : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) :=
      rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds g.2 kc.2
    have hfg : (⟨_, hRg⟩ : kFiniteFunctions (complexStandardModule n ds)
        (unitaryCompact ℂ n)) = f := by
      apply Subtype.ext
      change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
          (kc : Langlands.GeneralLinear n ℂ)
          (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
            ((kc⁻¹ : unitaryCompact ℂ n) : Langlands.GeneralLinear n ℂ)
            (f : Langlands.GeneralLinear n ℂ → ℂ)) = f
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, map_one, Module.End.one_apply]
    have key := hΛK kc g hRg
    rw [hfg, hu] at key
    refine ⟨g, ?_, ?_⟩
    · change (g : Langlands.GeneralLinear n ℂ → ℂ) ∈ S
      exact Submodule.subset_span ⟨kc⁻¹, rfl⟩
    · apply LinearMap.ext
      intro w
      rw [← key]
      rfl
  -- The intertwining map `A`.
  have hPinj : Function.Injective P.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hPnd v fun w => by
      have := congrArg (fun ℓ : W →ₗ[ℂ] ℂ => ℓ w) hv
      simpa using this
  have hrange : ∀ f, Λ f ∈ LinearMap.range P.flip := by
    intro f
    obtain ⟨v, hv⟩ := hPfin (Λ f) (hfin f)
    exact ⟨v, LinearMap.ext fun w => (hv w).symm⟩
  set A : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ] V :=
    (LinearEquiv.ofInjective P.flip hPinj).symm.toLinearMap ∘ₗ
      Λ.codRestrict (LinearMap.range P.flip) hrange with hAdef
  have hA : ∀ f w, P w (A f) = Q f (B w) := by
    intro f w
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective P.flip hPinj).apply_symm_apply
        (Λ.codRestrict (LinearMap.range P.flip) hrange f))
    rw [LinearEquiv.ofInjective_apply] at h
    have h' := congrArg (fun ℓ : W →ₗ[ℂ] ℂ => ℓ w) h
    exact h'
  have hext : ∀ x y : V, (∀ w, P w x = P w y) → x = y := by
    intro x y hxy
    rw [← sub_eq_zero]
    exact hPnd _ fun w => by rw [map_sub, hxy, sub_self]
  refine ⟨ds, by rw [hds, List.length_map, hlen'], ?_, A, ?_, ?_, ?_⟩
  · unfold IsComplexLanglandsOrdered
    rw [hds, List.pairwise_map]
    refine hord'.imp fun {d e} h => ?_
    simp only [complexCharacterDataInv, Complex.neg_re]
    linarith
  · -- `A ≠ 0`.
    intro hA0
    obtain ⟨w, hw⟩ : ∃ w, B w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hB0 (LinearMap.ext hcon)
    obtain ⟨f, hf⟩ := hQnd (B w) hw
    apply hf
    rw [← hA, hA0, LinearMap.zero_apply, map_zero]
  · -- Equivariance for `U(n)`.
    intro k f
    refine ⟨rightTranslation_mem_kFiniteFunctions_complexStandardModule n ds f.2 k.2, ?_⟩
    apply hext
    intro w'
    set k' : Matrix.unitaryGroup (Fin n) ℂ :=
      ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ with hk'
    have hw : ρ' k' (ρ' k'⁻¹ w') = w' := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hw, hPK, hA, hA]
    exact hΛK k f _ (ρ' k'⁻¹ w')
  · -- Equivariance for `𝔤𝔩_n(ℂ)`.
    intro X f
    refine ⟨rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X, ?_⟩
    apply hext
    intro w
    have hh : rightDerivative (matrixModel ℂ n) X (B w : Langlands.GeneralLinear n ℂ → ℂ) ∈
        kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n) := by
      rw [← hBX X w]
      exact (B _).2
    have e : B (π' (1 ⊗ₜ X) w) = ⟨_, hh⟩ := Subtype.ext (hBX X w)
    have h1 := hPg (1 ⊗ₜ X) w (A f)
    have h2 := hQX X f (B w)
      (rightDerivative_mem_kFiniteFunctions_complexStandardModule n ds f.2 X) hh
    have h3 := hA f (π' (1 ⊗ₜ X) w)
    rw [e] at h3
    rw [hA]
    linear_combination h2 - h1 + h3

end Langlands.Archimedean
