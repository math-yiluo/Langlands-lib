import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.LocalFactor.ArchimedeanGamma

/-!
# Reduction of Casselman's theorem in quotient form for `GL_n(ℝ)`

`RealPrincipalSeriesQuotientStatement` (Casselman's subrepresentation theorem, quotient form)
says that every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module receives a nonzero intertwiner
from the `O(n)`-finite functions of the principal series of some `n` characters of `ℝ^×`. This
file splits it into three statements:

* `RealPrincipalSeriesSubrepresentationStatement` (Casselman's subrepresentation theorem,
  Wallach 1979, Theorem 4.18, for `GL_n(ℝ)`, whose minimal parabolic subgroup is the upper
  triangular Borel subgroup): every irreducible admissible module has a nonzero intertwining
  map into the `O(n)`-finite functions of the principal series of some `n` characters;
* `RealContragredientStatement`: every irreducible admissible module `V` has an irreducible
  admissible `O(n)`-finite contragredient `W` with an invariant pairing `W × V → ℂ` that
  separates the points of `V` and represents every `O(n)`-finite linear functional on `W`;
* `RealPrincipalSeriesDualityStatement`: the `O(n)`-finite functions of the principal series
  of pointwise inverse characters carry an invariant pairing, nondegenerate in the second
  argument (integration over `O(n)`).

`realPrincipalSeriesQuotientReduction` proves that the three imply the target: dualize, embed
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

/-- `B` is a `(𝔤, K)`-intertwining map from `(ρ, π)` into the `O(n)`-finite functions of the
standard module of the real blocks `ds`: it carries `ρ(k)` for `k ∈ O(n)` to right translation
by `k`, and `π(1 ⊗ X)` for a real matrix `X` to the right derivative along `X`. -/
def IsRealStandardEmbedding (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (ds : List RealBlock)
    (B : V →ₗ[ℂ] kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) : Prop :=
  (∀ (k : unitaryCompact ℝ n) (v : V),
    (B (ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ v) :
        Langlands.GeneralLinear n ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (B v : Langlands.GeneralLinear n ℝ → ℂ)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℝ) (v : V),
    (B (π (1 ⊗ₜ X) v) : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) X (B v : Langlands.GeneralLinear n ℝ → ℂ)

end Embedding

/-- Casselman's subrepresentation theorem for `GL_n(ℝ)` (Wallach 1979, Theorem 4.18; the
minimal parabolic subgroup is the upper triangular Borel subgroup, and the irreducible
representations of its Levi factor, the diagonal subgroup `(ℝ^×)ⁿ`, are lists of `n`
characters of `ℝ^×`): every irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` has a
nonzero intertwining map into the `O(n)`-finite functions of the standard module of some list
of `n` real characters, read as real blocks of rank one. No order condition is imposed. -/
def RealPrincipalSeriesSubrepresentationStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ cs : List RealCharacterData, cs.length = n ∧
        ∃ B : V →ₗ[ℂ] kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
            (unitaryCompact ℝ n),
          B ≠ 0 ∧ IsRealStandardEmbedding n ρ π (cs.map RealBlock.character) B

/-- The `O(n)`-finite contragredient of an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module
(the `K`-finite contragredient `Hom_ℂ(V, ℂ)_K` of Knapp–Vogan 1995, Chapter II, remark after
(2.42); for admissible `V` it is again irreducible and admissible, and `V` is its
`K`-finite dual): every irreducible admissible module `(ρ, π)` on `V` has an
irreducible admissible module `(ρ', π')` on some `W` and a bilinear pairing `P : W × V → ℂ`
that is `O(n)`-invariant, `P(ρ'(k) w, ρ(k) v) = P(w, v)`, and `𝔤`-invariant,
`P(π'(Y) w, v) + P(w, π(Y) v) = 0`, separates the points of `V`, and represents every
`O(n)`-finite linear functional on `W`, for the dual representation `ℓ ↦ ℓ ∘ ρ'(k)⁻¹`, as
`P(·, v)` for some `v ∈ V`. -/
def RealContragredientStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ (W : Type uV) (_ : AddCommGroup W) (_ : Module ℂ W)
        (ρ' : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W)
        (π' : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W),
        IsRealGKModule n ρ' π' ∧ IsIrreducibleGKModule ρ' π' ∧ IsAdmissibleGKModule ρ' ∧
        ∃ P : W →ₗ[ℂ] V →ₗ[ℂ] ℂ,
          (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (w : W) (v : V),
            P (ρ' k w) (ρ k v) = P w v) ∧
          (∀ (Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) (w : W) (v : V),
            P (π' Y w) v + P w (π Y v) = 0) ∧
          (∀ v : V, (∀ w : W, P w v = 0) → v = 0) ∧
          ∀ ℓ : Module.Dual ℂ W, FiniteVectors.IsFiniteVector (Representation.dual ρ') ℓ →
            ∃ v : V, ∀ w : W, ℓ w = P w v

/-- Duality of real principal series (the standard pairing `⟨f, h⟩ = ∫_{O(n)} f(k) h(k) dk` of
principal series induced from inverse characters): if the position characters of the lists of
real characters `cs` and `cs'` are pointwise inverse, there is a bilinear pairing `Q` of the
`O(n)`-finite functions of their principal series that is invariant under right translation by
`O(n)`, `Q(R(k) f, R(k) h) = Q(f, h)`, and under right derivatives,
`Q(R(X) f, h) + Q(f, R(X) h) = 0`, and nondegenerate in the second argument: for every `h ≠ 0`
some `f` has `Q(f, h) ≠ 0`. -/
def RealPrincipalSeriesDualityStatement : Prop :=
  ∀ (n : ℕ) (cs cs' : List RealCharacterData),
    (∀ (i : ℕ) (x : ℝˣ),
      realPositionCharacter (cs.map RealBlock.character) i x *
        realPositionCharacter (cs'.map RealBlock.character) i x = 1) →
      ∃ Q : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
            (unitaryCompact ℝ n) →ₗ[ℂ]
          kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
            (unitaryCompact ℝ n) →ₗ[ℂ] ℂ,
        (∀ (k : unitaryCompact ℝ n)
            (f : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
              (unitaryCompact ℝ n))
            (h : kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
              (unitaryCompact ℝ n))
            (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
                (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
              kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
                (unitaryCompact ℝ n))
            (hh : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
                (k : Langlands.GeneralLinear n ℝ) (h : Langlands.GeneralLinear n ℝ → ℂ) ∈
              kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
                (unitaryCompact ℝ n)),
          Q ⟨_, hf⟩ ⟨_, hh⟩ = Q f h) ∧
        (∀ (X : Matrix (Fin n) (Fin n) ℝ)
            (f : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
              (unitaryCompact ℝ n))
            (h : kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
              (unitaryCompact ℝ n))
            (hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
              kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
                (unitaryCompact ℝ n))
            (hh : rightDerivative (matrixModel ℝ n) X (h : Langlands.GeneralLinear n ℝ → ℂ) ∈
              kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
                (unitaryCompact ℝ n)),
          Q ⟨_, hf⟩ h + Q f ⟨_, hh⟩ = 0) ∧
        ∀ h : kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character))
            (unitaryCompact ℝ n),
          h ≠ 0 → ∃ f, Q f h ≠ 0

/-- The three statements above imply `RealPrincipalSeriesQuotientStatement`. -/
def RealPrincipalSeriesQuotientReductionStatement : Prop :=
  RealPrincipalSeriesSubrepresentationStatement.{uV} → RealContragredientStatement.{uV} →
    RealPrincipalSeriesDualityStatement → RealPrincipalSeriesQuotientStatement.{uV}

/-! ## Proof of the reduction -/

/-- The position characters of the list of inverse characters are the pointwise inverses. -/
theorem realPositionCharacter_map_inverse_mul :
    ∀ (cs : List RealCharacterData) (i : ℕ) (x : ℝˣ),
      realPositionCharacter ((cs.map RealCharacterData.inverse).map RealBlock.character) i x *
        realPositionCharacter (cs.map RealBlock.character) i x = 1
  | [], _, _ => by simp [realPositionCharacter]
  | c :: _, 0, x => by
      change (((c.character x)⁻¹ : ℂˣ) : ℂ) * (c.character x : ℂ) = 1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  | _ :: cs, p + 1, x => realPositionCharacter_map_inverse_mul cs p x

/-- Proof of the reduction. Let `W` be the contragredient of `V` with pairing `P` and embed
`W` into the principal series of `cs'` by `B`. With `cs` the list of inverse characters and
`Q` the duality pairing, the functional `w ↦ Q(f, B w)` is `O(n)`-finite for each
`O(n)`-finite `f`, so it is `P(·, A f)` for a unique `A f ∈ V`. The map `A` intertwines by
the invariance of `P`, `Q` and `B`, and it is nonzero because `B` is nonzero and `Q` is
nondegenerate in its second argument. -/
theorem realPrincipalSeriesQuotientReduction :
    RealPrincipalSeriesQuotientReductionStatement.{uV} := by
  intro hS1 hS2 hS3 n V _ _ ρ π hgk hirr hadm
  obtain ⟨W, _, _, ρ', π', hgk', hirr', hadm', P, hPK, hPg, hPnd, hPfin⟩ :=
    hS2 n V ρ π hgk hirr hadm
  obtain ⟨cs', hlen', B, hB0, hBK, hBX⟩ := hS1 n W ρ' π' hgk' hirr' hadm'
  set cs := cs'.map RealCharacterData.inverse with hcs
  obtain ⟨Q, hQK, hQX, hQnd⟩ := hS3 n cs cs' (realPositionCharacter_map_inverse_mul cs')
  -- The functionals `w ↦ Q(f, B w)`.
  set Λ := Q.compl₂ B with hΛ
  have hΛapp : ∀ f w, Λ f w = Q f (B w) := fun f w => rfl
  -- Invariance of `Λ` under `O(n)`.
  have hΛK : ∀ (k : unitaryCompact ℝ n)
      (f : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n))
      (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)) (w : W),
      Λ ⟨_, hf⟩ (ρ' ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ w) =
        Λ f w := by
    intro k f hf w
    have hh : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (B w : Langlands.GeneralLinear n ℝ → ℂ) ∈
          kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character)) (unitaryCompact ℝ n) := by
      rw [← hBK k w]
      exact (B _).2
    have e : B (ρ' ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ w) =
        ⟨_, hh⟩ := Subtype.ext (hBK k w)
    rw [hΛapp, hΛapp, e]
    exact hQK k f (B w) hf hh
  -- `Λ f` is `O(n)`-finite.
  have hfin : ∀ f, FiniteVectors.IsFiniteVector (Representation.dual ρ') (Λ f) := by
    intro f
    set S : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
      Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ n =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ)) with hS
    have hSfin : FiniteDimensional ℂ S := (mem_kFiniteVectors_iff _ _ _).mp f.2.2
    set S' := S.comap
      (kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)).subtype with hS'
    have hS'fin : FiniteDimensional ℂ S' := by
      refine Module.Finite.of_injective
        ((kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)).subtype.restrict
          (p := S') (q := S) fun x hx => hx) ?_
      intro x y hxy
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : S => (z : Langlands.GeneralLinear n ℝ → ℂ)) hxy))
    have hT : FiniteDimensional ℂ (S'.map Λ) := Module.Finite.map S' Λ
    refine Submodule.finiteDimensional_of_le (S₂ := S'.map Λ) ?_
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, rfl⟩
    set kc : unitaryCompact ℝ n := ⟨Unitary.toUnits u⁻¹, (u⁻¹).2⟩ with hkc
    have hu : (⟨((kc : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), kc.2⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) = u⁻¹ := Subtype.ext rfl
    have hg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        ((kc⁻¹ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)
          (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) :=
      rightTranslation_mem_kFiniteFunctions_realStandardModule n (cs.map RealBlock.character) f.2 (kc⁻¹).2
    set g : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) := ⟨_, hg⟩
      with hgdef
    have hRg : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (kc : Langlands.GeneralLinear n ℝ) (g : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) :=
      rightTranslation_mem_kFiniteFunctions_realStandardModule n (cs.map RealBlock.character) g.2 kc.2
    have hfg : (⟨_, hRg⟩ : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
        (unitaryCompact ℝ n)) = f := by
      apply Subtype.ext
      change Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (kc : Langlands.GeneralLinear n ℝ)
          (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
            ((kc⁻¹ : unitaryCompact ℝ n) : Langlands.GeneralLinear n ℝ)
            (f : Langlands.GeneralLinear n ℝ → ℂ)) = f
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, map_one, Module.End.one_apply]
    have key := hΛK kc g hRg
    rw [hfg, hu] at key
    refine ⟨g, ?_, ?_⟩
    · change (g : Langlands.GeneralLinear n ℝ → ℂ) ∈ S
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
  set A : kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n) →ₗ[ℂ] V :=
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
  refine ⟨cs, by rw [hcs, List.length_map, hlen'], A, ?_, ?_, ?_⟩
  · -- `A ≠ 0`.
    intro hA0
    obtain ⟨w, hw⟩ : ∃ w, B w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hB0 (LinearMap.ext hcon)
    obtain ⟨f, hf⟩ := hQnd (B w) hw
    apply hf
    rw [← hA, hA0, LinearMap.zero_apply, map_zero]
  · -- Equivariance for `O(n)`.
    intro k f
    refine ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n (cs.map RealBlock.character) f.2 k.2, ?_⟩
    apply hext
    intro w'
    set k' : Matrix.unitaryGroup (Fin n) ℝ :=
      ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ with hk'
    have hw : ρ' k' (ρ' k'⁻¹ w') = w' := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hw, hPK, hA, hA]
    exact hΛK k f _ (ρ' k'⁻¹ w')
  · -- Equivariance for `𝔤𝔩_n(ℝ)`.
    intro X f
    refine ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n (cs.map RealBlock.character) f.2 X, ?_⟩
    apply hext
    intro w
    have hh : rightDerivative (matrixModel ℝ n) X (B w : Langlands.GeneralLinear n ℝ → ℂ) ∈
        kFiniteFunctions (realStandardModule n (cs'.map RealBlock.character)) (unitaryCompact ℝ n) := by
      rw [← hBX X w]
      exact (B _).2
    have e : B (π' (1 ⊗ₜ X) w) = ⟨_, hh⟩ := Subtype.ext (hBX X w)
    have h1 := hPg (1 ⊗ₜ X) w (A f)
    have h2 := hQX X f (B w)
      (rightDerivative_mem_kFiniteFunctions_realStandardModule n (cs.map RealBlock.character) f.2 X) hh
    have h3 := hA f (π' (1 ⊗ₜ X) w)
    rw [e] at h3
    rw [hA]
    linear_combination h2 - h1 + h3

end Langlands.Archimedean
