/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.Mathlib.Algebra.Group.AddChar
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Additive characters induced along the trace and nontrivial additive characters

Let `L / K` be a finite separable field extension and `ψ` an additive character of `K`. The
*induced character* `ψ_L = ψ ∘ Tr_{L/K}` is an additive character of `L`, nontrivial if `ψ` is,
hence primitive. For a finite field `k₀ = 𝔽_q` of characteristic `p` and a nontrivial character
`Ψ` of `𝔽_p` this gives *the* nondegenerate additive character `ψ = Ψ ∘ Tr_{k₀/𝔽_p}` of `k₀`,
and over `𝔽_{qⁿ}` the character `ψₙ = ψ ∘ Tr_{𝔽_{qⁿ}/k₀} = Ψ ∘ Tr_{𝔽_{qⁿ}/𝔽_p}`.

The sums of these characters are the orthogonality relations: a nontrivial additive character
sums to zero over a finite group, and `∑_{y ∈ L} ψ_L((x - x') y)` is `#L` if `x = x'` and zero
otherwise.

## Main definitions

- `AddChar.compTrace`: the induced character `ψ ∘ Tr_{L/K}`.

## Main statements

- `AddChar.compTrace_ne_one` and `AddChar.isPrimitive_compTrace`: the induced character of a
  nontrivial character is nontrivial, hence primitive.
- `AddChar.compTrace_compTrace`: transitivity, `(ψ_L)_M = ψ_M`.
- `AddChar.sum_const_mul_eq_ite`: orthogonality of an additive character.
- `AddChar.sum_compTrace_sub_mul`: additive orthogonality over `L`.
- `AddChar.exists_ne_one_of_isAlgClosed`: a finite field `F` has a nontrivial additive
  character with values in any algebraically closed field `K` whose characteristic differs
  from that of `F`: the primitive character `AddChar.FiniteField.primitiveChar`, with values in
  a cyclotomic extension of `K`, followed by a `K`-embedding of that extension into `K`.
-/

@[expose] public section

namespace AddChar

variable {K L M R : Type*} [Field K] [Field L] [Field M] [CommRing R]

section CompTrace

variable [Algebra K L] [Algebra L M] [Algebra K M]

variable (L) in
/-- The additive character `ψ_L = ψ ∘ Tr_{L/K}` of `L` induced by an additive character `ψ`
of `K`. For a finite field `k₀` of characteristic `p` and a nontrivial character `Ψ` of `𝔽_p`,
`Ψ.compTrace k₀` is *the* nondegenerate additive character `ψ = Ψ ∘ Tr_{k₀/𝔽_p}` of `k₀`, and
over `𝔽_{qⁿ}` the character `ψₙ = ψ ∘ Tr_{𝔽_{qⁿ}/k₀}` is `ψ.compTrace 𝔽_{qⁿ}`.
(blueprint: `theorem-weight-bound-affine-line--1`; sketch blueprint:
`theorem-weight-bound-affine-line--1`) -/
noncomputable def compTrace (ψ : AddChar K R) : AddChar L R :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

@[simp]
lemma compTrace_apply (ψ : AddChar K R) (x : L) :
    ψ.compTrace L x = ψ (Algebra.trace K L x) :=
  rfl

/-- The induced character of a nontrivial character along a finite separable extension is
nontrivial: the trace is surjective. (sketch blueprint: `theorem-weight-bound-affine-line--1`) -/
theorem compTrace_ne_one [FiniteDimensional K L] [Algebra.IsSeparable K L] {ψ : AddChar K R}
    (hψ : ψ ≠ 1) : ψ.compTrace L ≠ 1 := by
  obtain ⟨a, ha⟩ := ne_one_iff.mp hψ
  obtain ⟨x, rfl⟩ := Algebra.trace_surjective K L a
  exact ne_one_iff.mpr ⟨x, ha⟩

/-- **The nondegenerate additive character is primitive**: for a nontrivial character `ψ` of
`K` and a finite separable extension `L / K`, every scaling `x ↦ ψ_L(a x)`, `a ∈ Lˣ`, of the
induced character is again nontrivial.
(blueprint: `theorem-weight-bound-affine-line--1`; sketch blueprint:
`theorem-weight-bound-affine-line--1`) -/
theorem isPrimitive_compTrace [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ψ : AddChar K R} (hψ : ψ ≠ 1) : (ψ.compTrace L).IsPrimitive :=
  IsPrimitive.of_ne_one (compTrace_ne_one hψ)

/-- Transitivity of induced characters: for a tower `M / L / K` of finite extensions,
`(ψ_L)_M = ψ_M`, i.e. `ψ(Tr_{L/K}(Tr_{M/L}(x))) = ψ(Tr_{M/K}(x))`. In particular
`ψₙ = ψ ∘ Tr_{𝔽_{qⁿ}/k₀} = Ψ ∘ Tr_{𝔽_{qⁿ}/𝔽_p}`.
(blueprint: `theorem-weight-bound-affine-line--1`; sketch blueprint:
`theorem-weight-bound-affine-line--1`) -/
theorem compTrace_compTrace [IsScalarTower K L M] [Module.Free K L] [Module.Finite K L]
    [Module.Free L M] [Module.Finite L M] (ψ : AddChar K R) :
    (ψ.compTrace L).compTrace M = ψ.compTrace M := by
  ext x
  simp [Algebra.trace_trace]


end CompTrace

section Orthogonality

/-- **Orthogonality of an additive character.** For an additive character `ψ` of a finite
group `A` with values in a domain and `c ∈ R`,
`∑_{x ∈ A} c ψ(x) = c · #A` if `ψ = 1` and `0` otherwise. Applied to `ψ_a = ψ(a ·)` on
`k₀ = 𝔽_q` this is `∑_x c ψ_a(x) = c q` or `0`.
(blueprint: `corollary-plancherel--1`; sketch blueprint: `corollary-plancherel--1`) -/
theorem sum_const_mul_eq_ite {A : Type*} [AddGroup A] [Fintype A] [IsDomain R]
    (ψ : AddChar A R) (c : R) [Decidable (ψ = 1)] :
    ∑ x, c * ψ x = if ψ = 1 then c * Fintype.card A else 0 := by
  rw [← Finset.mul_sum]
  split_ifs with h
  · rw [sum_eq_card_of_eq_one h]
  · rw [sum_eq_zero_of_ne_one h, mul_zero]


/-- **Additive orthogonality over `L`.** For a nontrivial additive character `ψ` of `K`, a
finite separable extension `L / K` with `L` finite and the induced character
`ψ_L = ψ ∘ Tr_{L/K}`,
`∑_{y ∈ L} ψ_L((x - x') y) = #L` if `x = x'` and `0` otherwise. For `L = 𝔽_{qⁿ}` over
`K = k₀` this is `∑_y ψₙ((x - x') y) = qⁿ δ_{x, x'}`.
(blueprint: `corollary-plancherel--1`; sketch blueprint: `corollary-plancherel--1`) -/
theorem sum_compTrace_sub_mul [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Fintype L] [DecidableEq L] [IsDomain R] {ψ : AddChar K R} (hψ : ψ ≠ 1) (x x' : L) :
    ∑ y : L, ψ.compTrace L ((x - x') * y) = if x = x' then (Fintype.card L : R) else 0 := by
  simp_rw [mul_comm (x - x')]
  rw [sum_mulShift _ (isPrimitive_compTrace hψ)]
  simp [sub_eq_zero]

end Orthogonality

/-- A finite field `F` has a nontrivial additive character with values in an algebraically
closed field `K` of characteristic different from that of `F`. -/
theorem exists_ne_one_of_isAlgClosed (F K : Type*) [Field F] [Finite F] [Field K]
    [IsAlgClosed K] (h : ringChar K ≠ ringChar F) : ∃ ψ : AddChar F K, ψ ≠ 1 := by
  let ψ := FiniteField.primitiveChar F K h
  have : Algebra.IsAlgebraic K (CyclotomicField ψ.n K) :=
    inferInstanceAs (Algebra.IsAlgebraic K (Polynomial.cyclotomic ψ.n K).SplittingField)
  let φ : CyclotomicField ψ.n K →ₐ[K] K := IsAlgClosed.lift
  refine ⟨(φ : CyclotomicField ψ.n K →* K).compAddChar ψ.char, fun h1 ↦ ?_⟩
  refine ψ.prim one_ne_zero ?_
  ext a
  apply φ.injective
  have := DFunLike.congr_fun h1 a
  simpa [mulShift_apply] using this


section Dedekind

/-- Every additive character of a finite field `F` with values in a field is a multiplicative
shift `x ↦ ψ (a x)` of a given primitive character `ψ`. -/
theorem exists_mulShift_eq_of_isPrimitive {F : Type*} [Field F] [Finite F] {ψ : AddChar F K}
    (hψ : ψ.IsPrimitive) (φ : AddChar F K) : ∃ a : F, ψ.mulShift a = φ :=
  ((to_mulShift_inj_of_isPrimitive hψ).bijective_of_nat_card_le natCard_le).2 φ

end Dedekind

end AddChar
