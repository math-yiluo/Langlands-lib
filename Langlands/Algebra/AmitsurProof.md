# Renard B.I: proof of Amitsur's theorem

`Langlands/Algebra/AmitsurProof.lean` proves the published aggregate proposition
`Langlands.Renard.AmitsurTheoremStatement.{u}` from
`Langlands.Algebra.AmitsurStatements`, together with each of its three component
assertions. The main theorem is

```lean
theorem Langlands.Renard.amitsurTheorem : AmitsurTheoremStatement.{u}
```

that is, for carriers in an arbitrary universe `u`:

- for every `A : Type u` with `[Ring A] [Algebra ℂ A] [Nontrivial A]`, both
  `AmitsurSpectrumNonemptyStatement A` and `AmitsurSpectrumSingletonZeroStatement A`;
- for every `D : Type u` with `[DivisionRing D] [Algebra ℂ D]`,
  `AmitsurDivisionAlgebraStatement D`.

The algebras are arbitrary associative unital complex algebras. They need not be
commutative, and no topology or finite dimension is assumed. Countable dimension is
`Module.rank ℂ A ≤ Cardinal.aleph0`. The spectrum is Mathlib's actual `spectrum ℂ a`,
and scalarity is bijectivity of the actual map `algebraMap ℂ D`. `Nontrivial A` is used
only in the two spectrum assertions, as in the statement. All theorems have the single
universe parameter `u`, and the axioms of `amitsurTheorem` are `propext`,
`Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`): B.I
"Théorème d'Amitsur", printed pages 271–272 / PDF pages 277–278. The second sentence
of the proof of the Lemme in B.III (printed page 273 / PDF page 279) uses the
one-sided consequence "il existe λ ∈ ℂ^× tel que *a* − λ1_*A* soit non inversible à
gauche". The 2010-edition *corrections et compléments*
(`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF pages 18–19)
have no entry for B.I. They are background only, and the 2026 text governs.

## How the proof differs from the printed order

The source first proves b). If Spec(*a*) is empty, the uncountable family of inverses
(*a* − λ1_*A*)⁻¹ is linearly dependent, which yields a nonconstant polynomial *P* with
*P*(*a*) = 0, and the linear factors of *P* contradict invertibility. It then shows
that nilpotent elements have spectrum {0} by the geometric series, and it proves the
converse by the same dependence argument applied to the family indexed by ℂ \ {0}.
Finally a) follows from b): in a division algebra a nonscalar element would have
empty spectrum.

The Lean proof does not repeat the dependence argument. It uses the stronger one-sided
result of the prerequisite task `dbbc9c86-3398-4450-9a39-761e2434a490`,

```lean
theorem Langlands.Renard.nonnilpotentLeftResolvent (A : Type u) [Ring A] [Algebra ℂ A] :
    NonnilpotentLeftResolventStatement A
```

from `Langlands.Algebra.NonnilpotentLeftResolventProof`. It says: in countable
dimension, a nonnilpotent `a` has some `z ≠ 0` such that `a - algebraMap ℂ A z` has no
left inverse. A shift with no left inverse is not invertible, so such a `z` is a
nonzero point of the spectrum. Hence every nonnilpotent element has a nonzero spectral
value. This one fact replaces both uses of the dependence argument in B.I. The
nilpotent case and the division-algebra deduction follow the source.

Mathlib's spectrum uses the shift `algebraMap ℂ A z - a`, while the source uses
*a* − λ1_*A*. The two differ by a sign, and the proof passes between them with
`neg_sub` and `IsUnit.neg`. The published comparison
`mem_spectrum_iff_not_isUnit_sub_smul_one` records the same convention check.

## Declarations

All declarations are theorems in namespace `Langlands.Renard`.

### `mem_spectrum_of_forall_mul_sub_ne_one`

```lean
theorem mem_spectrum_of_forall_mul_sub_ne_one {A : Type u} [Ring A] [Algebra ℂ A] {a : A}
    {z : ℂ} (hz : ∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1) : z ∈ spectrum ℂ a
```

If `a - z` has no left inverse, then `z ∈ spectrum ℂ a`. Suppose
`algebraMap ℂ A z - a` were a unit. Its negative `a - algebraMap ℂ A z` is then a unit
(`neg_sub`, `IsUnit.neg`), and the inverse of that unit is a left inverse
(`IsUnit.val_inv_mul`). This contradicts `hz`.

### `spectrum_eq_singleton_zero_of_isNilpotent`

```lean
theorem spectrum_eq_singleton_zero_of_isNilpotent {A : Type u} [Ring A] [Algebra ℂ A]
    [Nontrivial A] {a : A} (ha : IsNilpotent a) : spectrum ℂ a = ({0} : Set ℂ)
```

The nilpotent case of B.I. A nilpotent element of a nontrivial ring is not a unit
(`IsNilpotent.not_isUnit`), so `0` is in the spectrum (`spectrum.zero_mem_iff`). For
`z ≠ 0`, the shift `algebraMap ℂ A z - a = algebraMap ℂ A z + (-a)` is a unit: the
scalar `algebraMap ℂ A z` is a unit, `-a` is nilpotent and commutes with it
(`Algebra.commute_algebraMap_right`), and `IsNilpotent.isUnit_add_left_of_commute`
applies. That Mathlib lemma is proved through the finite geometric series, as in the
source's formula for (*a* − λ1_*A*)⁻¹.

### `amitsurSpectrumNonempty`

```lean
theorem amitsurSpectrumNonempty (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A] :
    AmitsurSpectrumNonemptyStatement A
```

B.I b), first assertion. Assume `Module.rank ℂ A ≤ ℵ₀` and let `a : A`. If `a` is
nilpotent, `0` is in its spectrum, as above. Otherwise `nonnilpotentLeftResolvent`
gives `z` such that `a - z` has no left inverse, and
`mem_spectrum_of_forall_mul_sub_ne_one` puts `z` in the spectrum. `Nontrivial A` is
needed only in the nilpotent case. In the zero algebra every element is nilpotent and
every spectrum is empty.

### `amitsurSpectrumSingletonZero`

```lean
theorem amitsurSpectrumSingletonZero (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A] :
    AmitsurSpectrumSingletonZeroStatement A
```

B.I b), second assertion. Assume `Module.rank ℂ A ≤ ℵ₀` and let `a : A`.

- If `spectrum ℂ a = {0}` and `a` is not nilpotent, `nonnilpotentLeftResolvent` gives
  `z ≠ 0` such that `a - z` has no left inverse. Then `z` is in the spectrum, so
  `z = 0`, a contradiction.
- If `a` is nilpotent, `spectrum_eq_singleton_zero_of_isNilpotent` applies.

### `amitsurDivisionAlgebra`

```lean
theorem amitsurDivisionAlgebra (D : Type u) [DivisionRing D] [Algebra ℂ D] :
    AmitsurDivisionAlgebraStatement D
```

B.I a). Assume `Module.rank ℂ D ≤ ℵ₀`. The map `algebraMap ℂ D` is injective because
it is a ring homomorphism from a field to a nontrivial ring (`RingHom.injective`). For
surjectivity, let `d : D`. A division ring is nontrivial, so
`amitsurSpectrumNonempty D` gives `z ∈ spectrum ℂ d`. Then `algebraMap ℂ D z - d` is
not a unit. In a division ring every nonzero element is a unit (`Ne.isUnit`), so
`algebraMap ℂ D z - d = 0`, that is, `algebraMap ℂ D z = d` (`sub_eq_zero`). This is
the source's argument that b) implies a).

### `amitsurDivisionAlgebraEquiv`

```lean
theorem amitsurDivisionAlgebraEquiv (D : Type u) [DivisionRing D] [Algebra ℂ D] :
    AmitsurDivisionAlgebraEquivStatement D
```

The algebra-isomorphism form of B.I a): in countable dimension there is
`e : ℂ ≃ₐ[ℂ] D` with `e z = algebraMap ℂ D z` for every `z`. It is obtained from
`amitsurDivisionAlgebra` by the published comparison
`amitsurDivisionAlgebraStatement_iff_equivStatement`. This records the correspondence
between the two formulations. The target of this module remains the bijectivity
statement inside `AmitsurTheoremStatement`.

### `amitsurTheorem`

```lean
theorem amitsurTheorem : AmitsurTheoremStatement.{u}
```

The aggregate: the anonymous-constructor pair of
`fun A _ _ _ => ⟨amitsurSpectrumNonempty A, amitsurSpectrumSingletonZero A⟩` and
`fun D _ _ => amitsurDivisionAlgebra D`.

## Scope

This module proves the unital B.I assertions only. It does not prove the B.II Schur
assertions, the B.III quotient and separation steps, or the source's reductions for
nonunital algebras. Those are separate obligations.

## Provenance and credit

Worker 972 wrote this module and this note. The route through the one-sided resolvent
follows the suggestion in the task context. The resolvent theorem itself was published
earlier by Worker 972 for task `dbbc9c86-3398-4450-9a39-761e2434a490`. No code was
taken from the division-algebra argument in
`Langlands.Representation.Schur.CountableDimensionProof`.

## Checks

In Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module compiles with no
errors or warnings. Inspection of `Langlands.Renard.amitsurTheorem` reports the level
parameter `u` and the axioms `propext`, `Classical.choice` and `Quot.sound`.
