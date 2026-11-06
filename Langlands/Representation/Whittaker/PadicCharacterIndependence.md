# Independence of p-adic Whittaker genericity from the additive character

Worker 1582 constructs character independence of the actual standard Whittaker
functional spaces over every supplied `PadicField.TopologicalData T`. The field
universe `uF` and representation-carrier universe `uV` are independent. The rank
is `n + 1`, including rank one. The representation `ρ` and its carrier `V` are
unchanged throughout.

This is an internal derived construction. Its mathematical inputs are the
published `PadicAdditiveCharacterSelfDuality`, `CharacterChange`, and
`Group.GL.Padic` modules. It combines their proved results and introduces no
additional mathematical premise beyond those explicitly present in each
construction or theorem. It does not assert that every irreducible admissible
representation is generic or construct the initial functional for a cuspidal
local component.

## Characters and continuity

`HarmonicAnalysis.isLocallyConstant_addChar_of_open_subgroup` applies to an
additive character with values in any monoid. If it is trivial on an open
additive subgroup `H`, it is constant on every translate of `H`. The implemented
proof uses the open neighborhood `{y | y - x ∈ H}` of `x` and the equality
`χ(y) = χ(y - x) χ(x) = χ(x)`.

For a continuous nontrivial unitary additive character of the supplied p-adic
field, `T.exists_additiveTrivialAt` gives a valuation lattice on which it is
trivial, and `T.isOpen_additiveLattice` proves this lattice open. This yields
`T.isLocallyConstant_unitaryAdditiveCharacter`. Conversely,
`T.unitaryAdditiveCharacterOfTrivialOnIntegers` bundles a raw circle-valued
additive character `χ ≠ 1` which is trivial on `T.Integers`. Its continuity is
proved by applying the same argument to the level-zero additive lattice,
which is exactly the integer ring. The `_apply` lemma records that the bundled
character has precisely the original values.

`T.exists_unit_scale_eq ψ χ` proves `ψ.scale a = χ` for some `a : F.Carrierˣ`.
The complex-valued character underlying `χ` is locally constant by the result
above. The published self-duality theorem expresses it as `ψ(a x)` for a field
scalar `a`. If `a = 0`, the character would be constantly one, contradicting
`χ.nontrivial`. The proof therefore uses `Units.mk0 a` and circle extensionality
to recover equality of the original bundled characters. All topological
certificates are those of the supplied `T`.

## Functional spaces and genericity

`T.whittakerCharacterEquiv ρ ψ χ` chooses the scalar above and transports the
published `Whittaker.characterChangeFunctionalEquiv` along the proved character
equality. It is a complex linear equivalence

```
Whittaker.glFunctionals ψ n ρ ≃ₗ[ℂ] Whittaker.glFunctionals χ n ρ.
```

The imported equivalence translates a functional by the action of
`diag(a^n, ..., a, 1)`. Thus it uses exactly the positive standard character,
the character of the sum of first-superdiagonal entries. The action and the
representation carrier remain `ρ` and `V`; no representation equivalence or
replacement carrier is required.

`T.hasFunctional_iff_character` uses this equivalence and its inverse to
preserve nonzero functionals. Nonzeroness is the nonzeroness of the underlying
algebraic dual element, as in the Library's `HasFunctional` definition.
`T.isGeneric_iff_character` retains the same irreducibility and admissibility
conjuncts and applies this equivalence to the existence conjunct. Admissibility
and genericity use exactly `T.generalLinearTopology (n + 1)`.

Finally, `T.isGeneric_of_functional_trivialOnIntegers` accepts a raw
circle-valued character, its nontriviality and integer-triviality, and an actual
nonzero complex-linear functional satisfying

```
ℓ (ρ(u) x) = χ(Σ i, u[i,i+1]) · ℓ(x).
```

Together with irreducibility and admissibility of `ρ`, these data imply
`Whittaker.IsGeneric ψ n ρ` for every supplied continuous nontrivial `ψ`. The
proof bundles the raw character with the proved continuity, regards `ℓ` as a
standard functional for it, and applies character independence. This is a
conditional transport lemma: global cuspidal Whittaker existence remains a
separate input to the full cuspidal local genericity target.
