# Root-valued evaluation of the intrinsic character on actual torsion points

This internal unit composes the actual dual-kernel character with the
relative integer-multiplication kernel comparison and Cartier evaluation.
Its output is an actual `μ_n`-valued function on the two torsion-point
sets, with a proved homomorphism law in the primal variable. Naturality
in the parameter scheme and additivity in the dual variable remain
separate obligations.

First, `GroupScheme.torsion_multiplication_eq_one` proves that multiplication
by an arbitrary integer `n` on `GroupScheme.torsion G n` is the constant
unit homomorphism. Postcomposition with the monomorphic torsion inclusion
reduces the assertion, by naturality of multiplication, to the defining
kernel square. Thus the annihilation proof used below is derived from the
actual torsion construction.

Let `A/S` be an abelian scheme with `S` quasi-separated. Retain
`hA : HasDualScheme A`, the seven existing dual-constructor propositions
(tensor-pullback preservation, composition, unit coherence, associativity,
left-unitor comparison, symmetry and Picard-zero stability), and the
actual inverse bundle `MA` with its tensor evaluation isomorphism.
Write `GA` for the existing `dualCommGroupSchemeFromEvaluation`.
For each natural number `n`, the primal group scheme is
`kernelCommGroupScheme (multiplication A (n : ℤ))`; its underlying group
scheme is the actual `A[n]`. The dual torsion scheme is the actual
`GroupScheme.torsion GA.toGrp (n : ℤ)`.

For every test scheme `T/S` and actual point `y : T → GA[n]`,
`dualTorsionCharacter` first applies the inverse of
`relativeDualMultiplicationKernelIso` to obtain a point of the actual
kernel of the dual of `[n]`. It then applies `dualKernelPointCharacter`.
This is the intrinsic character constructed from the Poincaré
representative, its proved trivial pullback, and the canonical kernel
translation action. The published relative additivity proof supplies
the equality between dual multiplication and multiplication on the
dual; no endpoint additivity assumption is supplied separately.

For `x : T → A[n]`, `finiteWeilValue n x y` is

```text
muEvaluation n (proved annihilation) (dualTorsionCharacter n y) x.
```

It is a morphism `T → μ_n`, where `μ_n` is the existing
scheme-theoretic kernel of `[n]` on the multiplicative group scheme.
`finiteWeilValue_incl` identifies its composite with the actual inclusion
`μ_n → Gm` as evaluation of the constructed beta character at `x`.
`finiteWeilValue_unique` proves that this inclusion equation uniquely
determines the result. These specialize the existing Cartier
evaluation and torsion-kernel universal-property lemmas.

The orientation is `e_n(x,y) = beta(y)(x)`: the dual character uses the
published transported-action divided by trivial-action convention.
This unit makes no inversion or replacement by an arbitrary character.
`finiteWeilValue_one_left`, `finiteWeilValue_mul_left` and
`finiteWeilValue_inv_left` specialize Cartier's corresponding laws.
`finiteWeilValueHom` packages the resulting homomorphism
`A[n](T) → μ_n(T)` for each fixed `y`.

The definitions and supporting equations are derived internally from the
imported constructions. The motivating convention is
Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary build
2012-02-08, XI §11.11, printed p.162 / PDF p.166, together with the
intrinsic beta construction of VII §§7.4–7.5, printed pp.99–100 /
PDF pp.103–104. Those passages treat abelian varieties over a field;
they are not used here to assert an unproved relative duality theorem.

This unit accepts no arbitrary pairing, character or duality isomorphism.
It requires no isogeny, finiteness, characteristic or invertibility
hypothesis for the displayed function and its first-variable laws;
`n = 0` is also allowed as a kernel construction. For positive `n` it
is the root-valued evaluation intended for the finite Weil pairing.
It does not yet assert that this family is natural in `T`, is a
morphism from the product of the two torsion schemes, or is bilinear
in both variables. Dual-variable additivity, Cartier duality,
perfectness, alternation, polarization, transition compatibility,
monodromy and inverse-limit pairings remain subsequent obligations.
