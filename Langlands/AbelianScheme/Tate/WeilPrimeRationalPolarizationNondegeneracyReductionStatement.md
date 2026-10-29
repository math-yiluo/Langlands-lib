# Reduction of rational prime-adic polarization nondegeneracy to finite levels

`Langlands.AbelianScheme.PrimeRationalPolarizationWeilNondegeneracyReductionStatement`
is a proposition definition. It is the implication

```text
GeometricFiniteWeilNondegeneracyStatement.{u} →
  AlgClosedPointDivisibilityStatement.{u} →
    PrimeRationalPolarizationWeilNondegeneracyStatement.{u}
```

between three published proposition definitions, all in the same universe
`u`. The file proves nothing. It records the claim that the geometric-point
nondegeneracy of the rational prime-adic polarization Weil pairing follows from
two more basic statements. Neither hypothesis is asserted here.

## The three propositions

All three are imported unchanged.

- `GeometricFiniteWeilNondegeneracyStatement`, from
  `Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyStatement`.
  For every actual abelian scheme over a quasi-separated base, with its dual
  inputs and the ten quantified propositions, every algebraically closed point
  `s : Spec K ⟶ S` and every `n` with `(n : K) ≠ 0`, the existing finite Weil
  pairing `finiteWeilLevelBilinearMap ... n (Over.mk s)` has trivial left and
  right kernels on the actual `n`-torsion points of `A` and of the dual.
- `AlgClosedPointDivisibilityStatement`, from
  `Langlands.AbelianScheme.AlgClosedPointDivisibilityStatement`. For every
  abelian scheme `B` over a scheme `S`, every algebraically closed point
  `s : Spec K ⟶ S` and every `m` with `(m : K) ≠ 0`, each point
  `Over.mk s ⟶ B.X` is an `m`-th power in the group of points.
- `PrimeRationalPolarizationWeilNondegeneracyStatement`, from
  `Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyStatement`.
  For the same data, an actual polarization `lam : A ⟶ A^t`, an algebraically
  closed point `s` and a prime `p` with `(p : K) ≠ 0`, the existing pairing
  `primeRationalWeilAlongHomBilinearMap ... lam` on the rational prime-adic
  Tate module of `A` over `Over.mk s` is nondegenerate in Mathlib's sense:
  both radicals vanish.

Each hypothesis is a universally quantified proposition. The implication is
therefore between the global statements. It does not say that, for one fixed
abelian scheme, finite-level nondegeneracy implies the prime-adic statement for
that scheme alone. A proof may apply the hypotheses to any abelian scheme, in
particular to `A` and to the dual abelian scheme
`dualAbelianSchemeFromEvaluation`. The finite hypothesis does not assume
`0 < n` separately; `(n : K) ≠ 0` already excludes `n = 0`.

## Source correspondence and derived scope

The provenance is **derived**. Over a field, the classical argument is in
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft
built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Printed page numbers equal PDF page numbers minus 4.

- Chapter XI, Definition (11.11) and the discussion that follows, printed
  pp.162–163, PDF pp.166–167, define the finite pairing
  `e_n(x, y) = β(y)(x)` and note that it is perfect by construction.
- Chapter XI, (11.23), printed p.168, PDF p.172, assembles the pairings
  `e_{ℓ^m}` into a pairing `E : T_ℓ X × T_ℓ X^t → Z_ℓ(1)` and states that
  it is perfect. The polarization pairing is `E^λ(x, x') = E(x, T_ℓ λ(x'))`.
- Chapter X, Proposition (10.6) and Corollary (10.7), printed p.144,
  PDF p.148, show that an isogeny `f` induces an isomorphism
  `V_ℓ f : V_ℓ X → V_ℓ Y` for `ℓ ≠ char(k)`.

These sources yield the following argument, which is why the hypotheses imply
the conclusion. Apply the finite hypothesis with `n = p^k`, where
`(p^k : K) ≠ 0`. Apply the divisibility hypothesis with `m = p` to `A` and to
its dual. Then every transition `A[p^(k+1)](s) → A[p^k](s)` is surjective, so
each coordinate projection of the Tate module is surjective. Hence the
integral prime-adic pairing between the Tate modules of `A` and of its dual has
trivial kernels. The polarization is an isogeny. On points over `s` it is
surjective with finite kernel, so its Tate map is injective and its image
contains `N` times every element for some positive `N`. The integral twist has
no `p`-torsion, so the pairing pulled back along `lam` has trivial kernels.
Its rationalization over `Q_p` then has trivial kernels.

The sources treat abelian varieties over a field. The Lean propositions
concern the relative constructors evaluated at a geometric point of a general
base. In that setting, the comparison of the relative pairing at `s` with the
field pairing is part of the finite hypothesis, not of this reduction. The
reduction needs no comparison with the fibre. All of its steps take place in
the groups of points `Over.mk s ⟶ A.X` and `Over.mk s ⟶ A^t.X`. The deduction
above is a proof obligation for a separate theorem and is not made in this
file.

## Formal status

The declaration is a `Prop`-valued `def`, not a theorem and not an assumption.
It adds no axiom. It proves neither hypothesis and does not prove the
prime-adic nondegeneracy target.
