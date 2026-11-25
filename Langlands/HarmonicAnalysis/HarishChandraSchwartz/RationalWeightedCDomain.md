# The two densities on the weighted c-family's domain

`Langlands.HarishChandraSchwartz.WeakExpansion.WeightedCScalarPresentationStatement`
is an exact description of the *scalar* in `cWeightedCompactFamily` and of
its allowed parameter set. `weightedCScalarPresentation` proves it for the
published `cDomain`, `cWeightedDomain`, and the two actual density packages.
No density is replaced by a surrogate and no weight-normalization identity
between the packages is assumed.

For a fixed lift and its Levi inclusion, write `D` for `cDomain`, `D₀` for
`cWeightedDomain`, and `X` for `X(M_I(F))`. There are regular functions `a,b`
on `X` satisfying all of the following:

- `b ≠ 0` as a function if and only if the lower package's canonical scalar
  `j_P` is nonzero as a rational function. This does not assert nonvanishing
  of the scalar at every parameter.
- `D₀ = D ∩ {z | b(z) ≠ 0}`. The nonvanishing test is exact even if `b = 0`.
- At every point of `D₀`, the scalar `µ^G(z) µ^{M′}(sz)⁻¹` used in the actual
  weighted compact family equals `a(z)/b(z)`.

In the same module `cWeightedDomain_interior_nonempty_iff` shows that the
interior of `D₀` is nonempty exactly when the interior of `D` is nonempty
and that lower canonical scalar is not identically zero. Thus the two
regular-value requirements do not impose a further nonempty-interior
condition once those two inputs hold. Neither input is proved here.

## Implemented proof

First `exists_fraction_on_regular_locus` uses
`rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid` and
Mathlib's reduced numerator and denominator of a fraction. If `m/n`
represents the same function as the reduced `p/q`, cross-multiplication in
the regular ring gives `p n = m q`. Relative primality implies `q ∣ n`.
Consequently, a representation with `n(z) ≠ 0` can exist only if `q(z) ≠ 0`.
The reduced presentation itself supplies a witness in the other direction.
`rationalValueAt_eq` identifies the value with `p(z)/q(z)` wherever this
denominator does not vanish. This works on the entire complex character
torus, not just on unitary characters.

Apply this to each density on its actual centralizer scheme. Transport the
regular coefficients first through `standardLeviParameterIso` for the upper
package and `lowerParameterIso` for the lower package, then through the
literal Levi homeomorphism. `lowerDensityParameter_eq` checks that this
second pullback uses exactly the `z ↦ sz` parameter in `cWeightedDomain`:
`leviRationalPointHomeomorph_lowerParameterIso` gives the character equality
on every point of the lower parameter group. The upper parameter is the
specified restriction by definition.

Let `A_G/B_G` and `A_M/B_M` denote the transported reduced fractions. The
upper density must be regular, and the lower density must be regular with
nonzero value. These are the three tests `B_G(z) ≠ 0`, `B_M(z) ≠ 0`, and
`A_M(z) ≠ 0`. Use

```
a = A_G * B_M * B_M
b = B_G * B_M * A_M
```

(up to association). Here `b` is intentionally not reduced: keeping the
factor `B_M` records the requirement that the lower density itself be
regular, even where the reduced quotient of the two densities might already
be defined. Field arithmetic on this exact locus gives the displayed ratio.
The regular-function rings are domains, and the two reduced denominators
are nonzero in those rings. Thus `b ≠ 0` exactly when `A_M ≠ 0`, which is
equivalent to the lower density being nonzero in the function field. The
lower ambient group is connected reductive, and its chosen torus is split;
`rankOneGammaProduct_ne_top_of_isSplitTorus` and
`plancherelDensity_eq_zero_iff` identify this with nonvanishing of the
lower package's canonical scalar.

For the interior result, if `b ≠ 0`, its nonzero locus is open by regular
function continuity and dense by `rationalUnramifiedRegular_dense_nonzero`,
transported to the literal Levi. Intersect it with the nonempty open
interior of `D`. In the converse direction, a point of the interior of
`D₀` witnesses that `b` is nonzero, and `D₀ ⊆ D` gives the inclusion of
interiors.

## Source and limits

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, V.2 and
Lemma V.2.1, printed p.292 (PDF p.58), define `µ = j⁻¹ ∏ γ²` and state its
rational regularity on the unitary orbit. Corollary V.2.3, printed p.294
(PDF p.60), uses the operator weighted by `µ^G(ω) µ^{M′}(sω)⁻¹`. Registered
source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The principal-open description and the nonempty-interior criterion are
derived for the Library's domain, not stated in the article. They are an
algebraic step toward continuing the weighted operator from its original
convergence domain. This module does not prove joint convergence, nonzero
lower canonical scalar, pole support of the ratio, or any of the three
exact targets on regularity, the weak expansion and the packet identity
stated in `RationalWeakExpansionTargets`. The original field and representation-carrier
universes, measures implicit in the packages, and normalization-dependent
operator are unchanged.
