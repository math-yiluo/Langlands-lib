# The actual opposite-radical height cutoff

This module proves the geometric tail inclusion used in the proof of
Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, Proposition VIII.3.1, printed p.325.
The original is registered as `waldspurger-2003-plancherel`,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The source defines a tail by
`delta*(1 + sigma(a)) <= 1 + sigma(u)` and proves that the
opposite radical outside `a*GammaBar*a^-1` lies in it. The Lean
constant is named `b`.

`RationalOppositeTailHeightCutoffStatement` quantifies over an
arbitrary nonarchimedean local field in universe `u`, an affine
locally finite type connected reductive group, its actual maximal
split torus `i` and generic cocharacter `nu`, a simple root `alpha`,
and any standard cocharacter `zeta` for the maximal face
`Delta \ {alpha}`. It also quantifies over an arbitrary nonempty
finite closed matrix realization `rho`, a compact open subgroup
`K` with the minimal Iwasawa factorization, and any compact open
`GammaBar` in the actual opposite radical of `zeta`.

It proves that there is `b > 0` such that, for every `a` in
`rationalMinimalRootSector i nu alpha` and every actual opposite
radical point `u` outside the conjugated subgroup
`a*GammaBar*a^-1`,

```text
b * (1 + rationalHeight rho a) <= 1 + rationalHeight rho u.
```

The sector is the part of the full actual chamber
in the common norm kernel where `alpha` has largest simple-root
order. There is no common-uniformizer section restriction. The
conjugated subgroup is expressed by the ordinary subgroup map
under `MulAut.conj a`, after including `GammaBar` in `G(F)`.
The theorem `rationalOppositeTailHeightCutoff` has exactly the
closed Prop as its type.

The proof uses the one-sided II.3.5 estimate directly. If `V` is
the opposite radical and `P` the parabolic, then
`V ∩ (GammaBar*P) = GammaBar`: for `x=v*p` in `V`, with
`v ∈ GammaBar`, the parabolic factor `p=v^-1*x` also lies in `V`.
The proved dynamic intersection `V ∩ P = {1}` gives `p=1`.
This is `mem_mapped_opposite_open_of_mem_mul`. Thus, if
`x=a^-1*u*a` is outside `GammaBar`, the one-sided estimate gives

```text
C6 * order_alpha(a) < 1 + sigma(x) + sigma(u).
```

Torus centralizer normalization keeps `x` in the opposite radical.
Membership of `u` outside the mapped conjugate subgroup is exactly
nonmembership of `x` in `GammaBar`. The source obtains the same
height consequence from the complement of the full truncated cell;
the implemented proof uses the already sufficient one-sided
inclusion.

`oppositeUnipotent_le_oppositeMinimalParabolic` proves the actual
subgroup containment needed for the next estimate. Negating the
standard cocharacter expresses the chosen opposite radical as a
standard radical in the reversed root system. Contravariance of
standard radicals puts it inside the reversed minimal radical,
and hence inside the reversed minimal parabolic. The proved
actual inverse-conjugation bound from II.3.3 then gives one
`C8 >= 1` with

```text
1 + sigma(a^-1*u*a) <= C8 * (1 + sigma(u)).
```

Combining the two inequalities bounds `order_alpha(a)` by
`(C8+1)/C6 * (1+sigma(u))`. The sector-height comparison
supplies `H > 0` with
`1+sigma(a) <= H*(1+order_alpha(a))`. Since matrix height is
nonnegative, one may take

```text
b = 1 / (H * (1 + (C8 + 1)/C6)).
```

Every constant is uniform in the chamber and radical points. The
proof retains the original matrix height and does not assume an
adapted realization, a height cutoff, an analytic decay estimate,
or a special choice of the Xi-defining compact. Both local-field
characteristics and nonsplit connected reductive groups are
included. The tail cutoff is a geometric prerequisite; no tail
integral estimate or closed VIII.3.1 theorem is claimed here.
