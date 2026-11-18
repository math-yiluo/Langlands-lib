# Nilpotent elements and degenerate cosets (KP Definition 13.6.5)

Author: Worker 3557.

This module belongs to the Kaletha–Prasad Bruhat–Tits program (task
`f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`). It formalizes KP Definition 13.6.5:
nilpotent elements of `𝔤` and of `𝔤*` in the sense of 1-parameter subgroups,
and degenerate cosets. These notions are the input of KP Propositions 13.6.7
and 13.7.4. The module has six definitions and no theorems.

## Setting

`k` is a field and `G` a group scheme over `Spec k` with
`[IsAffineHom G.X.hom]`. Its Lie algebra `𝔤 = Lie(G)` is the Library's
`Additive (lieKernel G k)`. A 1-parameter subgroup of `G` defined over `k` is
a homomorphism of group schemes over `Spec k`

```
ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G
```

For `n : ℤ`, `Gm.powerHom _ n` is the character `t ↦ tⁿ` of `𝔾_m`, and the
Library's `weightSpace ν χ` is the weight space of `χ` for `Ad ∘ ν`: the `X`
with `Ad(ν(t)) X = χ(t) X` for all points `t` of `𝔾_m` over all `k`-algebras.

The Moy–Prasad lattices (`Langlands.Geometry.Building.KPLieFiltration`) are
submodules of `GenericLie 𝒪[F] G`, a type synonym of `𝔤` that also carries
an `𝒪[F]`-module structure. The definitions below therefore take elements of
`GenericLie R G` for any `R` with `[Algebra R k]`, and pass to `𝔤` through
the identity equivalence `GenericLie.equiv R G`. The ring `R` only selects the
type synonym. With `R = k` the definitions concern `𝔤` itself.

## The definitions

### `cocharacterPositiveLie ν` and `cocharacterNonnegativeLie ν`

```
cocharacterPositiveLie ν    = RelativeRoot.positiveWeightSpan ν (𝟙 _)
cocharacterNonnegativeLie ν = nonnegativeWeightSpan ν (𝟙 _)
```

These are the `k`-subspaces `𝔤_{>0}(ν)` and `𝔤_{≥0}(ν)` of `𝔤`: the sums of
the weight spaces of `Ad ∘ ν` with weight `n ≥ 1`, respectively `n ≥ 0`.
They are specializations of published weight spans, with the torus `𝔾_m`
mapped to `G` by `ν`:

- `RelativeRoot.positiveWeightSpan i a`
  (`Langlands.GroupScheme.Rational.RootSubgroupStructureStatement`) is the
  sum of the weight spaces `weightSpace i (n • a)` for `n > 0`. With
  `i = ν` and `a = 𝟙 _`, the identity character `t ↦ t` of `𝔾_m`, the
  characters `n • a` are `t ↦ tⁿ`, `n ≥ 1`.
- `nonnegativeWeightSpan j μ`
  (`Langlands.GroupScheme.Absolute.RegularCocharacterWeights`) is the sum of
  the weight spaces `weightSpace j χ` over the characters `χ` with
  `⟨χ, μ⟩ ≥ 0`. With `j = ν` and `μ = 𝟙 _`, the identity cocharacter of
  `𝔾_m`, the character `t ↦ tⁿ` has pairing `n`, so the sum runs over
  `n ≥ 0`.

### `IsCocharacterNilpotent X`

For `X : GenericLie R G`: there is a 1-parameter subgroup `ν` with
`GenericLie.equiv R G X ∈ cocharacterPositiveLie ν`.

### `IsCocharacterNilpotentDual X`

For a `k`-linear form `X : Module.Dual k (GenericLie R G)`: there is a
1-parameter subgroup `ν` such that `X Y = 0` for every `Y` with
`GenericLie.equiv R G Y ∈ cocharacterNonnegativeLie ν`.

### `IsDegenerateLieCoset M X` and `IsDegenerateDualCoset M X`

For an `R`-submodule `M` of `GenericLie R G` and `X : GenericLie R G`, the
coset `X + M` is degenerate if some `Y` with `IsCocharacterNilpotent Y`
satisfies `Y - X ∈ M`. The dual version is the same for an `R`-submodule `M`
of `Module.Dual k (GenericLie R G)`, with `IsCocharacterNilpotentDual`.

KP's cosets are `Ξ = X + 𝔤_{x,r+}` with `X ∈ 𝔤_{x,r}`, and
`X + 𝔤*_{x,r+}` with `X ∈ 𝔤*_{x,r}`. The published Library interface
(`Langlands.Geometry.Building.KPLieFiltration`) provides, for supplied
`L : P.LieFiltrationData` and a nonnegative depth `r : NNReal`, the lattices
`L.lieFiltration x r` and `L.lieFiltrationPlus x r`. For such a depth KP's
coset is `IsDegenerateLieCoset (L.lieFiltrationPlus x r) X` with
`X ∈ L.lieFiltration x r`. The Library has no Moy–Prasad lattices at negative
real depths and no dual lattices `𝔤*_{x,r}`. Applications to those cases pass
the denominator as a supplied submodule `M`; the definitions accept any
submodule. The definitions do not require `X ∈ 𝔤_{x,r}`. Statements about
cosets of `𝔤_{x,r}/𝔤_{x,r+}` assume it separately.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. Printed page numbers are the
PDF page numbers minus 31.

- Definition 13.6.5, printed p. 480, PDF p. 511: "We say that an element X
  of 𝔤 or 𝔤* is nilpotent if there is a 1-parameter subgroup λ: G_m → G
  defined over k such that lim_{t→0} λ(t)X = 0. Let x be a point of B(G).
  We say that a coset Ξ in 𝔤_{x,r}/𝔤_{x,r+} or 𝔤*_{x,r}/𝔤*_{x,r+} is
  degenerate if it contains a nilpotent element."
- The authors' corrections of 1 November 2024
  (`kaletha-prasad-2024-corrections`), PDF p. 49: the only entry in §13.6
  replaces the reference 1.3.35 at the end of 13.6.2 by 8.4.8(3). Definition
  13.6.5 is unchanged.

## Derived formulation

**Limits as weight conditions.** KP write `lim_{t→0} λ(t)X = 0`: the orbit
map `t ↦ λ(t)X` from `𝔾_m` to the affine space of `𝔤` extends to `𝔸¹` with
value `0` at `t = 0`. The split torus `𝔾_m` acts on the finite-dimensional
space `𝔤` through `Ad ∘ λ`, so `𝔤` is the direct sum of its weight spaces
`𝔤_n(λ)`, `n ∈ ℤ`. Write `X = Σ X_n` accordingly. Then `Ad(λ(t)) X = Σ tⁿ X_n`.
This extends to `𝔸¹` exactly when `X_n = 0` for `n < 0`, and its value at
`0` is `X_0`. So the limit exists and is `0` exactly when
`X ∈ 𝔤_{>0}(λ)`, which is `IsCocharacterNilpotent`.

For `X ∈ 𝔤*` with the coadjoint action
`(g · X)(Y) = X(Ad(g)⁻¹ Y)`, one gets `(λ(t) · X)(Y) = t⁻ⁿ X(Y)` for
`Y ∈ 𝔤_n(λ)`. The limit at `0` exists and is `0` exactly when `X` vanishes on
`𝔤_n(λ)` for every `n ≥ 0`, that is, on `𝔤_{≥0}(λ)`. This is
`IsCocharacterNilpotentDual`. Both reformulations use the weight
decomposition of a `𝔾_m`-representation. The module does not prove it; it
enters only the comparison with KP's wording, not the definitions.

**Cosets.** KP's coset `Ξ` lives in a quotient `𝔤_{x,r}/𝔤_{x,r+}`. Here a coset
is given by a representative `X` and the submodule `M`, and "contains a
nilpotent element" becomes `∃ Y, IsCocharacterNilpotent Y ∧ Y - X ∈ M`. This
does not depend on the representative.

**Base and generality.** KP's `k` is the field of Chapter 13 and `G` is
connected reductive. The definitions only need a field and an affine group
scheme, so they are stated in that generality. Statements that use them add
KP's hypotheses.

## Not included

- Remark 13.6.6 (comparison with nilpotence in the sense of the Jordan
  decomposition and with nilradicals of parabolic subalgebras).
- The sets `N` and `N'` of §13.7 and the depth of an element (§13.7).
- Instability of a coset under `G_x` (Proposition 13.6.7, 13.7.4(2)).
  KP's instability says that `0` lies in the Zariski closure of an orbit.
  The Library has orbits and orbit closures for scheme actions
  (`SchemeAction.orbit` in `Langlands.GroupScheme.SchemeActionOrbit`,
  `SchemeAction.exists_reduced_orbitClosure` in
  `Langlands.GroupScheme.SchemeActionReducedClosed`). What is missing is
  the algebraic action of the maximal reductive quotient of the special
  fiber of `G_x` on the Moy–Prasad graded pieces `𝔤_{x,r}/𝔤_{x,r+}`
  (KP 13.3.4) as a scheme action.

## Provenance

Derived from KP Definition 13.6.5. The limit conditions are replaced by the
equivalent weight-space conditions explained above. The names
`cocharacterPositiveLie`, `cocharacterNonnegativeLie`,
`IsCocharacterNilpotent`, `IsCocharacterNilpotentDual`,
`IsDegenerateLieCoset` and `IsDegenerateDualCoset` are internal. The module
uses the published `RelativeRoot.positiveWeightSpan`,
`nonnegativeWeightSpan` and `Gm` (see above) and `GenericLie`
(`Langlands.GroupScheme.IntegralModel.LieLattice`).
