# `PP̄`-regularity of Langlands triplets (Renard VII.4.1, Lemma): statement

Author: Worker 1222. Module
`Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityStatement`,
namespace `Langlands.Aubert.General.RepresentedParabolic`. The module contains one
**statement**, the closed `Prop`-valued definition
`LanglandsTripletOppositeRegularityStatement` (universe parameters `u, v`). It proves
nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
**9 July 2026**, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 1222
read VII.3.1–VII.3.5 and VII.4, printed pp.232–246 / PDF pp.238–252, for this unit.

The Lemma of VII.4.1, printed p.241 / PDF p.247, reads:

> **Lemme.** Si `(P = MN, (σ, E), ψ)` est un triplet de Langlands, alors la représentation
> `σ ⊗ ψ` est `PP̄`-régulière. En particulier, il existe un opérateur d'entrelacement non
> nul, unique à un facteur scalaire près :
> `J_{P̄|P}(σψ) : i^G_P(σ ⊗ ψ) → i^G_{P̄}(σ ⊗ ψ)`.

Its proof, printed pp.241–242 / PDF pp.247–248, ends: "par réciprocité de Frobenius
`Hom_G(i^G_P(σ ⊗ ψ), i^G_{P̄}(σ ⊗ ψ))` est de dimension 1, engendré par `J_{P̄|P}(σψ)`."

Langlands triplets are those of the Definition of VII.4.1, printed p.241 / PDF p.247.
`PQ`-regularity is defined in VII.3.3, printed pp.233–234 / PDF pp.239–240, and the
operator `J_{Q|P}(σ)` in VII.3.4, printed pp.235–236 / PDF pp.241–242.

## Published objects used

- From [LanglandsTriplet](LanglandsTriplet.md): `IsLanglandsTriplet`, the triplet predicate
  of VII.4.1 relative to a maximal split torus `i`, a generic cocharacter `ν` and reflection
  data `D`; `leviUnramifiedCharacters l hl`, Renard's `X(M)`.
- From [PQRegularity](../Intertwining/PQRegularity.md): `IsPQRegular p l r hp hr hl hmul q lQ
  rQ hq hrQ hlQ hmulQ a σ`, condition (i) of the VII.3.3 Lemma, `I_σ + I^{PQ}_σ = ℂ[A_M]`,
  for the split component `a : A_M → M`.
- The twist `σ ⊗ ψ` is the published `SmoothRep.twist` with
  `Plancherel.unramifiedCharacter_isOpen_ker`, exactly as in the published
  [LanglandsClassificationStatement](LanglandsClassificationStatement.md).
- `leviInductionFunctor`, Renard's normalized `i^G_P` on representations of `M(F)`, from
  the published represented-parabolic interface.
- From Mathlib: `Representation.IntertwiningMap` with its `ℂ`-module structure, and
  `Module.finrank`.

## Lean statement

`LanglandsTripletOppositeRegularityStatement` quantifies over exactly the data of the
published `LanglandsQuotientUniqueStatement`:

- a nonarchimedean local field `k : Type u` of any characteristic and a connected reductive
  `G` over `Spec k`, whose rational points carry the canonical topology and are assumed
  locally compact and nonarchimedean;
- a commutative group scheme `T` with `i : T.toGrp ⟶ G` (`[Mono i.hom.hom.left]`), a
  cocharacter `ν` and reflection data `D`;
- a represented parabolic `P = MU` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`), a split
  component `a : A.toGrp ⟶ M` with `ha`, a simple-root index `J`, a factor `f : A ⟶ T`, a
  smooth representation `σ` of `M(F)` on a carrier in universe `v`, and `ψ` in
  `leviUnramifiedCharacters l hl`.

It adds an opposite parabolic: group schemes `Pbar`, `Ubar` and maps
`pbar : Pbar ⟶ G`, `lbar : M ⟶ Pbar`, `rbar : Ubar ⟶ Pbar` with `hpbar`, `hlbar`, `hrbar`,
`hmulbar`. Two hypotheses make it opposite to `P`, as in the published
`LeviSecondAdjointnessStatement`: `lbar ≫ pbar = l ≫ p` (the same Levi `M` in `G`), and
`pointImage p ⊓ pointImage pbar = pointImage (l ≫ p)` (`P(F) ∩ P̄(F) = M(F)`).

If `IsLanglandsTriplet i ν D p l a hp hl ha J f σ ψ` holds, then, writing `τ` for
`σ ⊗ ψ`:

1. `IsPQRegular p l r hp hr hl hmul pbar lbar rbar hpbar hrbar hlbar hmulbar a τ`: `σ ⊗ ψ`
   is `PP̄`-regular;
2. `Module.finrank ℂ (IntertwiningMap (i_P^G τ) (i_{P̄}^G τ)) = 1`, where the two
   representations are `(leviInductionFunctor p l r …).obj τ` and
   `(leviInductionFunctor pbar lbar rbar …).obj τ`.

Since `Module.finrank` is zero on infinite-dimensional spaces, clause 2 says that the space
of intertwining maps is finite-dimensional of dimension exactly one: there is a nonzero
intertwining operator, unique up to a scalar.

## Provenance and departures from the source

The provenance is the source Lemma.

- **The operator `J_{P̄|P}(σψ)`.** The source names the spanning operator
  `J_{P̄|P}(σψ)`. The published
  [PQIntertwiningOperatorStatement](../Intertwining/PQIntertwiningOperatorStatement.md)
  characterizes `J_{Q|P}(σ)` only relative to an identification `e` of
  `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E)` with `E`, because the integral over `N̄ ∩ U` is not yet
  formalized. Clause 2 states the dimension without naming the operator. Once the
  dimension is one, every nonzero intertwining operator, in particular any `J_{P̄|P}(σψ)`
  of that statement, spans the space.
- **`PQ`-regularity.** `IsPQRegular` is condition (i) of the VII.3.3 Lemma. Renard defines
  `PQ`-regularity as "(i) or (ii)"; the Lemma proves the two equivalent.
- **The opposite parabolic.** Renard's `P̄` is the parabolic opposite to the standard `P`
  with respect to `M`. Here it is any actual rational parabolic with the same Levi whose
  rational points meet those of `P` exactly in `M(F)`, the published convention of the
  VI.9.6 statements.
- **Sizes.** The carrier of `σ` lies in an independent universe `v`; the induced
  representations lie in `max u v`. No finite-dimensionality of `σ` is assumed.

## Scope

This module states the VII.4.1 Lemma and proves it in no part. The Definition of VII.4.1
is the published `IsLanglandsTriplet`, and the Theorem of VII.4.2 is the published
`LanglandsClassificationStatement`. A proof belongs to a separate proof task.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.LanglandsClassification.LanglandsTriplet` | `IsLanglandsTriplet`, `leviUnramifiedCharacters`, and through it `leviInductionFunctor`, `leviPointTopology`, `leviPoints_nonarchimedeanGroup` |
| `Langlands.Representation.Intertwining.PQRegularity` | `IsPQRegular` |
| `Langlands.Representation.Category.Twist` | `SmoothRep.twist` |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
