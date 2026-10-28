# Irreducible unequal-rank mirabolic pairings

This module states the two conclusions of the Lemma in JPSS (1983), §2.11,
printed p.399, in the namespace `Langlands.RankinSelberg`:

- `UnequalRankMirabolicPairingRigidityStatement.{uF,uV,uW}`;
- `UnequalRankCompactGenericPairingStatement.{uF,uW}`.

Both are `Prop`-valued definitions. They provide targets for the irreducible
lemma; they do not prove it or the full Whittaker-type extension
`UnequalRankBilinearUniquenessStatement`. That published target and all imported
definitions remain unchanged. The proof for general Whittaker-type coefficient
models requires additional filtration arguments beyond this statement family.

## Data, topology and covariance

The parameters are `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData`, and natural numbers `n,r`. Each statement
installs `T.topology` and obtains its local `IsTopologicalRing F.Carrier`
instance from `T.valuativeRel` and `T.localField`, as in the published
`Whittaker.MirabolicPairingStatement`. The absolute value and residue
cardinality are `normalizedAbsoluteValue T` and `q = T.residueCardinality`;
no canonical topological data are substituted.

For every `hnr : n < r`, write `R = r+1` and `t = n+1`. Let
`ψ : UnitaryAdditiveCharacter F.Carrier`. The first representation acts on
the actual mirabolic subgroup `GeneralLinear.mirabolic r F.Carrier` of
`GL_R`, and the second acts on the actual `Langlands.GeneralLinear t F.Carrier`.
General carriers are complex modules with `AddCommGroup` structures.

The imported
`unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) ξ η s`
is the actual submodule of curried complex bilinear forms
`B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ` satisfying both laws:

```text
B (ξ (unequalRankEmbedding hnr g) v) (η g w)
  = determinantWeight (normalizedAbsoluteValue T) g
      (((r-n : ℕ) : ℂ)/2 - s) * B v w
```

for every `g : GL_t` and every `v,w`, and

```text
B (ξ (unequalRankUnipotentLift u) v) w
  = (Whittaker.standardCharacter ψ r u : ℂ) * B v w
```

for every upper unipotent `u` satisfying
`IsUnequalRankCovarianceUnipotent n u` and every `v,w`.
The embedding is `g ↦ diag(g,I_(r-n))`. The additional unipotent subgroup is
exactly `U_(t+1,R) = U_(n+2,r+1)`, whose leading `(n+2)`-square block is
the identity. Its character is the standard character of `GL_R`, restricted
to this subgroup. Neither law is redefined in this module.

Only `n < r` restricts the ranks. In particular `n=0` and adjacent ranks
`r=n+1` are included. In the latter case the additional unipotent subgroup
is trivial, as proved in `unequalRankCovarianceSubgroup_adjacent`.

## Spectral rigidity

For arbitrary independent carriers `V : Type uV`, `W : Type uW`, and

```text
ξ : Representation ℂ (GeneralLinear.mirabolic r F.Carrier) V
η : Representation ℂ (Langlands.GeneralLinear (n+1) F.Carrier) W,
```

the hypotheses are exactly

```text
IsSmooth ξ
Representation.IsIrreducible ξ
IsAdmissible η
Representation.IsIrreducible η.
```

Admissibility already includes smoothness for `η`. There is no admissibility
assumption on `ξ` and no central character, classification, finite length,
genericity or auxiliary rigidity premise.

`UnequalRankMirabolicPairingRigidityStatement` asserts that there is a finite
set `E : Finset ℂ` such that, for every `s : ℂ` with
`spectralPoint q s ∉ E` and every nonzero element `B` of the covariance space,

```text
Nonempty (ξ.Equiv (Whittaker.mirabolicCompactInduced ψ r)) ∧
Whittaker.HasFunctional
  (N := GeneralLinear.upperUnipotent (n+1) F.Carrier)
  (θ := Whittaker.inverseStandardCharacter ψ n) η.
```

The finite set is chosen after the character and representations but before
`s` and `B`. Its elements are spectral values `q^(-s)`, not exponents.
This states the lemma's generic-spectral-value vanishing alternative as an
implication: outside the finite set, nonvanishing forces the compact/generic
case. No representation equivalence or functional is assumed.

## Exact dimension for the compact/generic pair

`UnequalRankCompactGenericPairingStatement` takes an arbitrary independent
carrier `W : Type uW` and the smaller representation `η` above. It assumes
admissibility, irreducibility, and explicitly the same inverse-standard
`Whittaker.HasFunctional` condition. This condition means the existence of
a nonzero character-equivariant linear functional; it is the source's
genericity condition in this irreducible setting.

For every `s : ℂ` the conclusion is

```text
Nonempty
  ((unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
      (Whittaker.mirabolicCompactInduced ψ r) η s) ≃ₗ[ℂ] ℂ).
```

Thus the space is exactly one-dimensional, including existence of a nonzero
form, for every exponent, with no exceptional set. The compact representation
is the published actual right-translation representation on compactly induced
functions, not a supplied substitute. Its carrier
`Whittaker.MirabolicCompactFunctions ψ r` has its natural universe `Type uF`.
The first statement keeps `uF,uV,uW` independent; the second keeps `uF,uW`
independent, with no additional carrier universe for the compact model.

## Original source and parameter correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
367–464, §2.11, printed pp.398–403, especially the Lemma on p.399.
Registered source: `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.11 was visually read completely on printed pp.398–403
(zero-based PDF pages 32–37, verified against printed page headers).
No applicable registered erratum was found in the checked project and current
Library notes/wiki or the literature index.

The source's large rank `r` is `R=r+1` here; its smaller rank is `t=n+1`.
Its `τ_R` is the actual standard compact mirabolic representation used above.
Equation (2.11.1) has integral exponent `s-(R-t)/2`, and the simultaneous
covariance (2.11.2) has the opposite exponent `(R-t)/2-s`.
The Proposition and Lemma on p.399 describe invariant pairings with the first
representation twisted by `α^λ`, where `α(g)=|det g|`. Such a pairing has
untwisted covariance factor `|det g|^(-λ)`. Consequently

```text
λ = s-(R-t)/2 = s-(r-n)/2
|det g|^(-λ) = |det g|^((r-n)/2-s).
```

The variable `s` in both Lean statements is the integral parameter. Since
`n<r`, the natural difference `r-n` in the published weight equals the
ordinary rank difference. The source's spectral point is related by

```text
q^(-λ) = q^((R-t)/2) q^(-s).
```

The factor `q^((R-t)/2)` is fixed and nonzero, so rescaling a finite exceptional
set preserves finiteness. The exact one-dimensional assertion at every
exponent is also preserved by the shift.

Equation (2.11.4), and condition (5) on p.399, impose the standard character
on `U_(t+1,R)`. The smaller Whittaker character in the proof is the conjugate
of the standard character; for the unitary `ψ` it is precisely the
inverse-standard character explicitly retained in both statements.

The lemma assumes a smooth irreducible mirabolic representation and an
irreducible admissible smaller general linear representation. It states exact
dimension one for the compact/generic pair, and otherwise vanishing outside
a finite spectral set. The separate p.399 Proposition starts with irreducible
generic representations of both full general linear groups. Its reduction
through finite composition series and the distribution argument on pp.400–403
are source proof context; this module contains no implementation of those proofs.
The source permits arbitrary non-Archimedean local fields, while these targets
have the requested `PadicField` scope.

## Provenance

These definitions translate the two conclusions of the original irreducible
lemma, using the published actual form space and compact model. The finite-set
implication and linear-equivalence formulation express its vanishing and exact
dimension conclusions with the integral parameter convention. They introduce
no additional mathematical premise, new axiom or proof claim.
