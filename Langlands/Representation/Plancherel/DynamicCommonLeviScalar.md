# The scalar `j` does not depend on `P ∈ P(M)` (target)

Worker 5. The module
`Langlands.Representation.Plancherel.DynamicCommonLeviScalar`
states one Prop-valued target,
`ConditionalDynamicCommonLeviScalarStatement`. It is Waldspurger's
IV.3 (1), "`j_P(π)` does not depend on `P ∈ P(M)`", for an arbitrary second
parabolic `P' ∈ P(M)`. It is stated for the Library's canonical scalar
`conditionalCanonicalRationalScalar` (the scalar `j_P` of
`J_{P|P̄} J_{P̄|P}`, module `DynamicOppositeCanonicalScalar`), in the
transport form of the published opposite-pair target
`ConditionalDynamicOppositePairScalarStatement` (module
`DynamicOppositePairScalar`).

The target is not proved here. The module proves:

- two lemmas giving trivial splittings, `splitsAlong_of_radical_eq` and
  `splitsAlong_of_radical_eq_opposite`, and from them
  `isCommonLeviSplitting_of_pair`: when the radicals of `ψ` are those of `χ`,
  in the same or the exchanged order, every compact open subgroup has the
  common-Levi splitting for `χ` and `ψ`;
- `conditionalDynamicOppositePairScalar_of_commonLevi`: the target of this
  module implies the published opposite-pair target.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- Start of IV.3, printed p.285 / PDF p.51: for `π'` in the nonempty Zariski
  open subset of `O_ℂ` where `I_P^G V'` is irreducible,
  `J_{P|P̄}(π') J_{P̄|P}(π')` is multiplication by `j_P(π')`, and `j_P` is a
  rational function on `O_ℂ`.
- IV.3 (1), printed pp.285–286 / PDF pp.51–52: "`j_P(π)` est indépendant de
  `P ∈ P(M)`." For `P' ∈ P(M)` the proof starts from
  `j_{P'}(π) J_{P'|P}(π) = J_{P'|P̄'}(π) J_{P̄'|P'}(π) J_{P'|P}(π)`. It applies
  the composition formula IV.1 (12), printed p.283 / PDF p.49, to write
  `J_{P'|P̄'} = J_{P'|P} J_{P|P̄'}` and `J_{P̄'|P'} = J_{P̄'|P̄} J_{P̄|P'}`. It then
  applies IV.1 (12) again to write `J_{P|P̄'} J_{P̄'|P̄} = J_{P|P̄}` and
  `J_{P̄|P'} J_{P'|P} = J_{P̄|P}`. The result is
  `j_{P'}(π) J_{P'|P}(π) = J_{P'|P}(π) j_P(π)`.
- Théorème IV.1.1, printed p.278 / PDF p.44: for `P, P' ∈ P(M)` the integral
  `J_{P'|P}` converges on a cone and is a rational operator.
- I.1, printed p.240 / PDF p.6: `K` is the fixer of a special point of the
  apartment of `A_0`. Every closed algebraic subgroup `H` gets the Haar
  measure with `mes(H ∩ K) = 1`, and `G = P K` for every semistandard
  parabolic `P`.

## Provenance

The target is a derived statement adapted to the Library's data.

**Parabolics as cocharacters.** The Library's parabolic data are dynamic:
`P = P_G(χ)`, `U = U_G(χ)`, `P̄ = P_G(χ⁻¹)`, `Ū = U_G(χ⁻¹)` and `M = Z_G(χ)`
for a cocharacter `χ`. A parabolic `P' ∈ P(M)` is `P_G(ψ)` for a cocharacter
`ψ` with the same centralizer, and `j_{P'}` is the canonical scalar of `ψ`.
The target is stated for every `ψ` with the same centralizer subgroup
functor, `Z_G(ψ) = Z_G(χ)` (hypothesis `hM`). With `ψ` arbitrary, this
covers every `P'` given by a cocharacter, and also the change of
cocharacter describing one parabolic.

**The four instances of IV.1 (12).** In the notation of the published
target `ConditionalDynamicCommonLeviCompositionStatement` (module
`DynamicCommonLeviComposition`), IV.1 (12) for cocharacters `ψ₀, ψ₁, ψ₂` is
`J_{P₂|P₀} = J_{P₂|P₁} J_{P₁|P₀}` with `Pᵢ = P_G(ψᵢ)`. The proof of IV.3 (1)
uses the triples

- `(ψ₀, ψ₁, ψ₂) = (ψ⁻¹, χ, ψ)`: `J_{P'|P̄'} = J_{P'|P} J_{P|P̄'}`;
- `(ψ, χ⁻¹, ψ⁻¹)`: `J_{P̄'|P'} = J_{P̄'|P̄} J_{P̄|P'}`;
- `(χ⁻¹, ψ⁻¹, χ)`: `J_{P|P̄} = J_{P|P̄'} J_{P̄'|P̄}`;
- `(χ, ψ, χ⁻¹)`: `J_{P̄|P} = J_{P̄|P'} J_{P'|P}`.

In each triple the end points are opposite, so the distance condition
holds. The published composition target asks that `K ∩ U_G(ψ₁)` split along
`ψ₀` and `K ∩ U_G(ψ₂)` split along `ψ₁`, in the sense of Worker 200's
`CommonLeviSplitting.SplitsAlong` (module `CommonLeviCompactSplitting`).
Up to `SplitsAlong.inverse`, which replaces the cocharacter along which one
splits by its inverse, the eight splittings of the four triples are:
`K ∩ U_G(ψ)` and `K ∩ U_G(ψ⁻¹)` split along `χ`, and `K ∩ U_G(χ)` and
`K ∩ U_G(χ⁻¹)` split along `ψ`. These are exactly the four fields of
Worker 200's structure `CommonLeviSplitting.IsCommonLeviSplitting K χ ψ`.
The target takes this structure as its hypothesis `_hs`.

**The compact subgroup.** Both scalars are formed with one compact open
subgroup `K`. The data of `χ` use `G = P K` and `G = P̄ K` (`hPK`,
`hOppK`). The data of `ψ` use `G = P' K` and `G = P̄' K`, taken as further
hypotheses `hPK'`, `hOppK'`. The Library normalizes the Haar measures on
the radicals and their intersections by `K`, so that `K ∩ H` has mass one
as in I.1, and uses the induced quotient measures. For an arbitrary compact
open `K` with these factorizations the composition identities need not hold
without constant factors. Under the splitting hypothesis the published
composition target asserts the four identities without constant factors.
When `P` and `P'` are semistandard, Waldspurger's `K` has the four
factorizations by I.1. The splittings are expected for it from Bruhat–Tits
theory. The Library proves neither property for that `K`.
Worker 200's `CommonLeviSplitting.exists_isCommonLeviSplitting` gives
arbitrarily small compact open `K` with the splitting. Such a `K` need not
have the factorizations. The Library constructs no `K` with both
properties.

**Representation and parameters.** As in the opposite-pair target, `Aψ`
is the local notation for `changeRepresentation χ ψ hM A`: the same
representation viewed on `Z_G(ψ)(F) = M(F)`. The two scalars live in the
function fields of the unramified characters of the two actual centralizer
schemes `parameterScheme χ` and `parameterScheme ψ`. The target compares
them through `rationalUnramifiedFunctionFieldEquiv` along
`parameterChangeIso χ ψ hM`, as explained in `DynamicOppositePairScalar.md`.

**Smoothness instance.** `IsCommonLeviSplitting` is declared under the
instance `[Smooth G.X.hom]`. The target binds this instance. It is the field
`smooth` of `IsConnectedReductive G`, as in the published composition
target.

## Splittings for the parabolics of one opposite pair

Section `Splitting` assumes `[Smooth G.X.hom]`, needed only to form
`SplitsAlong`. `SplitsAlong Q t m` says that every point of `Q ∩ U_G(m)` is
`a * b` with `a ∈ Q ∩ U_G(t⁻¹) ∩ U_G(m)` and `b ∈ Q ∩ U_G(m) ∩ U_G(t)`.

- `splitsAlong_of_radical_eq`: if `U_G(m) = U_G(t)` on rational points,
  then `SplitsAlong Q t m` for every compact open `Q`; take `a = 1`,
  `b = g`.
- `splitsAlong_of_radical_eq_opposite`: if `U_G(m) = U_G(t⁻¹)`, then
  `SplitsAlong Q t m`; take `a = g`, `b = 1`.
- `isCommonLeviSplitting_of_pair`: if `U_G(ψ) = U_G(χ)` and
  `U_G(ψ⁻¹) = U_G(χ⁻¹)`, or `U_G(ψ) = U_G(χ⁻¹)` and `U_G(ψ⁻¹) = U_G(χ)`, then
  `IsCommonLeviSplitting Q χ ψ` for every `Q`. Each of the four fields is
  one of the two previous lemmas.

## The target

`ConditionalDynamicCommonLeviScalarStatement` quantifies over a
nonarchimedean local field `F`, an affine group scheme `G` of locally finite
type with `[Smooth G.X.hom]`, cocharacters `χ`, `ψ`, the premises `hRefl`,
`hCST`, `hG : IsConnectedReductive G`, and the equality `hM` of
centralizer subgroup functors. It also quantifies over a compact open
subgroup `K`, the splitting `_hs : IsCommonLeviSplitting K χ ψ`, the
decompositions `hPK : G = P K`, `hOppK : G = P̄ K`, `hPK' : G = P_G(ψ) K`,
`hOppK' : G = P_G(ψ⁻¹) K`, and a smooth representation `A` of `M(F)`. It
takes:

- conditional data of the canonical scalar for `(χ, K, A)`, exactly as
  taken by `conditionalCanonicalRationalScalar`: continuations `p`, `q`,
  open nonempty `DForward ⊆ forwardFullDomainRegion χ K hK A` and
  `DReverse ⊆ reverseFullDomainRegion χ K hK A`, and an open nonempty `D`
  on which the unramified induction of `A ⊗ z` from `P` is irreducible
  (`hi`);
- independent conditional data `p'`, `q'`, `DForward'`, `DReverse'`, `D'`,
  `hi'` of the same kind for `(ψ, K, Aψ)`; `hi'` is generic irreducibility
  of the induction from `P'`.

Its conclusion is

```
conditionalCanonicalRationalScalar ψ … K hK hPK' hOppK' Aψ p' q' … hi'
  = rationalUnramifiedFunctionFieldEquiv … (parameterChangeIso χ ψ hM)
      (conditionalCanonicalRationalScalar χ … K hK hPK hOppK A p q … hi).
```

The hypothesis list is that of the opposite-pair target, with the pair
hypothesis `_hpair` replaced by `_hs` and with the instance
`[Smooth G.X.hom]` added. The splitting `_hs` is the only hypothesis
relating `ψ` to `χ` beyond `hM`.

## The opposite-pair target from this target

`conditionalDynamicOppositePairScalar_of_commonLevi` assumes the target and
proves `ConditionalDynamicOppositePairScalarStatement`. Given the data of
that statement, it sets `[Smooth G.X.hom]` to `hG.smooth`. It obtains
`IsCommonLeviSplitting K χ ψ` from `isCommonLeviSplitting_of_pair`, using
the two radical equalities in each branch of `_hpair`. Then it applies the
target to the same data.

## Intended use and missing inputs

The proof of the target is meant to follow Waldspurger's proof. The
Library does not yet have all of its inputs.

1. The four instances of IV.1 (12) above, on the common region where the
   integrals of each triple converge, are instances of the published target
   `ConditionalDynamicCommonLeviCompositionStatement`, given `_hs`. That
   target is unproved (proof tasks Task 7002
   `01859916-3d8b-438c-816e-386388809766` and, for its structural
   hypothesis, Task 7001 `7351966c-e13e-40a4-bf1d-6b627cd4da5f`). Its
   pair families take a squared-modulus identity for each pair as a proof
   argument. The Library's opposite families obtain it from `hRefl` and
   `hCST` (`conditionalSquaredModulus`); for the pairs here that are not
   opposite it is not supplied.
2. The four operators `J_{P'|P}`, `J_{P|P̄'}`, `J_{P̄'|P̄}` and `J_{P̄|P'}` of
   pairs that are not opposite need rational continuations (Théorème IV.1.1)
   to make sense of the identities at the points where the scalars are
   evaluated. The Library has continuation data only for opposite pairs.
   The target does not take such data, so a proof must construct these
   continuations or wait for them.
3. The cancellation of `J_{P'|P}` in
   `j_{P'} J_{P'|P} = J_{P'|P} j_P` needs the continued `J_{P'|P}` to be
   nonzero as a rational family.
4. The compact pictures of `ψ` live on `Z_G(ψ)(F)` with `Aψ`. They must be
   identified with those of the common Levi `Z_G(χ)(F)` with `A`, as in the
   transport step of the opposite-pair target (proof task Task 6924
   `9fe80067-873a-442f-b6b5-c3a6191f7655`).

No proof task is published with this target, because of the missing
input 2.

## Not proved here

The target. The composition formula IV.1 (12), the rational continuation
of `J_{P'|P}` for pairs that are not opposite, and IV.3 (4) and (5). The
existence of a compact open `K` that has both the four factorizations and
the splitting.

## Axioms

The proved results use only `propext`, `Classical.choice` and `Quot.sound`.
The target is a `def … : Prop` and introduces no axioms.
