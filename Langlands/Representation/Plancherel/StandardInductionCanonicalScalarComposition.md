# Equal canonical opposite scalars for two parabolics with one Levi

Author: Worker 200.

## Source and provenance

This is derived support for J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques (d'après Harish-Chandra)*, J. Inst. Math.
Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082. The registered
original is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

At the beginning of IV.3, printed p.285 / PDF p.51, the composite
`J_{P|P̄}(π') J_{P̄|P}(π')` of the two opposite standard intertwiners is the
scalar `j_P(π')`. Assertion (1) states that `j_P` does not depend on
`P ∈ P(M)`. Its proof, printed pp.285–286 / PDF pp.51–52, uses four
instances of the composition formula IV.1(12), printed p.283 / PDF p.49,
and cancels `J_{P'|P}`. In the source all measures are normalized by one
special maximal compact subgroup (I.1, printed p.240 / PDF p.6).

The published `standardInductionCompositeCanonicalRationalScalar` (module
`StandardInductionCanonicalScalar`) is the rational scalar of the actual
continued composite of two standard integral families, for fixed
decompositions, compact model, inducing object and measures. This module
proves that the canonical scalars of two opposite pairs `(P, P̄)` and
`(P', P̄')` with a common Levi subgroup agree, if eight composition
identities hold on nonempty open sets of parameters. It applies
`continuedCompositeRationalScalar_eq_of_parabolicComposition_symm` from the
module `ContinuedParabolicCompositionScalar`, a candidate under review, to
the compact pictures. The provenance is internal. No new translation of a
numbered literature result is asserted.

## Composition on an open set

The first section uses the setting of `ContinuedIntertwiningComposition`. `F`
is a nonarchimedean local field of arbitrary characteristic and `L` a group
scheme over `F` whose rational points carry a topology. Parameters are the
unramified characters for `rationalNormCharacters L`. `G` is a locally
compact nonarchimedean group with three closed semidirect decompositions
`P₀ = M U₀`, `P₁ = M U₁`, `P₂ = M U₂` sharing the Levi subgroup `M`. Each
comes with `IsUnimodularModulus`, a closed parabolic, the factorization
`G = Pᵢ K` for one compact open subgroup `K`, and a continuous projection.
`e : L(F) ≃ₜ* M` identifies parameters, every rational norm character of `L`
is continuous, and `A` is a canonical `SmoothRep.{0,uG,uV} ℂ M`. Write
`Iᵢ(χ)` for the actual normalized induction from `Pᵢ` of the twist of `A` by
the character transported through `e`.

`HasOpenInductionComposition L h₀ hU₀ h₁ hU₁ h₂ hU₂ e A J₁₀ J₂₁ J₂₀` is a
`Prop` about three families of actual ambient intertwining maps:
`J₁₀` from `I₀` to `I₁` on `Ω₁₀`, `J₂₁` from `I₁` to `I₂` on `Ω₂₁`, and `J₂₀`
from `I₀` to `I₂` on `Ω₂₀`. The regions are arbitrary sets. It states that
there is an open, nonempty `D` contained in `Ω₁₀`, `Ω₂₁` and `Ω₂₀` with
`J₂₀(χ) = J₂₁(χ) ∘ J₁₀(χ)` for all `χ ∈ D`.

`HasOpenInductionComposition.compact` proves `HasOpenComposition` for the
three conjugate families on the fixed compact pictures, given by the
published `compactIntertwiningOperator`, on the same set `D`. The
pointwise step is the published `compactIntertwiningOperator_comp`.

## Four decompositions

The main section adds four closed decompositions `P₀ = M U₀`, `P₁ = M U₁`,
`P₂ = M U₂`, `P₃ = M U₃`, with the same accompanying data as above for each.
They play the roles of `P`, `P'`, `P̄'` and `P̄`. No opposition, root or
length relation between them is assumed. `L` is connected reductive (`hL`),
its valuation-image projection is continuous (`hp`), and `G` is Hausdorff
and separable, as needed for the published scalar construction and generic
Schur argument.

The two opposite pairs carry standard integrals. As in
`StandardInductionCanonicalScalar`, all measure data are explicit: Borel
structures on the four radicals, on the four intersections
`U₀ ∩ U₃`, `U₃ ∩ U₀`, `U₁ ∩ U₂`, `U₂ ∩ U₁` (as `subgroupOf`), and on the four
quotients; quotient measures `q₃₀`, `q₀₃`, `q₂₁`, `q₁₂`; regular
right-invariant Haar measures on the radicals and intersections; the four
quotient integration compatibilities; closedness of `M`; and the four
`SquaredModulusCompatibility` identities for `(P₀,P₃)`, `(P₃,P₀)`,
`(P₁,P₂)` and `(P₂,P₁)`. The families `J₃₀`, `J₀₃`, `J₂₁`, `J₁₂` are the
published `standardInductionIntertwinerFamily` on their
`standardIntertwiningFullDomainRegion`s, from `P₀` to `P₃`, from `P₃` to
`P₀`, from `P₁` to `P₂` and from `P₂` to `P₁`. Each has a continuation `pᵢⱼ`
of its compact conjugate and a nonempty open subset `Dᵢⱼ` of its region.
There are two irreducibility loci. `D` is open and nonempty, and `I₀(χ)` is
irreducible for `χ ∈ D`. `D'` is open and nonempty, and `I₁(χ)` is
irreducible for `χ ∈ D'`.

The eight cross families are arbitrary actual intertwining families on
arbitrary regions, each with a continuation of its compact conjugate:
`J₁₀` (from `P₀` to `P₁`), `J₀₂` (from `P₂` to `P₀`), `J₂₃` (from `P₃` to
`P₂`), `J₃₁` (from `P₁` to `P₃`), `J₀₁` (from `P₁` to `P₀`), `J₁₃` (from `P₃`
to `P₁`), `J₃₂` (from `P₂` to `P₃`) and `J₂₀` (from `P₀` to `P₂`). They need
not be standard integrals.

## Equality of the canonical scalars

`standardInductionCompositeCanonicalRationalScalar_eq_of_parabolicComposition`
assumes eight hypotheses `HasOpenInductionComposition`:

* `h₁₂`: `J₁₂ = J₁₀ ∘ J₀₂`, that is `J_{P'|P̄'} = J_{P'|P} J_{P|P̄'}`;
* `h₂₁`: `J₂₁ = J₂₃ ∘ J₃₁`, that is `J_{P̄'|P'} = J_{P̄'|P̄} J_{P̄|P'}`;
* `h₀₃`: `J₀₃ = J₀₂ ∘ J₂₃`, that is `J_{P|P̄} = J_{P|P̄'} J_{P̄'|P̄}`;
* `h₃₀`: `J₃₀ = J₃₁ ∘ J₁₀`, that is `J_{P̄|P} = J_{P̄|P'} J_{P'|P}`;
* `h₀₃'`: `J₀₃ = J₀₁ ∘ J₁₃`, that is `J_{P|P̄} = J_{P|P'} J_{P'|P̄}`;
* `h₃₀'`: `J₃₀ = J₃₂ ∘ J₂₀`, that is `J_{P̄|P} = J_{P̄|P̄'} J_{P̄'|P}`;
* `h₁₂'`: `J₁₂ = J₁₃ ∘ J₃₂`, that is `J_{P'|P̄'} = J_{P'|P̄} J_{P̄|P̄'}`;
* `h₂₁'`: `J₂₁ = J₂₀ ∘ J₀₁`, that is `J_{P̄'|P'} = J_{P̄'|P} J_{P|P'}`.

The first four are the instances of IV.1(12) used in the source. The last
four are the same identities with the roles of `P` and `P'` exchanged. Each
holds on its own nonempty open set. The conclusion is

```
standardInductionCompositeCanonicalRationalScalar (P₁, P₂) … =
  standardInductionCompositeCanonicalRationalScalar (P₀, P₃) … ,
```

where the left side uses the families `J₂₁`, `J₁₂`, their continuations,
`D₂₁`, `D₁₂` and the locus `D'`, and the right side uses `J₃₀`, `J₀₃`, their
continuations, `D₃₀`, `D₀₃` and the locus `D`. Both are elements of the
published field `rationalUnramifiedFunctionField L hp hL`. No nonvanishing
of any intertwiner or scalar is assumed.

The proof unfolds each canonical scalar to the coefficient scalar
`continuedCompositeRationalScalar` at its internally selected normalized pair
`compactInductionScalarExtraction`. The eight hypotheses become
compact-picture `HasOpenComposition` hypotheses by
`HasOpenInductionComposition.compact`. The scalar identities of the two
continued composites on their whole common regular regions are the
published `continuedInductionComposite_compact_eq_scalar`, applied with the
locus `D` for `(P₀, P₃)` and `D'` for `(P₁, P₂)`. Then
`continuedCompositeRationalScalar_eq_of_parabolicComposition_symm` gives the
equality.

## Use in IV.3(1)

For actual parabolic subgroups `P, P' ∈ P(M)` and their opposites, the
eight identities are instances of IV.1(12). Proving them on open sets
requires convergence of the integrals and the measure-theoretic composition
of standard integrals. Here the three quotient measures in each identity
must also be compatible, for example normalized by one compact open
subgroup. For opposite-source dynamic radicals with a common Levi this
composition is `CommonLeviSplitting.comp_hasIntegral_of_isCommonLeviSplitting`
of the module `CommonLeviCompactSplitting`, an approved candidate. It still
needs convergence, and turning the cross families into standard integrals
needs their own `SquaredModulusCompatibility` identities. Neither is
supplied here.

## Scope

* All eight composition identities, all four continuations of the standard
  families, all eight cross families with continuations, and both
  irreducibility loci are explicit inputs. No convergence domain, integral
  composition or instance of IV.1(12) is proved.
* All measures and the four `SquaredModulusCompatibility` identities are
  explicit inputs. The scalars depend on these measures. The conclusion
  compares the two canonical scalars for the given measures only. It is not
  the source's statement for its measures normalized by a special maximal
  compact subgroup.
* No opposite relation between `P₀` and `P₃`, or between `P₁` and `P₂`, is
  used or established.
* No nonvanishing, positivity or orbit property of the scalar, no `μ` and no
  Plancherel conclusion is claimed.
