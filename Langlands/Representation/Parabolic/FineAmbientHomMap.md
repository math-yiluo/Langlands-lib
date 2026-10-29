# The fine-to-ambient Hom map

This module defines `Langlands.RelativeHomComparison.fineAmbientHomMap`, an
actual `ℂ`-linear map between spaces of intertwiners. It is attached to one
specified outer intertwiner `q` and is defined on every inner intertwiner `f`,
including zero and non-surjective ones.

## Data

The inputs are a prime `p`, a p-adic field `F` with compatible topological data
`T`, a rank `n`, a block shape `B`, a refinement `S` of `B`, and a fine
representation `ω` on `(B.flatten S).Levi F.Carrier`. The map also takes a
fine real parameter `v₀ : Fin (B.flatten S).length → ℝ`, a coarse real
parameter `t : Fin B.length → ℝ`, a coarse representation `π` on
`B.Levi F.Carrier`, and an ambient representation `J` on
`GeneralLinear n F.Carrier`. The carriers of `ω`, `π` and `J` have universes
`uV`, `uW` and `uZ`. These are independent of each other and of the field
universe `uF`. The only hypothesis is `hω : IsSmooth ω.ρ` in the topology
supplied by `T`, which is used to construct `E_flat` below. There is no
assumption of irreducibility, admissibility, cuspidality, unitarity,
temperedness, finite-dimensionality, positive rank or a chamber condition.
Surjectivity of `f` or `q` is not assumed either.

Write, with the published `RelativeJacquetMultiplicity` and `RelativeRecovery`
definitions,

```text
A₀ = innerInduced T B S (fineTwist T B S ω v₀ 0)
Aₜ = innerInduced T B S (fineTwist T B S ω v₀ t)
A_f = RelativeRecovery.fineAmbientInduced T B S ω v₀ t
Ind = CuspidalJacquetMultiplicity.induced T B .
```

Here `fineTwist` uses the exact fine exponent
`-v₀ k + t ((B.flattenBlockEquiv S).symm k).1`. `innerInduced` is normalized
refined induction inside the coarse Levi, and `Ind` is upper normalized
parabolic induction to `GeneralLinear n F.Carrier`. Both use right translation
and positive-half modulus covariance. The specified intertwiner is

```text
q : (Ind (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ .
```

## Fixed choices

**The coarse character.** `coarseCharacter T B t` is the published coarse
determinant character `T.leviRealPowerCharacter B t`,
`m ↦ ∏ᵢ |det mᵢ|^{tᵢ}` with residue-normalized absolute values, packaged as an
`Induction.SmoothCharacter` using `T.isOpen_ker_leviRealPowerCharacter`.

**The inducing-data identity.** `inducingData_twist` states that twisting the
refined inducing data at coarse parameter `0` by the restriction of this
character to `refinedParabolic F.Carrier B S` gives the refined inducing data at
parameter `t`. On both sides the inducing data are
`twist (T.refinedParabolicHalfModulus B S) ((fineTwist …).ρ.comp
(refinedLeviProjection F.Carrier B S))`. The proof uses the first conjunct of
the published theorem `Langlands.refinedLeviRealTwist`, the restriction formula
for the coarse character. It instantiates the unused coarse-representation
universe of that theorem at `0`. The rest of the proof uses
`T.leviRealPowerCharacter_add` and commutativity of scalar multiplication.

**`E₀`.** `coarseTwistEquiv T B S ω v₀ t` is the actual equivalence

```text
E₀ : (T.leviRealPowerTwist B t A₀.ρ).Equiv Aₜ.ρ .
```

It is `Induction.smoothInductionTwistEquiv`, which multiplies induced functions
by the coarse character, followed by `Induction.smoothInducedEquiv` applied to
`equivOfRepresentationEq (inducingData_twist …)`. It depends only on
`T B S ω v₀ t`. It does not depend on `π`, `f`, `q` or `J`, and the universe
`uW` does not occur in it. Two lemmas give its evaluation formulas, both by
`rfl`:

```text
coarseTwistEquiv_eval:      (E₀ f)(m)      = χₜ(m) • f(m)
coarseTwistEquiv_symm_eval: (E₀.symm f)(m) = χₜ(m)⁻¹ • f(m)
```

Here `χₜ = T.leviRealPowerCharacter B t` and `f(m)` stands for
`Induction.eval _ _ f m`. These are the same two formulas that
`refinedLeviRealTwist` states for its existential equivalence. `E₀` is
constructed directly from the same imported ingredients as that proof, not
extracted from the existential.

**`E_flat`.** `flatStagesEquiv T B S ω v₀ t hω` is the actual equivalence

```text
E_flat : (Ind Aₜ).ρ.Equiv A_f.ρ .
```

It is `Langlands.Parabolic.orderedRefinementInductionEquiv` instantiated at the
fine shape `B.flatten S`, the coarse shape `B`, the refinement `S` and the
canonical coordinates. These coordinates are `B.flattenBlockEquiv S`, the
inverse of `B.flatten_size_flattenBlockEquiv S`, and
`B.index_index_eq_flatten S`. The equivalence is applied to the fine twist
`T.leviRealPowerTwist (B.flatten S) (fun k => -v₀ k + t ((B.flattenBlockEquiv
S).symm k).1) ω.ρ`, whose smoothness comes from `hω` and
`T.isSmooth_leviRealPowerTwist_iff`. Its type is then rewritten along the
published equation `B.leviRefinementEquiv_flatten F.Carrier S`, which replaces
the general Levi coordinate map by the canonical flattened Levi equivalence.
After unfolding `orderedRefinementIteratedInduced`, the resulting source is
definitionally `(Ind Aₜ).ρ` and the target is `A_f.ρ`. This is the same
construction as in the published proof
`Langlands.fineAmbientQuotientTransport`. It uses the same raised heartbeat
budget of `800000`.

## Linear pieces

`inducedMapLinear T B σ τ` is `f ↦ T.normalizedParabolicInducedMap B f`, the
published normalized parabolic induction of a Levi intertwiner, as a
`ℂ`-linear map from `σ.IntertwiningMap τ` to intertwiners between the two
normalized parabolic inductions. Its additivity and scalar compatibility are
proved pointwise on induced functions. `inducedMapLinear_apply` records the
formula by `rfl`.

`coarseTwistHom T B S ω v₀ t π` is the `ℂ`-linear map

```text
f ↦ fₜ = (twistIntertwining χₜ f).comp E₀.symm.toIntertwiningMap
```

from `A₀.ρ.IntertwiningMap π.ρ` to
`Aₜ.ρ.IntertwiningMap (T.leviRealPowerTwist B t π.ρ)`. The published
`twistIntertwining` keeps the underlying linear map of `f`. Its additivity and
scalar compatibility hold by `rfl`. `coarseTwistHom_apply` records the formula.

## The map

`fineAmbientHomMap T B S ω v₀ t hω π J q` is the composite of `ℂ`-linear maps

```text
llcomp q ∘ₗ (llcomp).flip E_flat.symm.toIntertwiningMap
  ∘ₗ inducedMapLinear T B _ _ ∘ₗ coarseTwistHom T B S ω v₀ t π
```

from `A₀.ρ.IntertwiningMap π.ρ` to `A_f.ρ.IntertwiningMap J.ρ`. Here `llcomp`
is Mathlib's bilinear composition `Representation.IntertwiningMap.llcomp`.
Postcomposition with `q` and precomposition with `E_flat.symm` are therefore
linear by Mathlib, not by a separate claim. `fineAmbientHomMap_apply` proves by
`rfl` the implemented formula

```text
C_q(f) = q.comp ((T.normalizedParabolicInducedMap B fₜ).comp
           E_flat.symm.toIntertwiningMap) .
```

## Provenance and scope

This is an internal construction for the relative Hom comparison, assembled
from published Library results. It is not presented as a construction stated
by Silberger. Every representation equivalence is derived from published
constructions: `smoothInductionTwistEquiv`, `smoothInducedEquiv`,
`equivOfRepresentationEq`, `orderedRefinementInductionEquiv` and
`leviRefinementEquiv_flatten`. The `E_flat` construction follows the published
proof of `Langlands.fineAmbientQuotientTransport`.

That theorem and the third clause of `refinedLeviRealTwist` are existence
statements for one specified surjection. Given surjective `q₀` and `q`, they
assert that some surjective transported map exists. The present module instead
defines one explicit linear map on the whole space of inner intertwiners for
each fixed `q`. It proves no property of `C_q` beyond its formula and
linearity. It makes no claim of injectivity, of surjectivity, that `C_q`
preserves surjections, or of any Hom-dimension inequality. In particular it
supplies no analytic upper bound and no relative comparison conclusion.
