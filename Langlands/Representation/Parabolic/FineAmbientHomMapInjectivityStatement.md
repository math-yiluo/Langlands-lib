# Injectivity of the specified fine-to-ambient Hom map

Authors: Worker 125, Worker 526 and Worker 359.

`Langlands.RelativeHomComparison.FineAmbientHomMapInjectivityStatement`
defines a closed proposition asserting injectivity of the actual public
`Langlands.RelativeHomComparison.fineAmbientHomMap`. This module supplies
the statement only.

## Data and hypotheses

Fix a prime `p`, a p-adic field `F : PadicField.{uF} p`, topological data `T`,
any rank `n`, a block shape `B : BlockShape n`, and a refinement
`S : BlockRefinement B`. The fine representation `ω` is on the flattened
product Levi `(B.flatten S).Levi F.Carrier`; `π` is on the coarse product
Levi `B.Levi F.Carrier`; and `J` is on `GeneralLinear n F.Carrier`.
The four universes `uF`, `uV`, `uW` and `uZ` for the field and these three
representation carriers remain independent.

The real parameters are arbitrary functions
`v₀ : Fin (B.flatten S).length → ℝ` and `t : Fin B.length → ℝ`.
The representation hypotheses are precisely smoothness `hω : IsSmooth ω.ρ`,
irreducibility `Representation.IsIrreducible π.ρ`, nontriviality
`Nontrivial J.V`, and surjectivity of the specified actual intertwiner

```text
q : (CuspidalJacquetMultiplicity.induced T B
       (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.IntertwiningMap J.ρ .
```

Smoothness of `π` is not a premise. Neither irreducibility of `J` nor any
admissibility, unitarity, cuspidality, temperedness, support, finite-length,
finite-dimensionality, positive-rank or chamber condition is imposed.
There is no middle representation or chosen-equivalence hypothesis.

## The two Hom spaces and the conclusion

Write

```text
A₀ = innerInduced T B S (fineTwist T B S ω v₀ 0)
Aₜ = innerInduced T B S (fineTwist T B S ω v₀ t)
A_f = RelativeRecovery.fineAmbientInduced T B S ω v₀ t .
```

The domain is the full space of coarse-Levi intertwiners
`A₀.ρ.IntertwiningMap π.ρ`. The codomain is the full space of ambient-group
intertwiners `A_f.ρ.IntertwiningMap J.ρ`. For the fixed specified `q`,
the public construction is the `ℂ`-linear map

```text
C_q = fineAmbientHomMap T B S ω v₀ t hω π J q
C_q(f) = q ∘ T.normalizedParabolicInducedMap B fₜ ∘ E_flat⁻¹,
fₜ = (twistIntertwining (T.leviRealPowerCharacter B t) f) ∘ E₀⁻¹ .
```

Here `E₀ = coarseTwistEquiv T B S ω v₀ t` identifies the coarse real twist
of `A₀` with `Aₜ`, and
`E_flat = flatStagesEquiv T B S ω v₀ t hω` identifies the outer induction
of `Aₜ` with `A_f`. These are the actual fixed equivalences defined in the
imported map module.

The conclusion `Function.Injective C_q` means that for every pair of inner
intertwiners `f` and `g`, equality `C_q(f) = C_q(g)` implies `f = g`.
It applies to the entire Hom space, including zero and non-surjective maps.
The statement neither restricts the domain to surjections nor replaces the
value `C_q(f)` by an existentially selected map.

## Conventions inherited from the public map

The fine determinant exponent is exactly
`-v₀ k + t ((B.flattenBlockEquiv S).symm k).1`: the negative fine parameter
plus the positive coarse parameter restricted to its containing coarse
block. At coarse parameter zero this is `-v₀ k`. Each real determinant
character uses residue-normalized absolute values.

The inner induction uses the upper refined parabolic inside the coarse
Levi, and the outer and fine ambient inductions use the upper block
parabolics of `GL_n(F)`. They act by right translation and have covariance
by the positive half of the corresponding modulus. The flattened product
Levi is identified with the refined subgroup by `flattenedLeviEquiv`;
`fineTwist` pulls the representation back along its inverse. The induction
in stages equivalence uses the canonical coordinates
`B.flattenBlockEquiv S`, the inverse size equality
`B.flatten_size_flattenBlockEquiv S`, and `B.index_index_eq_flatten S`,
with the Levi coordinate map identified by `B.leviRefinementEquiv_flatten`.

## Internal provenance and scope

This is an internal algebraic target extracted from the shared prototype
by Workers 526 and 359. Worker 359 supplied the nonzero-map and
nonzero-linear-combination argument, and Worker 526 implemented the
prototype's actual surjection-preservation step. The intended route uses
irreducibility of `π` to make every nonzero inner map surjective. Its
smooth source then supplies smoothness of `π` for that map. Twisting,
smooth induction surjectivity and the fixed equivalences transport that
surjection to the actual value `C_q(f)`. A surjection onto the nontrivial
carrier of `J` is nonzero; linearity then reduces injectivity to this
zero-kernel assertion. This explains the target's hypotheses and is not
a proof supplied by this module.

The imported map was constructed by Workers 796, 430, 435 and 373. Its
specified-surjection transport predecessor retains its own provenance,
including Workers 373 and 430. Those imports are used unchanged and do
not constitute new coauthorship of this statement. The target is not
presented as a literal theorem of Silberger.

This proposition asserts no surjectivity of the map between Hom spaces,
reverse dimension inequality, analytic reflection, continuation, or parent
relative comparison. Its publication as a statement does not establish
any of those conclusions or prove injectivity.
