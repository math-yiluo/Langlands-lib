# Root restrictions of locally quasi-finite maps over local rings

This internal derived unit proves the local core of the characteristic clause
in Conrad, *Reductive group schemes* (2014), Proposition 6.1.7. Condition 3 of
Definition 6.1.6 asks that the base be a `ℤ/pℤ`-scheme whenever a root factor is
a power `> 1` of the prime `p`. Conrad derives this from the form of the map
between root groups (Lemma 6.1.4, pp.188-189). Here the conclusion is proved over
an arbitrary local commutative ring, including nonreduced rings, for a locally
quasi-finite homomorphism and a supplied root-datum isogeny. The proof reuses
the Library's actual root restriction and its power formula from
`RelativeIsogenyRootRestriction` and `RelativeIsogenyRootPower`. It replaces the
finiteness hypothesis of `RelativeIsogenyRootUnit` by local quasi-finiteness.

## Additive-line maps (namespace `LocalSplitCell`)

These results hold over any commutative ring `R` unless stated otherwise.

- `locallyQuasiFinite_baseChangeEndomorphism`: for an `R`-algebra `A` and an
  endomorphism `f` of the additive group `𝔾ₐ` over `R` that is locally
  quasi-finite, the Library's coefficient base change `baseChangeEndomorphism A f`
  is locally quasi-finite. The base change of `f` is a pullback of `f`
  (`baseChange_map_isPullback`), and `baseChangeEndomorphism A f` differs from it
  by the isomorphisms `gaIso` on both sides.
- `not_discreteTopology_ga`: over a field `K`, the underlying space of `𝔾ₐ` is not
  discrete. The generic point `⊥` of `K[X]` specializes to the point `(X)`, and
  the two are different.
- `coefficient_ne_zero_of_locallyQuasiFinite`: over a field `K`, let `f` be a
  locally quasi-finite endomorphism of `𝔾ₐ` with `f(a) = c a ^ q` on the points
  over every test scheme. Then `c ≠ 0`. If `c = 0`, then `f` is the constant map to
  the identity. Then the fibre of `f` over one point is all of `𝔾ₐ`, but fibres of
  locally quasi-finite morphisms are discrete
  (`Scheme.Hom.isDiscrete_preimage_singleton`).
- `isUnit_coefficient_of_power_of_locallyQuasiFinite`: over any commutative ring,
  let `f` be a locally quasi-finite endomorphism of `𝔾ₐ` with
  `f(a) = c a ^ q` on every coefficient algebra. Then `c` is a unit. The previous
  lemma applies to the base change of `f` to every field, so `c` is nonzero in
  every residue field. The Library criterion
  `NaturalLine.Operation.isUnit_value_one_of_fields` then shows that `c` is a
  unit.
- `scalarOperation_add`: the operation `scalarOperation f` that `f` induces on
  every coefficient algebra is additive. This follows from `rootPoint_add`.

## The local theorem (namespace `RelativeIsogeny`)

The variables are those of the Library module `RelativeIsogenyRootUnit`:

- a local ring `R`;
- affine group schemes `G` and `H` over `Spec R` with coordinate split tori `i`
  and `j` and reduced fibrewise root data `P` and `Q`;
- a root-datum isogeny `r : RootDatumIsogeny p Q P`;
- a torus homomorphism `tau` that pulls back each exponent character `m` to
  `r.weightMap m` (`hweight`);
- a homomorphism `phi : G ⟶ H` with `i ≫ phi = tau ≫ j` (`hphi`);
- reductivity of `H` with a fibrewise maximal torus `j`;
- an index `b : J'`;
- root parametrizations `u` of `G` for `P.root (r.indexEquiv b)` and `v` of `H`
  for `Q.root b`.

Finiteness of `phi` is replaced by the instance
`[LocallyQuasiFinite phi.hom.hom.left]`.

- `rootRestriction_locallyQuasiFinite`: the Library's actual root restriction is
  locally quasi-finite. Composed with the closed immersion `v`, it equals the
  composite `u ≫ phi` (`rootRestriction_comp`), and that composite is locally
  quasi-finite. Local quasi-finiteness then cancels through the composition
  (`LocallyQuasiFinite.of_comp`).
- `isUnit_rootRestrictionCoefficient_of_locallyQuasiFinite`: the coefficient
  `c` of the Library's power formula `rootRestriction_power`,
  `a ↦ c a ^ (r.rootFactor b)`, is a unit.
- `natCast_eq_zero_of_rootFactor_ne_one`: if `r.rootFactor b ≠ 1`, then
  `(p : R) = 0`.

Proof of the last theorem. Since the root factor is a power `p ^ n` different
from `1`, `p` is prime and `n ≠ 0`. The operation of the restriction is additive
(`scalarOperation_add`). Evaluate it on the coefficient algebra `R[X][X]` at the
two variables. This gives `c (X + Y) ^ (p ^ n) = c X ^ (p ^ n) + c Y ^ (p ^ n)`
with `c` a unit. Then `natCast_prime_eq_zero_of_add_pow`
([`CommutativeAlgebra.AdditivePrimePower`](../../CommutativeAlgebra/AdditivePrimePower.md))
gives `(p : R) = 0`.
