# Semilinear quotient actions with a moving reference apartment

This internal algebraic construction generalizes `SemilinearActionData` to
coefficient automorphisms that move the reference apartment. It concerns the
existing `ApartmentQuotient P`, its original quotient relation and its existing
left `H`-action. It assumes all apartment transport data; it does not construct
coefficient transport for a reductive group, a metric or finite Galois orbits.

For a homomorphism `rho : Gamma ->* MulAut H`,
`MovingSemilinearActionData P rho` specifies corrections `c_sigma : H` and
apartment functions `a_sigma : A -> A`. The corrected automorphism
`n -> c_sigma^-1 rho_sigma(n) c_sigma` preserves the given normalizer and
intertwines its action with `a_sigma`. The same corrected automorphism sends
`P x` into `P (a_sigma x)`. The identity data are normalized. For each pair
`sigma,tau`, a normalizer element `d_sigma_tau` satisfies

```
c_(sigma*tau) * d_sigma_tau = rho_sigma(c_tau) * c_sigma,
a_(sigma*tau)(x) = d_sigma_tau . a_sigma(a_tau(x)).
```

The descended representative map is

```
[(g,x)] -> [(rho_sigma(g) * c_sigma, a_sigma(x))].
```

The proof of representative independence transports a relation witness `n`
by the corrected automorphism. Its subgroup expression is the corrected
image of `g^-1 h n`, so the supplied subgroup compatibility applies. The
identity follows from normalization. For composition, the two formulas
produce representatives differing by `d_sigma_tau`; its inverse is an
explicit witness for the original quotient relation. Thus no separate
cocycle condition on the defects is needed.

`action` bundles the descended maps into one homomorphism to quotient
permutations; the inverse is the map for the inverse coefficient element.
`action_smul` proves semilinearity for the original left action, and
`action_smul_eq_iff` preserves and reflects full point fixation.

Finally `map_eq_of_normalizer` and `action_eq_of_normalizer` prove independence
of correction choices: replacing `c_sigma` by `c_sigma * n_sigma` and replacing
`a_sigma` by `n_sigma^-1 . a_sigma` gives identical quotient maps and the same
homomorphism. These are conditional algebraic facts, with provenance in the
published quotient relation and elementary group operations. They assert no
existence of such data for the maximal unramified building.

`action_isometry` supplies the metric assembly step. Assume a metric on the
same quotient for which the original `H`-action is isometric, common
translated apartments, and preservation of the distances between canonical
apartment points by each corrected apartment map. Place two quotient points
in one translated apartment. Semilinearity moves the translating element
through `rho_sigma`, the common correction `c_sigma` cancels from both
arguments of the distance, and the apartment hypothesis proves isometry.
The theorem neither constructs the metric nor assumes a stable apartment.
