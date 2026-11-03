# Proper-pullback and covering-trace operators with full smooth coefficients

This internal construction composes the existing proper equivariant pullback with the existing finite-covering trace on the entire compact-support locally constant function modules. Its finite-sum identities come from the paired topology `Correspondence` module. No external cohomological comparison theorem is invoked.

The topological spaces `S`, `X`, `Y`, `Z` share universe `uX`. The topological group, commutative coefficient ring, and smooth coefficient carriers have independent universes `uG`, `uR`, `uV`. Each space carries a continuous action of the original full group. The coefficient category is the existing `SmoothRep R G`, with every original smooth representation and every equivariant linear map; no topology is placed on coefficient carriers.

The functor `coefficientFunctor (X := X)` takes a smooth coefficient representation to all compactly supported locally constant functions on `X`, carrying the original diagonal action `g·f(x) = g·f(g⁻¹·x)`. The underlying function carrier has universe `max uX uV`. `smoothPullback_naturality` proves that proper precomposition commutes with every coefficient morphism, by evaluation. `pullbackNatTrans` assembles these morphisms on the full coefficient category.

For an equivariant continuous proper map `a : S → X` and an equivariant covering map `b : S → Y` with finite actual fibers, `correspondence` is the composite

```text
C_c(X,A) --a*--> C_c(S,A) --b_!--> C_c(Y,A).
```

`correspondence_apply` identifies its value at `y` with the literal finite sum `fiberSum b (f ∘ a) y`. Compact support, linearity and equivariance are inherited from the two already constructed maps. The covering trace uses the full actual fibers, permits empty fibers, and is unnormalized. Properness is required for `a`; no properness of `b` or separation property of the spaces is assumed.

`correspondence_naturality` is the naturality of the composite of the pullback and trace transformations. `correspondenceNatTrans` and its application formula package the same operator for all smooth coefficients. `correspondence_id` uses the actual singleton identity fiber; its finite-fiber instance is explicit and can be supplied by `finite_id_fiber`. `correspondence_self_apply` proves multiplication by the actual fiber cardinal for a map which is both proper and covering, by the topology degree law.

For an actual `IsPullback` square of the four underlying original maps, `smoothTrace_baseChange` proves the morphism equality

```text
a* ≫ b_! = q_! ≫ p*.
```

Here `a` and `p` are continuous proper maps, `b` and `q` are covering maps with finite fibers, and all four maps are equivariant. The proof evaluates on every compactly supported function and uses the actual cartesian fiber equivalence. `traceNatTrans_baseChange` proves the same equality on the full coefficient functors, by componentwise equality. No desired trace-compatibility equation is an input. Properness and the covering predicates of the actual maps remain explicit; this file does not assert their automatic stability under base change.

These are ordinary-open compact-function constructions. Higher sheaf or etale cohomology, Godement trace, analytic realization, and specialization to actual Harris or Shimura Hecke correspondences remain separate obligations.
