# Actual compact-function correspondences on induced rational spectra

This internal construction specializes proper-pullback and finite-covering-trace operators to the original `OpenSubgroupTransport` arrows and their already constructed induced maps on balanced quotient rational Banach spectra. It composes the existing `compactSupportPullback` and `compactSupportTrace`; its base-change and span-composition equalities are proved by actual fiber reindexing. It is groundwork for geometric correspondences, with no claim to instantiate Harris's etale or Shimura correspondences.

The inputs retain a complete ultrametric normed field and presented strict affinoid algebra in universe `u`, a topological group in independent universe `v`, its `RationalSpectralAction`, a commutative coefficient ring in independent universe `r`, and every smooth coefficient representation with carrier universe `w`. The entire original full-group action and all coefficient intertwiners are retained. Coefficients carry no topology. The function representation lives in universe `max u v w`.

For original transport arrows `a : S ⟶ X`, `b : S ⟶ Y`, the construction requires properness of `a.inducedMap`, the genuine covering predicate on `b.inducedMap`, and finiteness of each literal fiber of `b.inducedMap`. `compactSupportCorrespondence` is

```text
C_c(X,M) --a*--> C_c(S,M) --b_!--> C_c(Y,M).
```

Its application formula is precisely `fiberSum b.inducedMap (s ∘ a.inducedMap) y`. It sums every point in the actual fiber, permits an empty fiber, and never divides by the degree. The underlying modules are all compactly supported locally constant functions on the original induced spectra with their proved smooth diagonal actions. There is no smaller chosen coefficient category or function subspace.

`compactSupportCorrespondenceNatTrans`, its component formula, and `compactSupportCorrespondence_naturality` give this operator on the whole original coefficient functor. The identity span acts as the identity, both objectwise and naturally; the explicit identity finite-fiber instance can be supplied by the existing `finite_inducedMap_id_fiber`. A self-span with an actual proper covering map acts at `x` by multiplication by `Nat.card (a.inducedMap ⁻¹' {x})`, which may depend on `x`.

For arrows `a : S ⟶ X`, `b : S ⟶ Y`, `q : X ⟶ Z`, `p : Y ⟶ Z`, the cartesian premise is Mathlib's actual

```text
IsPullback (↾a.inducedMap) (↾b.inducedMap) (↾q.inducedMap) (↾p.inducedMap).
```

This is a universal property of the original induced spectrum maps as maps of types. A commuting labelled square alone is insufficient. `finite_inducedMap_pullback_fiber` proves finiteness of the original base-changed fibers from the topology fiber equivalence. `compactSupportTrace_baseChange` proves `a* ≫ b_! = q_! ≫ p*` by evaluating the same equivalence. The maps `a`, `p` are proper, `b`, `q` are covering with finite fibers, and these predicates are explicit. `compactSupportTraceNatTrans_baseChange` upgrades the equality to all coefficient objects and maps. No base-change equation is postulated.

For two original spans `X ← S → Y` and `Y ← T → Z`, let `e : W ⟶ S` and `f : W ⟶ T` form an actual cartesian square over the right leg `b` and the left leg `c`. `compactSupportCorrespondence_comp` proves that the composite operator equals that of the original composite span `X ← W → Z`, whose legs are `e ≫ a` and `f ≫ d`. The premises require properness of `a`, `c`, `e`, covering of `b`, `d`, `f ≫ d`, and finite fibers of `b`, `f`, `d`, `f ≫ d`. Properness of `e ≫ a` is derived from the proved proper-composition law. Finiteness of `f` and `f ≫ d` can be supplied using the pullback and composite finiteness lemmas. The proof rewrites the original induced composite maps by their existing composition formulas, uses the finite composite-fiber sum, and then the actual cartesian fiber reindexing. No separate covering property for `f` is needed in this statement because its trace is not used separately. `compactSupportCorrespondenceNatTrans_comp` gives the same equality naturally in all coefficients.

All constructions use the existing original arrows and actual balanced quotient spectra. Properness, coverings and cartesianness are not established for every rational arrow, nor is a pullback object asserted to exist in the rational transport category. Mathlib's type-level product-subtype pullback in the topology helper exhibits the general cartesian input but does not construct a rational, analytic or Shimura pullback object.

This unit acts on ordinary-open compactly supported locally constant functions. It constructs no trace on Godement resolutions or higher sheaf-derived etale cohomology, no analytic uniformization, and no actual arithmetic Hecke correspondence or Harris compatibility theorem. Those parts of the wider framework remain obligations.
