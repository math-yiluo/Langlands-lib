# Exact exchange of two induction blocks by ascending-character quotient descent

This is an internal derived construction using the Library's actual real standard modules, compact-finite functions and Frobenius maps. It proves that four recurrent character swaps descend through the ascending-character quotient to an exact intertwiner between the two actual induction-block modules. It also proves the factorization and range identities for that descent.

Let `d,e : ComplexCharacterData`, with positive absolute weights `L=|d.weight|` and `M=|e.weight|`, and choose internal parities `sd,se : Fin 2`. There is no order or genericity hypothesis on the exponents. Write `u=lo d sd`, `v=hi d sd`, `x=lo e se` and `y=hi e se`, using `RealInducedPairQuotientPresentation`. The first two have exponents `d.exponent-L/2` and `d.exponent+L/2`; the second two have exponents `e.exponent-M/2` and `e.exponent+M/2`. Their internal pair parities are `L-1` and `M-1` modulo two.

The source four-character list is `X(d,e)=[u,v,x,y]` and the target is `X(e,d)=[x,y,u,v]`. `MultiplierData` supplies four sequences with symmetry classes, symmetry signs and recurrence parameters as follows. Here `pairParity` and `sigma0` are the published character-pair data.

| Sequence | Ordered target pair for its swap | Recurrence parameter |
| --- | --- | --- |
| `μ₁` | `(x,v)` | `v.exponent-x.exponent+1` |
| `μ₀` | `(x,u)` | `u.exponent-x.exponent+1` |
| `μ₂` | `(y,v)` | `v.exponent-y.exponent+1` |
| `μ₃` | `(y,u)` | `u.exponent-y.exponent+1` |

For each row, symmetry means `IsSymmetric (pairParity first second) (sigma0 first second) μ`. All eight symmetry and recurrence premises remain explicit. No existence or normalization of nonzero sequences is asserted.

The actual Frobenius composite `crossings` follows the path

`[u,v,x,y] → [u,x,v,y] → [x,u,v,y] → [x,u,y,v] → [x,y,u,v]`.

The positions are respectively one, zero, two and one. The auxiliary path uses the other middle order, passing through `[u,x,y,v]`. `middle_comm` identifies these paths by the published disjoint Frobenius commutation theorem. The helper `swap_exact` calculates the two source position exponents of a general swap, so its assumed recurrence is exactly the recurrence required by the published derivative-intertwining theorem. Composing its four instances proves `crossings_exact`, for both compact right translation and every real matrix derivative.

There are two source tail kernels to control. If the left `d` tail kills `f`, `kernel_d` applies the forward ambient tail-kernel theorem first with character `x` and then with character `y`. The intermediate collapsed list is `[x,induced (positiveData d sd),y]`. The result says that the right `d` tail kills `crossings f`. If the right `e` tail kills `f`, `kernel_e` uses the reverse ambient theorem first with character `v` and then with character `u`. Its intermediate collapsed list is `[u,induced (positiveData e se),v]`. Disjoint middle commutation puts this second calculation on the path defining `crossings`. The result says that the left `e` tail kills `crossings f`. Both arguments use the exact four recurrences in `MultiplierData`, with their surrounding character blocks retained.

`beforeDescent` composes `crossings` with the target quotient map to `KF 4 [induced e,induced d]`. The quotient presentation identifies its actual target using equality of the compact-finite function spaces, which also covers negative original weights. This composite intertwines exactly. The source kernel generators `qd` and `qe` are killed: the one-pair tail-binomial identity puts each generator in its corresponding source tail kernel; the two containments above put its crossed image in a target tail kernel; the target tail composite is therefore zero. For `qd`, disjoint commutation of the target tails is used to apply the right-tail vanishing.

Define

`swap = beforeDescent ∘ quotientSection(d,e)`.

The section is only linear. Exact intertwining of `swap` follows instead from `RealInducedPairQuotientPresentation.descend`, applied to the proved zero composites with `qd` and `qe`. That theorem uses the computed source quotient kernel and its surjectivity. Consequently `swap_descend` proves all three assertions:

- `swap : KF 4 [induced d,induced e] →ₗ[ℂ] KF 4 [induced e,induced d]` is an exact intertwiner;
- `swap ∘ quotientMap(d,e) = beforeDescent`;
- `range swap = range beforeDescent`.

`RealInducedPairAscendingExchangeStatement` universally quantifies the data, parities, four sequences, their `MultiplierData`, and both positive absolute weight assumptions, and packages precisely these three assertions. `realInducedPairAscendingExchange` proves it. This result permits zero multiplier sequences and makes no nonvanishing, injectivity, surjectivity, inverse, heavier-image or filtration claim. The zero-weight cases are outside its scope.

The provenance is internal: the argument composes the ascending quotient presentation, forward and reverse tail-kernel containments, disjoint Frobenius commutation and exact-intertwiner descent already proved in the supporting Library development. No new assertion from external literature, classification input, or unproved landing premise is used. The full unconditional `RealInducedInducedFiltrationStatement` requires further work.
