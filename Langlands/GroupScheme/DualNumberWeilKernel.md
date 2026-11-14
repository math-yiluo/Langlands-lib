# The epsilon kernel in an actual dual-number Weil restriction

This is a supporting construction for the final calculation in the proof of
Kaletha–Prasad, Lemma C.4.4. It works over every field `k`, in arbitrary universe
`u`, and in every characteristic.

`DualNumberWeil.groupScheme k` is the published `AffineWeil.groupScheme` applied
to the one-dimensional vector group over `DualNumber k`. Thus it is the actual
affine Weil restriction of the additive group from `k[ε]` to `k`. The local
finite and projective module instances use the underlying module `k × k`.

The tensor isomorphism `tensorEquiv` identifies `k[ε] ⊗[k] T` with
`DualNumber T`. It is tensor symmetry followed by the published
`Picard.DualNumberBaseChange.tensorEquiv`. On a pure tensor its value is
`inl t * coefficientMap (algebraMap k T) z`. The proof of naturality uses
induction on tensors and the two actual dual-number coefficients.

`affineCoordinates` then identifies the original additive-group points over
the tensor algebra with additive dual numbers over `T`, naturally for every
coefficient algebra map. `coordinates` applies this comparison to the relative
global sections of an arbitrary test scheme, using
`Corepresented.pointsEquiv`. The comparison is multiplicative for the original
group law, written using `Multiplicative` for additive coordinates.
`coordinates_comp` proves its compatibility with every scheme pullback.
No reduction to field-valued points is used.

`epsilonMap` is the scheme homomorphism recovered by `homOfPoints` from the
natural additive map `z ↦ εz` in these all-test coordinates.
`coordinates_epsilonMap` records its action. The identity
`ε(a + εb) = εa` implies `epsilonMap_eq_one_iff`: a point is annihilated
exactly when its constant coefficient vanishes. This is valid in every
commutative coefficient ring, including nonreduced ones.

The kernel used here is the published group-scheme pullback along the target
unit. `kernelPointsEquiv` first identifies its actual scheme points with the
pointwise kernel of `epsilonMap`. `epsilonKernelPointEquiv` reads the remaining
epsilon coefficient, with inverse `b ↦ εb`. `kernelCoordinates_comp` proves
naturality on all test schemes. The resulting `kernelVectorCoordinates`
witnesses `kernel_isVectorGroup` in dimension one. The induced actual
isomorphism is

```text
kernelIso : kernel (epsilonMap k) ≅ VectorGroup.groupScheme (CommRingCat.of k) 1.
```

The declarations `kernel_smooth`, `kernel_connected` and `kernel_unipotent`
apply the published geometry and all-coefficient unipotence results for groups
with natural vector coordinates.

The provenance is derived: the coordinate comparisons, Yoneda construction
and pullback identification implement the dual-number calculation in the
proof of KP Lemma C.4.4, printed pp.701–702 / PDF pp.732–733 of the 2023 book,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
There the one-step map has kernel with coordinate algebra `A[u]/(εu)` over
`A = f[ε]/(ε²)`, and restriction to `f` gives the additive line. The current
construction proves this restricted kernel calculation via its full point
functor. It does not construct the unitary integral models `X_{r,s}`, identify
their depth maps with `epsilonMap`, or prove the full root-depth kernel
statement of KP C.5.3. Those are separate remaining inputs to the host task.
