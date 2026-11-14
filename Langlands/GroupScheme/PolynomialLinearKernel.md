# Scheme retracts for kernels with linear coordinates

Work over an arbitrary field `k : Type u`, with finite index types `I` and
`J`. Let `q : G ⟶ H` be a homomorphism of actual group schemes over `k`.
For every relative test scheme `T`, assume set equivalences

```
e T : (T ⟶ G.X) ≃ (I → Γ(T.left, ⊤))
d T : (T ⟶ H.X) ≃ (J → Γ(T.left, ⊤)).
```

The source equivalences `e` commute with pullback along every morphism of
test schemes. The target equivalences send the identity point to zero.
Assume a matrix `M : Matrix J I k` gives the original homomorphism in these
coordinates on every test scheme:

```
d T (x ≫ q.hom.hom) = M.map (scalarMap T) *ᵥ e T x.
```

No compatibility of `e` or `d` with addition of coordinate arrays is
required. In particular, this construction allows polynomial coordinates
of a noncommutative group whose group law has a bilinear correction.

`PolynomialLinearKernel.smooth_connected_kernel` proves that the actual
scheme-theoretic kernel is smooth and connected when the source is affine,
smooth and connected and the target is separated. `properties` additionally
proves `IsUnipotent (kernel q)` when the source is locally of finite type
and unipotent in the Library's representation-theoretic sense. All
conclusions concern the actual pullback kernel and retain arbitrary
universe `u` and arbitrary characteristic. Empty coordinate index types
are allowed.

The proof first establishes `exists_innerInverse`: every finite matrix
over a field has a matrix `N` with `M * N * M = M`. It splits the surjection
onto the range of the corresponding linear map and extends that section
from the range to the whole target. For every `k`-algebra the formula

```
project M N φ x = x - N.map φ *ᵥ (M.map φ *ᵥ x)
```

defines a projection onto the matrix kernel. Matrix identities prove that
it is killed by `M`, fixes every vector killed by `M`, and commutes with
all algebra maps.

Evaluate this projection at the universal source point to construct the
underlying scheme morphism `projection`. Source-coordinate naturality
computes its action on all test schemes. The target-coordinate formula
and its identity normalization show that its composite with `q` is the
identity point. The actual pullback universal property therefore gives
`retraction : G.X ⟶ (kernel q).X`. The equality `ι_retraction` proves that
this morphism is the identity after restricting to the actual kernel.
It is a retraction of schemes; no claim that it preserves the group law
is needed.

The source and the kernel are affine, the latter because the target is
separated. The published `AffineRetractGeometry.smooth_of_retract` and
`connectedSpace_of_retract` establish smoothness and connectedness. The
kernel inclusion is a closed immersion, so the published
`unipotentClosedSubgroup` theorem supplies unipotence from that of the
source.

This is a derived linear-algebra and scheme-retract construction, not a
literal statement of Kaletha–Prasad. Its intended use is the special-fibre
kernel calculation motivating KP Lemma C.5.3 (printed p.705, PDF p.736),
after the restriction-of-scalars assembly in Proposition C.5.1 (printed
pp.703–704, PDF pp.734–735). The present module does not supply the matrix
formula for a particular restricted bilinear map or identify supplied
root-depth models. Those comparisons remain obligations of the C.5.3
proof. It does not use the host KP Proposition 8.4.15 kernel theorem.
