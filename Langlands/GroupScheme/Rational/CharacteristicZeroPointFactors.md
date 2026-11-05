# Torus and additive factors of rational points in characteristic zero

This is an internal application of the actual torus-vector extension
splitting, the vector-group line through a rational point, and the
published nilpotent and unipotent structure results. It supplies the
characteristic-zero connected commutative case of the host factorization
task. All groups and homomorphisms are actual group schemes over the
original field, with the existing `rationalPoints.map` convention.

First, `TorusVectorExtension.exists_point_factors_of_vector_quotient`
works over any field. Its input is a commutative affine group scheme
`E`, a specified closed central torus inclusion `z : Z ⟶ E`, and an
actual fppf quotient `p : E ⟶ Q` with kernel `range z`, where `Q` has
natural vector coordinates of finite dimension. For every rational point
`x`, it returns a point `t` of the specified torus and an actual
homomorphism `φ : Ga ⟶ E` such that `x = z(t) * φ(1)`.
The parameter is literally the inverse of the standard vector coordinate
map applied to the constant coordinate one.

Choose the original-field torus retraction `r` and complementary quotient
section `s` from `exists_split_of_vector_quotient`. Their identity
`p ≫ s = id / (r ≫ z)` gives
`s(p(x)) = x / z(r(x))` on rational points. A vector-group line
`ψ : Ga ⟶ Q` takes coordinate one to `p(x)`. Set `t = r(x)` and
`φ = ψ ≫ s`. The identity and commutativity of `E` give the required
factorization.

The theorem `characteristicZeroPointFactors` assumes a characteristic-zero
field `k : Type u` and a smooth connected commutative affine group scheme
`C`. Its conclusion provides an actual torus `T`, closed inclusion
`i : T ⟶ C`, rational point `t` of `T`, and actual homomorphism
`φ : Ga ⟶ C`, with `x = i(t) * φ(1)` for the given point `x`.
Thus this case needs exponent one.
`CommutativePointFactorData` packages the actual factors and their proved
properties, and `characteristicZeroPointFactorData` chooses these data from
the existence theorem.

Commutativity gives geometric nilpotence. Choose the central maximal torus
and its actual smooth connected affine quotient using
`IsNilpotentGroupScheme.centralTorusQuotient`. Every commutator of `C` is
trivial, so fpqc quotient commutator descent proves commutativity of the
quotient on every scheme test. The published nilpotent no-torus theorem
makes this quotient unipotent. A characteristic-zero field is perfect,
so `perfectFieldUnipotentSplit` supplies a finite represented split
series. The characteristic-zero commutative split-series classification
gives actual natural vector coordinates. The first theorem now supplies
the factors inside `C`.

The result retains arbitrary universe `u` and does not assume that the
original torus is split. The positive-characteristic reduction and the
passage from a general ambient point to a connected commutative envelope
are separate parts of the host theorem.
