# The factor set of the middle exterior lifts

Let `M/F` be a field extension, let `H` be a subgroup of its automorphism
group, and let `P_g` be invertible `2m` by `2m` matrices over `M`.
Write `Λ` for the degree-`m` exterior action in the ordered subset basis,
and `J` for the matrix of the wedge pairing with the standard volume
coordinate. The construction `middleExteriorLift` takes `Q_g = Λ(P_g)`
for `g ∈ H` and `Q_g = Λ(P_g) J` otherwise.

The minor formula gives `Λ(Y⁻ᵀ) = Λ(Y)⁻ᵀ`, and multilinearity gives
`Λ(a I) = a^m I`. The wedge similitude identity gives
`J Λ(Y) = det(Y) Λ(Y⁻ᵀ) J`. The square of `J` is `(-1)^m I` and each
coefficient automorphism fixes `J`.

Suppose membership in `H` assigns a parity to the product `gh`, meaning
that `gh ∈ H` exactly when `g` and `h` have the same membership. Suppose
also that `P_g (g ⋆ P_h) = c(g,h) P_{gh}`, where `g ⋆ P_h` is `g(P_h)` for
`g ∈ H` and `g(P_h)⁻ᵀ` otherwise. The theorem `middleExteriorLift_mul`
computes `Q_g g(Q_h)` by applying `Λ` to this identity. If `g` is outside
`H`, moving `J` past `Λ(g(P_h))` contributes `g(det P_h)`. If both elements
are outside `H`, the product of the two copies of `J` contributes
`(-1)^m`. Thus for `ε(g) = 0` on `H` and `ε(g) = 1` outside `H`, the
scalar in `Q_g g(Q_h) = μ(g,h) Q_{gh}` is

\[
\mu(g,h)=c(g,h)^m\,g(\det P_h)^{\epsilon(g)}
                    (-1)^{m\epsilon(g)\epsilon(h)} .
\]

This scalar is `UnitaryDiscriminant.detCocycle H P c m g h`. For a unitary
involution one takes `H` to fix the quadratic center. The construction of
the discriminant algebra in Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions* (1998), (10.28), gives the same line of lifts
using `Jᵀ` in the outer branch. Replacing `Jᵀ` by `J` multiplies each
outer lift by the constant sign `(-1)^m`. This sign is fixed by coefficient
automorphisms and the parity rule makes its coboundary trivial.
The wedge pairing and the complementary signs come from (10.6) and
(10.25), printed pp. 117 and 126. The discriminant construction is on
printed pp. 127–128, and the middle weight interpretation is in §27.B,
printed p. 378.
