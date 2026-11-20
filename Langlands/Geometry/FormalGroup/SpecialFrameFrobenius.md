# Global rational inversion of relative Frobenius

`Langlands.FormalGroup.LocalDivision.SpecialModule.relativeFrobeniusQuasiIsogeny`
proves `RelativeFrobeniusQuasiIsogenyStatement` for every supplied height-certified
special formal frame and every scalar-compatible Frobenius iterate.

The proof evaluates the existing relative Frobenius on nilpotent tuples. It acts
by taking the `p^n`-th power in each coordinate. To lift a target tuple, the proof
adjoins a root of this degree for each coordinate by successive monic polynomial
quotients. Each quotient is finite free on a nonempty power basis and is finitely
presented. The adjoined roots are nilpotent because their powers are nilpotent.

The universal point of the truncated polynomial algebra with `p^n`-th coordinate
powers zero is killed by a common scalar power `π^j`, by the torsion clause of the
frame's height certificate. Every Frobenius kernel point is the image of this
point, so the same `π^j` kills every such kernel point. Faithfully flat descent and
reconstruction of formal maps give an integral map `g` from the twist back to
the frame whose composite with Frobenius is `[π^j]`. Cancellation against the
locally surjective Frobenius gives the other integral scalar composite.

In the global tensor Hom, the proof multiplies the rationalization of `g` by
`π^(-j)` in `K`. Bilinear composition turns both integral equations into inverse
equations against the original Frobenius tensor. The full-order quasi-isogeny
constructor uses the forward map's order equivariance to give the inverse its
order equivariance and retain both global inverse equations. The forward tensor
is exactly the rationalization of the published integral relative Frobenius.

This is the fixed-frame tensor inverse used toward the natural Frobenius
quasi-isogeny in Drinfel'd, *Coverings of p-adic symmetric regions* (1976),
§2 A, printed p. 109. The factorization and tensor calculation are internal to
the formal-coordinate model and use only positivity of `p^n`, including when
that exponent is one. The finite root construction begins with the identity
cover for an empty coordinate set.
