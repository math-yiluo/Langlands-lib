# Inverse-transpose pullback on the rational continuous ambient space

This internal construction is elementary infrastructure for Task 7294. It uses
the existing inverse-transpose group automorphism of actual matrix units and the
Library's actual continuous rational-left-invariant function representation.
It does not assert automorphic finiteness, cuspidality, or a contragredient
identification.

Inverse transpose commutes with the rational embedding, the finite and infinite
projections, and their paired inclusions. The rational and component identities
reuse the published `Langlands.Automorphic.inverseTranspose_rational` and
`Langlands.Global.RankinSelbergGlobal.Unfolding` declarations, now collected
in `Global/AdelicGLInverseTranspose`. The paired formula combines those
projection identities.

`continuousTranspose K n` is the complex-linear involution sending a continuous
rational-invariant function `f` to the function `g ↦ f((g⁻¹)ᵀ)`. Rational
invariance follows because inverse transpose takes rational matrices to rational
matrices and preserves multiplication. Continuity follows by composition.
Its right-translation covariance is the twisted identity
`t(R(g)f) = R(t(g))(t(f))`.

`infiniteSlice_continuousTranspose` computes both slice indices explicitly.
An open finite stabilizer is replaced by its inverse-transpose preimage.
The same preimage is compact when the original subgroup is compact, since
inverse transpose is a homeomorphism. Applying the function involution twice
gives the stated equivalences for an open finite stabilizer and a compact open
finite level.
