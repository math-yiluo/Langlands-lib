# Source-isomorphism transport of relative adjoint quotients

This internal construction is derived from the published full-centre fppf
quotient, centre transport, reductivity transport and canonical inner-action
interfaces.

If `q : G ⟶ A` is a supplied relative adjoint quotient and `i : G' ≅ G`,
then `i.hom ≫ q` is again a supplied relative adjoint quotient, with the same
target `A`. Reductivity and the three fppf morphism properties pass through
the source isomorphism. On every relative test, membership in the new kernel
means that the image under `i` belongs to the old kernel. The old kernel is
the full scheme-theoretic centre, and centre membership is preserved and
reflected by `i`. This proves the required kernel equality on all tests.

The two canonical actions of `A` on `G'` and `G` are intertwined by `i`.
To prove this equality at an arbitrary acting point, the implementation
tests it after an fppf local lift along `i.hom ≫ q`. Both actions then
become conjugation. Preservation of multiplication and inversion by `i`
gives the equality, which the covering morphism detects.

`OuterIsomorphismScheme.precomposeAdjoint` applies the general source
precomposition constructor with this compatibility proof. It retains the
supplied Isom parameter, the class scheme and the class morphism. Its
canonical action is exactly the one associated with the source-changed
full-centre quotient. Invariance and the unique same-test adjoint difference
come from the general constructor.

All bases, parameter schemes and relative tests are arbitrary. The argument
assumes no global lift of an adjoint point to the source group and adds no
condition on the centre. It transports a supplied outer quotient; it does
not prove its independent existence.
