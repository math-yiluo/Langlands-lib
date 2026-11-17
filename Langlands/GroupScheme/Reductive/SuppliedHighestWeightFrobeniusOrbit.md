# Frobenius orbits from supplied full simple-root coordinates

This internal construction assumes a split pinning, integral coroot span, and
a `SimpleRootCoordinateFamily` of full linked simple-root parametrizations.
It does not prove the existence of those inputs. For a supplied highest-weight
representation of weight `(q^r - 1) rho` over an infinite field of exponential
characteristic `q`, it computes the dimension of the actual Frobenius-origin
orbit of a nonzero highest vector as `(q^r)^N`, where `N` is the number of
positive roots. This is a lower bound mechanism for the independent Steinberg
proof, not the required entire-space irreducibility result.

Each full reflection-word root map is transported from the supplied family
and then lifted into the group representing the opposite dynamic unipotent
functor. On every coefficient algebra the lifted ordered chart is bijective:
its composite with the unipotent inclusion is the previously proved full
root chart, with the actual spectrum/global-section comparison on parameters.
Yoneda then gives a bijective pullback on coordinate algebras. The character
of each word factor has strictly positive pairing with the opposite rho
contraction, and the torus conjugation action scales that factor by this
character. All chart identities retain their arbitrary test-scheme meaning;
no reduction to reduced points establishes them.

Restriction to the actual unipotent representative preserves the ordered
coefficient operators. The supplied-family highest-weight endpoint theorem
makes the coefficient at the constant multi-index `q^r - 1` nonzero. The
generic ordered Frobenius cyclicity theorem therefore makes the actual
distribution orbit map injective and computes its orbit-span dimension.
Choosing a word listing every positive root once turns the word length into
`N`. A final lemma identifies this span with the whole representation if a
separately supplied upper dimension bound is known.

Only the independent torus action on the dynamic unipotent representative,
the generic Frobenius algebra, root enumeration, and the supplied-family
word-coordinate unit are reused. Canonical linked-root choices and their
existence proofs are not used. The argument never identifies a regular
dynamic subgroup as Borel or invokes the old canonical-rho Borel assembly.
This is derived internal content with no new external source claim.
