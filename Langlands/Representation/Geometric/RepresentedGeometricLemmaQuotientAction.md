# The actual common-Levi action on the coefficient quotient

This internal adapter uses the original target common Levi's literal inclusion
in the full orbit stabilizer. Composing it with the original source Levi
projection gives exactly the supplied conjugation map `D.e`, followed by the
original source common Levi embedding. This follows from the original ambient
conjugation identity and the section law for the original source projection.

The quotient action is the actual action on the full stabilizer coefficient's
target-kernel coinvariants, restricted along that same inclusion. Under the
explicit reverse image inclusion from `RepresentedGeometricLemmaRawQuotient`,
its class-preserving linear equivalence intertwines it with the actual
normalized source-intersection Jacquet module pulled back through `D.e`,
twisted by `sourceQuotientCorrectionCharacter`. This character is the original
source inducing half, restricted to the original common Levi, multiplied by
the inverse of the original inner source Jacquet inverse half, both transported
through the original `D.e`.

The proof checks the intertwining equation on original vector classes. It uses
the original source projection identity, the implemented quotient class
formula, and cancellation of the inner source normalization scalar. The
reverse subgroup-image inclusion remains an explicit intermediate geometric
input. This module does not identify the full target-parabolic inflation,
cancel the remaining Haar and endpoint characters, or prove the closed local
orbit comparison.

The equivalence sends each original vector class to the same class in the
source-intersection Jacquet quotient. Its naturality law ranges over every
original smooth coefficient morphism and uses the actual normalized Jacquet
functor map. That map has the same underlying localization quotient map as
the raw quotient comparison, so its existing naturality theorem proves the
displayed law. Pullback and character twisting preserve this linear map.
