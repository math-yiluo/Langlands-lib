# The actual rational source map in the literal Levi family

This internal adapter continues `RationalSourceJacquet` without changing its
structural inputs. It retains every field, the given affine ambient group
scheme, the supplied point Weyl comparisons and Coxeter system, both all-test
twisted-intersection properties, every minimum point representative, and every
normalizer lift of that representative. It requires no global finiteness of the
simple-root labels and makes no assumption that the root system is nonempty.

`pointSourceLeviIdentity` identifies the actual source intersection Levi with
the ambient standard Levi indexed by the literal `leviIndex J` of
`intersectionLeviIndex`. It combines the point-source identity with the exact
finite-label identity. `pointSourceLeviInclusion` then derives inclusion of
that ambient Levi in `L_J` from the intersection definition. No separate
standard-parabolic-order input is needed.

With the canonical rational-point evaluation topology, local compactness,
nonarchimedeanness, closed standard Levis and radicals, and the literal
inside-Levi compact-limit and Jacquet finite-length premises,
`pointStandardizedSourceJacquetK0` constructs the actual source Jacquet map
followed by identity conjugation to the identified standard Levi. Its carrier
universe is exactly `max (u + 1) v`, with independent `u` and `v`, and its domain
and codomain are the full exact finite-length Grothendieck groups.

`pointStandardizedSourceJacquetK0_eq` identifies this complete integer-linear
map with the literal inside-Levi `jacquetK0` map at `intersectionLeviIndex`,
followed by the pullback from the subgroupOf Levi to the ambient standard Levi.
Its proof specializes `geometricSourceJacquetK0OfEq`. The restricted radical
identity comes from the same point-source transport, the decomposition comes
from the literal standard family, finite-length preservation is the displayed
restricted Jacquet premise, and short-exact preservation follows from
`jacquetFunctor_preservesShortExact` and the compact-limit premise. The actual
source preservation witnesses are already derived in `RationalSourceJacquet`;
proof irrelevance identifies them with the generic comparison witnesses.

All provenance is internal, through the named published definitions and the
source reduction just described. Neither structural twisted-intersection
property is proved here. The final rational-point Aubert induction equation,
target induction comparison, stages, Weyl conjugacy and geometric expansion
remain separate proof obligations. This adapter adds no premise to the final
target and uses no local-field, Hausdorff or induction-preservation premise.
