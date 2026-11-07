# The size of nonzero summands in an actual smooth coproduct

Worker 1751. This is internal universe infrastructure for actual smooth
coproducts. Its index universe is independent of its representation carrier
universe.

`Cofan.restrictIndices` keeps a supplied cofan's vertex and retains precisely
the legs whose indices satisfy the given predicate. The two accompanying
colimit constructions prove that removing or adding zero objects preserves
the coproduct universal property. To remove them, extend a proposed restricted
cofan by zero legs and apply the original universal property. To add them
back, restrict the proposed cofan and use uniqueness of morphisms out of each
omitted zero object.

`SmoothRep.isZero_iff_subsingleton` compares the categorical and actual carrier
notions of zero. `nonzeroSummandIndex_small` then proves that the subtype of
indices with nontrivial summands is small in the vertex's carrier universe.
Choose one nonzero vector in each such summand. Send it into the vertex by
actual summation. Injectivity of the published actual direct-sum summation map
and the component projections show that these chosen images are pairwise
distinct. Thus these indices inject into the vertex's actual carrier.

`mapCofanIsColimit_of_carrierCoproducts` applies this size bound to a supplied
colimiting cofan. Restrict to its nonzero summands and shrink that index type to
the carrier universe. A functor preserving coproducts of this size preserves
the restricted cofan. If it also preserves zero morphisms, it sends the omitted
zero objects to zero objects. Adding them back proves that the full mapped
cofan is a coproduct, with the actual image vertex and mapped original legs.

This result makes no claim that arbitrary large coproducts exist in a fixed
carrier category. It transports any supplied actual coproduct cofan. It does
not assume finite support or representation admissibility, finite dimension,
finite type or finite length, and it does not prove a representation-theoretic
decomposition or compact-compression stability.
