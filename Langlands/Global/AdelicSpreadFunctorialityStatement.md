# Functoriality of adelic points with independently chosen arithmetic spreads

`AdelicSpreadFunctorialityStatement` is the conjunction of
`CurvePlaceSpreadFunctorialityStatement` and
`NumberFieldSpreadFunctorialityStatement`. It states that postcomposition
by an arbitrary morphism of schemes over the original field is continuous
on their actual full-adele points, equipped with the topologies from any
two specified finite-type arithmetic spreads.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), printed p.6 following (3.5.1), and printed p.9,
the opening of section 4. These passages assert functoriality of the
adelization and its topology in the finite-type field-scheme. This target
expresses continuity using the actual point carriers and explicit
specified-spread topologies. It is a proposition interface, not its proof.

In the function-field clause the constants are an arbitrary perfect field
`k`, and `F` has the specified compatible `k`–`RatFunc k` scalar tower and
`FunctionField k F` instance. The two finite sets `S` and `U` consist of
actual curve places. The models `X` and `Z` are schemes over their actual
outside-set integer rings. The specified isomorphisms identify their
actual pullback generic fibers with the original `F`-schemes `Y` and `W`.
The induced map is literally `p ↦ p ≫ g`, between morphisms over
`Spec F` from the spectrum of the actual full curve-place adele ring.

The number-field clause uses an arbitrary number field `K`, its actual
outside-set integer rings, and the actual full ring `Adeles K`.
Every infinite factor is retained; indexing the two sets by finite places
does not remove those factors. The point map is again actual
postcomposition over the original field.

Finite type is expressed by `LocallyOfFiniteType` and `QuasiCompact` on
each model's structure morphism. Neither model nor field-scheme need be
affine or separated. The morphism `g` is arbitrary: no lift to an integer
model, continuity, eventual descent, or topological comparison is supplied
as an assumption. The two finite sets need not be comparable and may be
empty. All constructions retain the original integer and field scalar
actions, and the common universe `u` is arbitrary.

Perfect constant fields and empty initial sets give a derived extension
of the source's global-field convention. For this continuity assertion,
the required arithmetic inputs are the integer-ring colimit and
Noetherianity, which give finite-presentation morphism descent for the
finite-type models, and the local product and final topologies.
Neither finite residue fields nor local compactness is needed. A proof
can enlarge both sets to their union, descend the prescribed
generic-fiber morphism to a further integer stage, apply continuity of
actual model postcomposition, and transport along initial-set
homeomorphisms. Independence of the spread topologies identifies these
topologies with those in the target.

This unit leaves its proof, existence of spreads for all finite-type
field-schemes, agreement with other point topology constructions, and the
remaining conclusions of the paper as separate obligations.
