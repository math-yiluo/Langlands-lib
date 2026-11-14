# Big-cell gluing from local algebra points

This derived criterion strengthens the arbitrary-algebra big-cell gluing
bridge by requiring comparison isomorphisms only on commutative local
coefficient algebras. The base ring itself may be any commutative ring.

Two reductive group schemes over `Spec R` are supplied with open big-cell
maps using a common coordinate split torus, additive-group families and
two common root enumerations. For every commutative local `R`-algebra,
assume an isomorphism of their actual point groups matching the torus and
every supplied additive-group parametrization. Then the groups are
isomorphic as group schemes, with exact agreement on the common cell.
The comparisons require no naturality. Local algebras may have nilpotents;
no reducedness or field restriction is imposed.

The proof first shows that local-ring points detect morphism equality
into an affine scheme. Apply the assumed equality to the spectrum of
each structure-sheaf stalk of the source. The canonical map from that
spectrum to the source identifies the induced global-section maps with
their germs. Equality of all germs gives equality of global-section
maps, and the affine target makes this sufficient for morphism equality.

`CellGluing.cellCompatible_of_localRingPoints` uses this result on the
multiplication relation defining cell compatibility. For each local-ring
test morphism, precomposition preserves group multiplication and the
assumed local relation gives the desired equality on that test.
Reductivity over the affine base supplies affine targets in both
directions. A torus/root-matching point-group isomorphism preserves the
cell relation; its inverse supplies the reverse direction. The published
open-cell gluing theorem then provides the actual isomorphism, because
reductive groups are smooth with geometrically irreducible fibres.

Passing from arbitrary structure morphisms `Spec A → Spec R` to the
associated `R`-algebra structures uses the same identity transport as the
arbitrary-algebra bridge. The module states the complete criterion as
`LocalSplitLocalAlgebraCellIsomorphismStatement` at every universe and
proves it as `localSplitLocalAlgebraCellIsomorphism`.

This is an internal consequence of scheme-stalk testing, affine-target
extensionality, cell-coordinate identities and the existing gluing
theorem. It does not construct the comparison isomorphisms and does not
prove the unrestricted local split Isomorphism Theorem.
