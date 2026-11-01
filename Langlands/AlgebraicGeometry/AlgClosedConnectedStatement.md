# Connected schemes over an algebraically closed field

`Langlands.AlgebraicGeometry.AlgClosedConnectedStatement` says that for every
algebraically closed field `K : Type u`, every scheme `X : Scheme.{u}`, and every
structure morphism `f : X ⟶ Spec K` locally of finite type, connectedness of `X`
implies Mathlib's `GeometricallyConnected f`.

Here connectedness includes nonemptiness. Geometric connectedness means that
every fibre after arbitrary scheme base change is connected; Mathlib's
field-extension criterion reduces this conclusion to connectedness of
`X ×_K Spec L` for every field extension represented by a morphism
`Spec L ⟶ Spec K`. The statement uses actual schemes and their Zariski topologies.
It assumes no properness, reducedness, smoothness, or characteristic restriction.

This is an internally derived geometric comparison. Its route uses the
following facts from the pinned Mathlib: a locally finite type scheme over a
field is Jacobson; closed points over an algebraically closed field are
rational; and a field-extension projection is open and surjective. For an
open surjection to a connected Jacobson space, preconnected inverse images
of closed points imply connectedness of the source: intersecting open images
contain a closed point, and its inverse image rules out a separation.
The inverse image of a rational point under this projection is isomorphic
to the spectrum of the extension field and is connected.

The Lean file only defines this proposition. A separate proof contribution
must establish it. This comparison is useful for packaging a connected
smooth proper closed subgroup as an abelian scheme. It asserts no torsion
cardinality, dimension comparison, or torsion density.
