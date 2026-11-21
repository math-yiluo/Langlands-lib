# The module topology in a p-adic tower

`padicTowerModuleTopology` proves `PadicTowerModuleTopologyStatement`.
For two `PadicField` objects over the same prime, an algebra structure
on the upper field over the lower one is supplied together with scalar
tower compatibility over \(\mathbf Q_p\). Give both carriers their
canonical topologies. The topology on the upper field is its module
topology over the lower field.

Finiteness over \(\mathbf Q_p\) gives finiteness over the lower field.
A basis over that field identifies the upper field with a finite
product of copies of the lower one. The basis equivalence and its
inverse are continuous by restriction of scalars to \(\mathbf Q_p\),
where the given topologies are module topologies. The finite product
has the lower field's module topology, so the continuous linear
equivalence transfers it to the upper field.

This is an internal consequence of the canonical `PadicField`
topologies and Mathlib's transport of module topology by a
continuous linear equivalence.
