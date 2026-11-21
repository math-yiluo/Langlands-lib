# Existence of an abelian variety's Néron model over a DVR

`Langlands.AbelianScheme.NeronModelExistenceStatement` fixes a discrete
valuation ring and its fraction field. For each abelian variety over that
field, it asserts the existence of a commutative group scheme over the
ring, smooth, separated and of finite type, with the Néron mapping
property. The output includes an isomorphism of commutative group schemes
from the original variety to the actual generic fibre of the model.

## Provenance

This is Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §1.3,
printed p. 16, Corollary 2, with the group law of §1.2, printed p. 14,
Proposition 6. The extended multiplication is commutative by the Néron
mapping property's uniqueness for maps from the smooth square of the
model. The output uses the Library's `NeronModel` structure to retain the
chosen identification of the generic fibre.
