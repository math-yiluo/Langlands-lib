# Actual root groups in different Cartan components commute

For a supplied `RootComponentCoordinates M`, this internal module defines the
actual roots of a chosen component on any supplied field-valued fibre of the
pinned model. These sets are nonempty and are contained in the actual roots;
together they cover the actual roots.

Root groups belonging to distinct components commute on every scheme over
the supplied field. The proof transports the integer exclusion of mixed
roots through the actual coordinate character equivalence. Every strict
positive combination of characters from different components is neither zero
nor an ambient root. The published all-test root-group commutation theorem
for that condition applies. Therefore each component root set is a commuting
partition in the existing `IsCommutingRootPartition` sense.

All root groups and field pullbacks here are the actual Library constructions.
The module is internally derived from the component-coordinate support and
mixed-root theorem, the fibrewise root datum of the pinned model and the
published strict-combination commutation theorem. It prepares factor
commutation in the proof route motivated by Conrad, *Reductive group schemes*
(2014), Proposition 6.4.4, pp.232–233. It does not assert that the relative
derived-centralizer groups themselves commute or form a product.
