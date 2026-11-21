# Filtered calculations for a simple representative

Internal tools for the proof of Bushnell–Kutzko (1993), (2.4.1)(iii), p. 65. They use the lattice-chain filtration of §1.1 rather than reproducing a separate result from the book.

`SymbolEq` requires membership of both endomorphisms in the same filtration degree and a difference in the next degree. `Shifts` requires an ambient endomorphism unit and its inverse to lie in opposite degrees. The latter implies that the unit translates the chain by the indicated integer and has exact filtration depth. The congruences respect addition in a fixed degree, multiplication, and powers and inverse of shifting units in the corresponding degrees.

When the ambient and extension chains have the same lattices as sets, the restriction of scalars preserves the filtered calculations. Over the given nonarchimedean local base field, an extension-linear map with the same symbol as an ambient shifting unit is itself a shifting unit on the extension chain. For the last assertion, each nonzero vector has a largest depth; the correction term takes that vector one lattice deeper than the ambient unit does. Thus the extension-linear map shifts vector depths exactly. It is injective, hence bijective in the finite-dimensional space supplied by the extension lattice chain.
