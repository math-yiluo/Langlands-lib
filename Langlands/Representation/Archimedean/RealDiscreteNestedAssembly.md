# Principal series on both sides of a tied real standard module

This is an internal reduction from arbitrary tied real blocks to the nested principal
series and the adjacent split principal series. The proof expands weight-zero blocks
into their two characters, which preserves the actual standard module. It groups even
center characters first, followed by the induction blocks in increasing absolute
weight and then the odd center characters. The permutations of the tied list give
intertwiners in both directions. Admissibility and compact finiteness give surjectivity
from the injections in both directions.

The donor surjection is `RealDiscreteNestedPresentation.nested_surjection`.
The receiver injection composes `RealDiscreteSplitInjection.splitInjection` along
the list, retaining all surrounding blocks at each step. The donor and receiver
have the same multiset of signed endpoint and center characters.
