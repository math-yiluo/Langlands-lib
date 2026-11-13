# Endpoint bounds in the multisegment rank order

These internal combinatorial adapters derive Badulescu's beginning- and ending-multiset bounds
from the published containment-count rank order. Their provenance is a direct
counting argument, not an additional representation-theoretic assumption.

At each cuspidal datum rho, the number of occurrences of rho in cuspidal content
is the number of segments ending at rho plus the number containing the adjacent
two-member segment starting at rho. Segment members are distinct by the proved
integral twist-freeness theorem, so these cases partition the occurrences.
Equality of cuspidal content and the defining rank-count inequalities therefore
show that rank-lowering can only remove ending occurrences. The analogous
partition using the two-member segment ending at rho gives the same bound for
beginnings. The proof constructs its beginning as the twist of rho by minus one;
integral twist-freeness again makes the cases disjoint.

The definitions retain multiplicities. This module does not assert any MW
correctness or constituent triangularity for Langlands heads.
