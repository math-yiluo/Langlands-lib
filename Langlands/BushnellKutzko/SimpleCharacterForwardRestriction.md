# Forward restriction within the critical bound

`simpleCharacters_restrict_forward` restricts a simple character at index `m` to an index `j ≥ m` within the level and critical bounds. For a nonterminal parameter of critical depth `r`, the defining twist uses a successor character at index `max(m, ⌊r/2⌋)`. The proof restricts that witness to index `max(j, ⌊r/2⌋)`. The high group equality identifies the test subgroup at group depth `max(j, ⌊r/2⌋) + 1`. Determinant factorization and relative normalization restrict along the subgroup inclusion. The terminal case uses the trace and determinant conditions directly.

The restriction follows from the character definitions in BK93 (3.2.1) and (3.2.3), printed pp. 98–99. The proof of (3.3.2), printed pp. 106–107, restricts the successor character to the index given by the preceding parameter's critical depth.
