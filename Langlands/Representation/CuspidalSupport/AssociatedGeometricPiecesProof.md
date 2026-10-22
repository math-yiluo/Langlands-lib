# Individual geometric pieces for associated Levis

Author: Worker 253.

This module proves the published `PadicAssociatedGeometricPiecesTheorem`
from `AssociatedGeometricPiecesStatement`. That statement is the
individual-piece reduction used in BZ77 Corollary 2.13(c), printed pp.448–449.
The theorem `padicAssociatedGeometricPieces` only assembles the three
published component theorems. For each prime `p`, `p`-adic field `F`,
compatible topological data `T` and positive rank `n`, it returns their
conjunction:

1. `associatedGeometricPieceVanishing F T n`
   (`AssociatedGeometricPieceVanishingProof`, Worker 178). For associated
   Levis and smooth quasicuspidal input, the actual normalized geometric piece
   of a minimal representative that does not conjugate the Levis vanishes.
2. `associatedGeometricPieceEquivalence F T n`
   (`AssociatedGeometricPiecesEquivalenceProof`, Worker 289). Under the same
   hypotheses, the actual geometric piece of a minimal representative that
   does conjugate the Levis is a `Representation.Equiv` to the existing
   whole-Levi `transport`.
3. `minimalWeylTransportQuasicuspidal F T n`
   (`MinimalWeylTransportProof`, Worker 253 with Worker 76). Whole-Levi
   transport along a minimal conjugating permutation preserves
   `IsLeviQuasicuspidal`.

The positivity hypothesis `0 < n` in the statement goes unused: all three
components hold in every rank. The proof keeps the quantified prime, the
actual `PadicField`, the topological data and the independent field and carrier
universes `uF` and `uV`. It adds no hypothesis to the components; their
scope, assumptions and source correspondence are documented in their own
paired Markdown.
