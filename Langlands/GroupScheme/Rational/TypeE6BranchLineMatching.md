# Geometric matching of rational branch lines in type E₆

Let two affine, locally finite-type, simply connected E₆ forms have actual Tits
indices over a field whose separable closure is algebraically closed. If both
short-arm vertices are distinguished, `exists_matching_typeE6BranchLines`
corrects a specified isomorphism over the separable closure by inner conjugation
in the target to match the two rational branch cocharacters. The construction
compares the split pinnings, transports the Cartan numbering to the target across
the based root-datum equivalence, and applies the primitive cocharacter
construction to both indices. The marking hypothesis on the target applies to
every E₆ numbering of its index.

`TypeE6BranchCentralizerCocycle` records a cocharacter of the original maximal
split torus whose geometric image is the integral branch coweight. It retains
the actual closed embedding of the multiplicative group, a closed representative
of its centralizer, and a centralizer-valued cocycle. On each pair of cover maps
from any test scheme, the image of this cocycle under the centralizer inclusion
equals the refined original cocycle twisted by the specified cochain.

`exists_typeE6BranchCentralizerCocycle` starts with a cocycle on a finite
Galois cover of a totally complex number field for an affine, locally finite-type,
simply connected absolutely almost-simple group with an actual numbered E₆
Tits index. It assumes that the short-arm vertex is distinguished for every
such group over a totally complex number field. It constructs the pure twist of
the original group and transports simple connectedness and absolute
almost-simplicity through the geometric isomorphism. Inner conjugation matches
the chosen branch line with its counterpart in the twist.
`LocalGroupIso.exists_finiteGalois_cocharacterMatching`
then descends the conjugating point and the matching equation to a finite Galois
refinement of the original cover. On that refinement the corrected discrepancy
fixes the branch line pointwise, so it lifts to a cocycle of the actual centralizer.

`exists_typeE6BranchCentralizerCocycle_of_marked_twist` gives the same
factorization starting with a supplied pure twist and marking proofs for its
index and the source index. This form applies when isotropy has been established
for the particular twist.

This is the cocharacter-matching step in Platonov and Rapinchuk, *Algebraic
Groups and Number Theory*, §6.8, printed pp. 382–383 and 385.
