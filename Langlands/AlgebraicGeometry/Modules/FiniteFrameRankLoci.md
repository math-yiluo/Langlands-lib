# Clopen rank loci from actual finite local frames

This internal module decomposes a supplied actual finite frame cover by
rank. Let `a : FiniteLocalFrames M` for a module sheaf `M` on an
arbitrary scheme `X`. The rank of a chart is the finite integer already
stored in `a`; no global constant-rank hypothesis is imposed.

The theorem `rank_eq_of_mem` proves that two charts containing the
same point have equal ranks. The germ from sections on their overlap
to the nontrivial stalk ring makes that section ring nontrivial.
The actual section frames give finite bases of the same module on
the overlap, so the existing strong-rank-condition comparison applies.

`rankOpen a n` is the union of the original chart opens whose stored
rank equals `n`. `mem_rankOpen` gives its membership criterion.
Different ranks give disjoint opens and `iSup_rankOpen` proves that
the rank opens cover `X`. The complement of one rank open is the union
of the other rank opens. Thus `rankOpen_isClopen` proves that every
rank locus is both open and closed. This construction allows empty
rank loci and does not require compactness of `X`.

`rankFrames a n` is an actual frame cover of the module pulled back
along the rank-open inclusion. Its charts are indexed by the original
charts of rank `n`; every frame index is normalized to
`ULift (Fin n)`. The construction uses the existing actual frame
pullback comparison.

The auxiliary `subopenFrame` restricts an actual finite free frame
to any smaller open. It uses its actual section basis and restriction
naturality in the generic affine-basis frame construction.
`exists_affineCover_of_rank_eq` then refines any supplied constant-rank
frame cover by affine opens with this same fixed standard finite index:
each point chooses an affine neighborhood inside one of the original
charts. Applying this to `rankFrames` gives
`exists_affineCover_rankOpen` for the actual pulled-back module on
every rank locus.

The provenance is internal. This is a decomposition and frame-cover
construction from existing actual finite frames, their section bases,
scheme germ maps, affine neighborhoods and actual pullback.
It proves no ampleness assertion and does not identify these
module pullbacks with any group scheme's cotangent sheaf.
