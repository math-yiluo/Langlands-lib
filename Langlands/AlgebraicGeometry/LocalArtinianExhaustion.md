# The local geometric step in Artinian subscheme exhaustion

This module supplies the local target for SGA 3, Exposé IX, Lemma 6.2 (registered
source `sga3-expose-ix-gille-polo-2009`, printed pp.53–54, retained PDF pp.23–24).
The base is the spectrum of a noetherian local ring and the structure morphism
is explicitly locally of finite type, locally quasi-finite and quasi-compact.
The finite-type hypothesis follows the source convention for quasi-finite
morphisms (footnote 41 on p.53); Mathlib does not include it in
`LocallyQuasiFinite`. A nonempty directed
increasing family of actual subscheme immersions has a stage equal to the whole
scheme on the punctured base, and on each canonical infinitesimal closed-point
neighbourhood. The target asks that one stage be an isomorphism globally.

The initial helpers show that an isomorphism after base change persists along
a subscheme inclusion. A common upper stage of the punctured-base stage and
the special-fibre stage is surjective on points, because those two base loci
cover the local spectrum. A surjective immersion is closed, so this yields a
closed-immersion stage still equal to the scheme on the punctured base.

The rest of the proof, in `LocalArtinianExhaustionProof`, separates its
defining ideal from a common power of the maximal ideal and kills a later ideal
using its vanishing on that thickening. This module does not prove the full
local statement.
