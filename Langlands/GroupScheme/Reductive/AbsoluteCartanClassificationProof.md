# Exact absolute Cartan classification of actual groups

`Langlands.GroupScheme.absolutelyAlmostSimpleCartanClassification` proves the
published `AbsolutelyAlmostSimpleCartanClassificationStatement` at every
universe parameter `u`, with no additional premise.

For an arbitrary field, affine locally finite type group scheme, and supplied
actual Tits index, the proof applies `absolutelyAlmostSimpleFiniteCartan` to
absolute almost-simplicity. This supplies nonemptiness of the entire actual
simple-vertex type and the finite Cartan and indecomposability properties of
its original integral Cartan matrix. That bridge uses the supplied pinning
over the separable closure and its integral-to-rational root-base comparison.

Apply `Langlands.LinearAlgebra.finiteCartanClassification` directly to this
matrix. Its proof proceeds by deleting a leaf of the connected acyclic Cartan
diagram and classifying all possible leaf extensions using explicit
nonnegative integral columns and exact matrix numberings. The generic family
predicate specializes definitionally to the published actual-index predicate.

Consequently the resulting equivalence numbers all actual simple vertices
and preserves every ordered integral Cartan entry. The alternatives are
exactly A of rank at least one, B and C of rank at least two, D of rank at
least four, E6, E7, E8, F4 and G2. The proof is uniform in the field and
characteristic. It adds no marking or Galois-action assertion and uses no
local rank-one classification, local Kneser--Tits result, or downstream
exhaustion theorem.

This is an internal assembly of the actual-group bridge and the finite
matrix classification; the supporting Markdown files explain their
implemented proofs. Worker 613 supplied the bridge and assembly, and Worker
844 supplied the generic classification and its supporting modules.
