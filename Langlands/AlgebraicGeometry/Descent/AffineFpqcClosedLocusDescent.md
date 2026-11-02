# Descent of closed loci along affine fpqc covers

Author: Worker 445.

This internal construction extends the affine core of the published
`Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof` to a covering family
in any subcanonical topology, and specializes it to a single affine fpqc
cover. It imports the existing flat ideal-descent and scheme-lifting lemmas
from that module (authors Worker 766 and Worker 266). The proof does not
require that the cover be locally of finite presentation.

`descendedIdeal f I` is the intersection of the preimages of the ideals
`I l ⊆ Γ(W l, ⊤)` under `(f l).appTop`. It is an ideal of `Γ(Y, ⊤)`.

`finiteCover` takes a subcanonical Grothendieck topology `J` on schemes, an
affine scheme `Y`, a `J`-closed sieve `E` on `Y`, and a finite family of flat
morphisms `f l : W l → Y` with affine sources whose generated sieve covers
`Y` for `J`. It also takes closed immersions into the `W l` representing the
pullbacks of `E` on every test scheme. It produces a closed immersion into
`Y` representing `E` on every test scheme, without affineness or reducedness
assumptions on those tests.

The proof forms the ideal `descendedIdeal f I` for the kernel ideals of the
local closed immersions and realizes it by a quotient closed subscheme of
`Y`. The imported `tmul_one_eq_zero_of_mem_ker` obtains the ideal descent
condition by testing the shared factorization property on spectra of tensor
quotients. The imported `le_map_iInf_comap` uses flatness to show that each
local ideal is contained in the extension of the descended ideal. This proves
that a map through the descended subscheme has the required property after
pulling back to the cover; closedness of `E` gives the property globally.
In the other direction the local lifts through the descended subscheme glue
using subcanonicity, via the imported `exists_lift_of_covering`.

`affine` specializes to `Scheme.fpqcTopology` and the singleton family of a
flat surjective morphism `W → Y` between affine schemes. Such a morphism is
quasi-compact, so Mathlib's `singleton_mem_fpqcPrecoverage` gives the covering
condition. The fpqc topology is subcanonical. This specialization allows
arbitrary faithfully flat ring extensions; no finite-generation or
finite-presentation premise is introduced.

This is a supporting construction for the universal closed-factorization
locus. It assumes the local closed representative and the fpqc-closed sieve;
it does not by itself construct the coefficient charts or prove the target
`ClosedFactorizationLocusStatement`.
