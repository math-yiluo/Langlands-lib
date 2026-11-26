# Scalar extension of adelic level rings

Let \(F\) be a global field and let \(S\subseteq T\) be finite sets of
places, with \(S\) nonempty and containing every archimedean place.
For a number field the index sets record only the finite places. The
full level rings include all archimedean factors at both levels. For
a global function field all places are discrete curve places over a
finite constant field. The hypothesis that \(S\) is nonempty is explicit
in this case.

`AdelicLevelBaseChangeStatement` asserts the isomorphism of
\(\mathcal O_{F,T}\)-algebras
\[
\mathcal O_{F,T}\otimes_{\mathcal O_{F,S}}\mathbb A_{F,S}
\simeq \mathbb A_{F,T}
\]
for the actual adelic level and integer rings. The isomorphism sends
\(b\otimes a\) to the product in \(\mathbb A_{F,T}\) of the diagonal of
\(b\) and the image of \(a\) under the level inclusion. The scalar
map on the tensor product is the inclusion of the actual outside-\(S\)
integers in the outside-\(T\) integers.

The identity occurs in the paragraph following Remark 3.5 on p. 6 of
Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, registered as `conrad-2011-weil-grothendieck-adelic-points`
with SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It identifies the change of level used to define the transition maps
in (3.5.1). The formula on simple tensors specifies the canonical map
from the two inclusions in that argument.
