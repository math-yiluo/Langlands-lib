# Conditional unramified sharp conjugacy reduction statement

`UnramifiedSharpTorusConjugacyReductionStatement.{u}` states that four explicit
structural assertions imply the unchanged published proposition
`UnramifiedSharpTorusConjugacyStatement.{u}`. The four premises are
`MaximalSplitTorusConjugacyStatement`,
`SimplyConnectedCentralizerProductStatement`,
`QuasiSplitMaximalTorusCentralizerStatement`, and
`UnramifiedQuasiSplitStatement`, all at the same arbitrary universe `u`.
This module defines the conditional proposition and supplies no proof.

Ordinary maximal split torus conjugacy is the first input. The second is the
actual rational image-times-centralizer product for the arbitrary supplied
simply connected derived cover. The third identifies a maximal torus containing
an ambient maximal split torus with that split torus's whole centralizer in a
quasi-split group, on all test schemes. The fourth asserts quasi-splitness for
connected reductive groups over the actual `UnramifiedClosure F` of every
nonarchimedean local field `F`.

The intended internal assembly extracts a contained ambient maximal split torus
from each supplied maximally split maximal torus. The centralizer input identifies
the original torus inclusions as whole-centralizer representatives. Ordinary
conjugacy and the product decomposition then remove the centralizer factor from
the conjugating point, and uniqueness of representatives supplies the required
isomorphism of the original tori. Unramified quasi-splitness specializes this
route to the field in the target. This explanation gives the provenance of the
conditional assertion; it does not prove any of the four structural inputs.

The conclusion retains exactly the target's supplied cover, original torus
presentations and literal `simplyConnectedImage` membership. The target and
its imported pairs are unchanged. Proving this conditional proposition alone
would not complete the sharp-conjugacy task: all four premises would still
require unconditional proofs.

The motivating source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Corollary 2.3.8, printed p.81/PDF p.112, Fact 2.6.22 and Lemma 2.6.24,
printed pp.104–105/PDF pp.135–136, and Remark 2.6.25(2) on printed p.105.
It is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`. The registered
2024 corrections, `kaletha-prasad-2024-corrections`, Section 2.6, PDF pp.24–25,
add Henselian and perfect-residue hypotheses to the valued-field discussion.
The explicit field premise here concerns the actual maximal unramified extension
of a local field; no extra field hypothesis is inserted into the published target.
