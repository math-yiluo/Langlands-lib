# Proof of the constructed p-adic residue exact sequence

Original mathematical and Lean author: Worker 9.
Submission preparation and verification: Worker 68.

The closing theorem is `Langlands.LocalGalois.padicResidueExactness`.
Its local-field theorem `localResidueProperties` proves the entire conjunction
from `AbsoluteStatement`. The final specialization takes arbitrary \(p,F,T\),
installs the supplied \(T\), proves characteristic zero from \(F/\mathbb Q_p\),
and applies the local-field theorem. No assertion of the target is introduced
as an additional assumption.

The `Langlands.PadicField` wrappers expose the same construction for the supplied
`F` and `T`: `absoluteResidueHom_continuous`, `absoluteResidueHom_surjective`,
`absoluteResidueHom_isOpenMap`, and `absoluteResidueHom_ker`. They also expose
closedness and the inherited compact, totally disconnected inertia topology,
and `absoluteResidueQuotientEquiv` with its formula on quotient representatives.
All these wrappers install the supplied realization locally.

## Arithmetic and closure transport

The imported spectral proof supplies integrality of the constructed unit ball,
algebraic closure of its residue field, actual residue-conjugate lifting,
continuity, surjectivity, and generic inertia/quotient results. Its surjectivity
argument lifts roots of a monic integral polynomial, uses primitive elements in
finite residue extensions to obtain density in the Krull topology, and uses
compactness of the Galois group to make the image closed. A separate
classification of all unramified extensions is not used or claimed.

The local norm's unit ball equals the original valuation ring.
`closureIntegers_integral` transports the generic integral-closure characterization
through that ring equivalence. Spectral-norm invariance gives invariance of the
constructed valuation under all absolute Galois automorphisms.

The residue-closure comparison is compatible with original integral elements by
reducing the actual integer-ring inclusion. Transport of the residue algebra
gives a \(k\)-algebra equivalence to `AlgebraicClosure k`; integrality transported
through that equivalence and the proved algebraic closedness show
`IsAlgClosure k` for the residue field of the closure.

## Krull topology and inertia

`semilinearAutCongr_continuous` proves continuity of change of closure
presentation. For a finite target intermediate field, it pulls a finite vector
space basis back through the closure equivalence. The intersection of its
finitely many open point stabilizers maps into the required fixing subgroup.
Compactness of the residue Galois group and Hausdorffness of the chosen absolute
Galois group make this continuous equivalence a homeomorphism.

Composition with this equivalence preserves continuity, surjectivity and
openness of the generic residue homomorphism. Checking an integral residue
representative proves the displayed action formula. Injectivity of the
conjugation equivalence identifies its kernel with generic inertia.
The generic residue-representative characterization identifies that subgroup
with field-theoretic inertia and with Mathlib's valuation-subring inertia.
Closedness, compactness, total disconnectedness and Hausdorffness are transferred
using the same inherited subgroup topology.

The generic topological quotient equivalence is composed with the proved closure
transport. Its value on every quotient representative is the constructed
absolute residue homomorphism, as required by the exact target.

Finally, equality of spectral norms in a tower gives the local inclusion of
integer rings. On residue representatives, restriction of field automorphisms
commutes with this inclusion; conjugating by the same closure comparison gives
the target's finite-level compatibility, in fact for every normal intermediate
field.

The proof imports `Langlands.Galois.Local.AbsoluteStatement`, which imports
`Langlands.Galois.Local.AbsoluteDefinitions` and its published spectral and
local-field dependencies. Its full target is the Library proposition
`Langlands.LocalGalois.PadicResidueExactness`, which a proof submission names
in `statement_declaration`. Compilation of a development copy does not
establish independent proof acceptance. Acceptance requires the Lake build,
exact-target inspection, independent semantic review and publication.

The source context is Serre, *Local Fields*, Greenberg English translation,
Springer GTM 67 (1979), registered literature ID `serre-1979-local-fields`
(SHA-256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):
Chapter I, section 7, Propositions 20–22 and the inertia definition, printed
pp. 20–23 (PDF 28–31); Chapter II, section 2, Proposition 3 and
Corollaries 2–3, pp. 28–29 (PDF 36–37); Chapter III, section 5, Theorems 2–3
and Corollaries 1–3, pp. 54–55 (PDF 61–62).
Those finite valuation and residue-lifting results explain the mathematical
meaning. This proof description follows the implemented derived
infinite-extension argument, including its compactness route.
