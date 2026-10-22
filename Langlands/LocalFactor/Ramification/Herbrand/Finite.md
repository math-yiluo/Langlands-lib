# Herbrand functions and upper ramification of finite p-adic extensions

Worker 60 specializes the real polygon to the published lower ramification
groups in `Langlands.LocalFactor.Ramification.Galois`. The base carrier `K`
and extension carrier `F.Carrier` retain independent universes. Their
specified algebra maps form an actual tower over `Padic p`. Every prime and
every supplied `T : F.TopologicalData` is allowed.

`lowerRamificationGroupReal T K u` is precisely the existing integer group
at `Int.ceil u`. In particular, the group at -1 is the full automorphism
group and the group at zero is the kernel of its actual residue action.
These are the original maximal-ideal-power groups on `T.Integers`.
The constant extension below -1 is only an implementation convention.

`lowerGroupOrder` is their actual finite cardinality. Finiteness follows
from finite dimensionality over the intermediate base; positivity follows
because each subgroup contains the identity. `ramificationCutoff` is chosen
from the published, proved termination theorem. No cutoff or termination
certificate is a field input. Its only use in the polygon is finite support:
the proved floor formula removes it entirely.

For nonnegative `u`, `herbrandPhi_floor` gives

`phi(u) = (sum (i < floor u) |G_(i+1)| + (u-floor u)|G_(floor u+1)|)/|G_0|`.

For nonpositive `u`, phi is `u`. The real helper proves continuity, strict
monotonicity and surjectivity from the subgroup orders' intrinsic positivity.
`herbrandPsi` is the inverse of this proved order isomorphism. Both inverse
identities, continuity and strict monotonicity are proved. The explicit
`herbrandHalfLineOrderIso` restricts to Serre's domain `[-1,infinity)`.

`upperRamificationGroup T K v` is the actual lower group at `psi(v)`.
The evaluation, -1 and zero formulas, normality, decreasing behavior and
eventual triviality are proved in the construction module. In the Galois
case these are the usual upper ramification groups. As with the existing
lower construction, definitions also make sense for a nonnormal extension;
no arithmetic quotient theorem is claimed in that larger domain.

`canonicalUpperRamificationGroup` explicitly applies the published
`PadicField.canonicalTopologicalData` constructor. Thus all finite
extensions of `Q_p` admit the construction without a special existence
certificate. The supplied-data interface remains available.

Original source: Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), IV.3, Proposition 12 and the definition of psi, printed page 73
(PDF 80); definition of upper numbering and its endpoint and termination
assertions, printed page 74 (PDF 81). Lower-group interpretation is IV.1,
Lemma 1 and Proposition 1, printed pages 61–62 (PDF 68–69).
Source `serre-1979-local-fields`, file
`C:/Central-Library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Project imports are `Langlands.LocalFactor.Ramification.Galois` for the
actual lower groups and termination theorem,
`Langlands.LocalField.Canonical` for the all-fields realization, and the
paired `Herbrand.Real` helper. The lower modules and canonical constructor
are published in the current Library. Worker 40 authored the lower
construction and Worker 26 authored the canonical constructor; their
published definitions are reused unchanged through imports. Worker 60
authored the new real analysis and specialization.

The finite ramp construction is an internal implementation; its equality
with the source formula is proved. No subgroup/quotient compatibility,
Herbrand theorem, tower law, integer-value theorem, Hasse–Arf theorem,
reciprocity or conductor transport is assumed. Those arithmetic claims
belong to separate proposition families. Lake development check
`d74dd2dc-6fdc-43fc-ba46-d10580db3113` compiled both new modules with no
errors or warnings and inspected `herbrandHalfLineOrderIso` with both
independent universes `uK` and `uL`. Only `propext`, `Classical.choice`, and
`Quot.sound` occur in the inspected definition's assumptions. Independent
semantic review and publication are still required.
