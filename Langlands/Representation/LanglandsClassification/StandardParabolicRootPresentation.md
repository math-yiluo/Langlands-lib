# Verified root presentations for the canonical standard data

Worker 148. This internal construction verifies the existing
`ParabolicRootPresentation` interface for the original canonical standard
parabolic datum. It fixes a connected reductive group over any field, a
maximal split torus, a generic cocharacter and any subset of the actual simple
relative roots. Its remaining supplied data are an actual split component
of the canonical standard Levi and a map from that component into the fixed
torus whose composite equals the component's ambient inclusion.

`ParabolicDatum.standardRootPresentation` keeps precisely that torus,
cocharacter, subset and factor map. It does not change representatives or
conjugate the data. `standardRootPresentation_data` records the equality of
its underlying presentation data.

The proof verifies every compatibility clause. The parabolic, rational Levi
and split-component predicates come from the standard datum and the supplied
split component. The parabolic and ambient Levi range identities are the
all-test identities of the canonical standard maps. The supplied factor
identity agrees with the composite through the standard Levi-to-parabolic
map by `Standard.leviToParabolic_comp`.

The published `genericMinimalParabolic` theorem proves that the dynamic
parabolic of the original generic cocharacter is minimal. Its containment
in the chosen standard parabolic follows from the empty-index endpoint and
the published order theorem on actual standard parabolics. Finally,
`standardCocharacter` supplies a standard cocharacter that simultaneously
realizes the given standard parabolic and Levi ranges as its dynamic
parabolic and centralizer.

The provenance is internal composition of published structural theorems.
This supplies the root-presentation part of the Langlands-triplet interface
for canonical standard data. The source context is Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition,
V.3 (standard parabolics and Levis) and VII.4.1–VII.4.2, printed
pp.241–244 / PDF pp.247–250. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The construction supplies no representation, unramified parameter,
positive-part decomposition, temperedness or Langlands classification proof.
