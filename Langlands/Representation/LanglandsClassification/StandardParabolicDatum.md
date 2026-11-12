# Canonical standard parabolics as actual parabolic data

Worker 148. This internal construction bundles existing canonical standard
group schemes as `ParabolicDatum`, for use with actual Jacquet exponents in
Renard VII.4.2. It assumes a connected reductive group over a field, a maximal
split torus and a generic cocharacter, and treats every subset of the actual
simple relative roots.

`Standard.parabolicStructure` proves the structural clauses for the existing
maps `Standard.parabolicHom`, `Standard.leviToParabolic` and
`Standard.unipotentToParabolic`: geometric parabolicity, the rational Levi
predicate, the full geometric radical predicate and the Levi-first
multiplication isomorphism. Its proof chooses a standard cocharacter using
`standardCocharacter`. The same theorem identifies all three choice-free
standard subgroup functors with the dynamic subgroup functors of that
cocharacter, on every test scheme.

The canonical standard maps already represent those functors. Dynamic
parabolic recognition gives parabolicity. Connected reductivity of the
standard Levi follows from `standardLeviSplitComponentStatement`. The dynamic
decomposition theorem gives the original Levi-first multiplication
isomorphism, and the dynamic geometric-radical theorem gives the full
radical property. Affineness converts this property to the rational-Levi
radical interface. Closedness of the Levi inclusion, reductivity and the
multiplication isomorphism then give the rational Levi predicate.

`ParabolicDatum.standard` uses precisely the published `Standard` schemes
and maps, together with these structural proofs. The three `range_standard`
lemmas identify its parabolic, ambient Levi and ambient radical ranges with
the existing choice-free standard functors on every test scheme.
`isIso_standard_full_p` uses the full simple-root endpoint and
`isIso_of_full_range` to prove that the original full-index inclusion is an
isomorphism.

The provenance is internal: this is a composition and packaging of published
structural theorems, preserving their actual schemes and morphisms. Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026 edition, V.3
(standard parabolics and Levis) and VII.4.2(iii), printed pp.243–244 / PDF
pp.249–250, motivate the application to the finite family of standard Jacquet
exponents. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This unit does not select split components, form the finite exponent family,
construct real-character lifts or positive parts, or prove temperedness,
exhaustion or the Langlands classification.
