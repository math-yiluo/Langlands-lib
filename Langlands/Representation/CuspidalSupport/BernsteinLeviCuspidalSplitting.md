# Actual Bernstein Levi splittings from whole-category decomposition

Worker 132. Derived supporting content for Task 5419, concerning Renard
2026, VI.3.5 and VI.7.2 second Lemma, printed pp.182–183 / PDF pp.188–189
for the latter, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`BernsteinLeviCuspidalSplittingProperty` says that every smooth representation
of each literal standard Levi in a supplied actual `BernsteinStandardFamily`
has the published cuspidal/remainder splitting. Its actual Boolean coproduct
has a cuspidal true component; the false component has no nonzero cuspidal
subquotient. Cuspidality uses the exact proper-standard normalized Jacquet
tests inside that literal Levi. Carriers lie in `max uF uV`, with independent
field and carrier universes.

`bernsteinLeviCuspidalSplitting_of_wholeStatement` proves this property
conditional on the closed whole-category cuspidal decomposition statement
at that saturated carrier universe. It applies the published
`hasLeviCuspidalRemainderSplitting_of_wholeStatement`. The existing intrinsic
`bernsteinLeviStandardFamily` supplies connected reductivity and maximal
splitness for the actual Levi and torus factor, so the published unconditional
`relativeRootSystem` supplies its root-system premise. The standard
cocharacter and standard Levi intersection theorems supply the remaining
geometric premises. Closedness and ambient topology come from the supplied
family; the existing transport theorem supplies the required intrinsic
topology and transports the coproduct to the literal subgroup. Proof
irrelevance identifies its semidirect-decomposition witnesses with the
family's witnesses.

This is an internal adapter of published results for the first clause of the
second Lemma. It proves neither the whole-category decomposition premise nor
the existence of cuspidal reflectors or the complete second-Lemma target.
