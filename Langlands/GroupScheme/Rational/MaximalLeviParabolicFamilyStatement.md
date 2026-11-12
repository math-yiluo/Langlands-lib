# A separated finite family for a maximal embedded Levi

`MaximalLeviParabolicFamilyStatement` asserts the existence of a family of at
most two actual rational parabolics in a connected reductive group over an
arbitrary field. The source parabolic is proper and maximal among actual
parabolics, with its specified rational Levi `l : M ⟶ P`. Every selected
parabolic has `M` itself as its Levi, and its composite Levi embedding is
literally `l ≫ p`. Each also comes with a represented geometric unipotent
radical whose multiplication with the Levi is an isomorphism.

The selected parabolics are pairwise nonconjugate by ground-field rational
points, as subgroup functors on all test schemes. They cover, up to that
conjugacy relation, every actual rational parabolic whose embedded Levi is
identified with a conjugate of `l ≫ p` by a specified isomorphism of Levis.
Coverage imposes no condition on a choice of radical for the parabolic being
covered.

This is an internal structural consequence of
`MaximalLeviParabolicCountStatement`, motivated by Renard V.4.8 (printed p.122 /
PDF p.128) and the finite family used in VI.5.4 (printed pp.173–174 / PDF
pp.179–180). Choose the original parabolic, and a second nonconjugate member if
necessary. Three distinct members with the same embedded Levi would contradict
the actual-image count. Conjugation reduces the stated coverage to this case.
The rational Levi predicate itself supplies each selected radical.

The assertion supplies a finite family for the represented length-budget route.
It supplies no geometric filtration, orbit enumeration, representation-theoretic
detection or induction-length theorem. It does not use the VI.5.4 association
theorem or a standard-parabolic classification.
