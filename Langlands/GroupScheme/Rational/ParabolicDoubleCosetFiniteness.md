# Finite parabolic double cosets from rational Bruhat covering

This internal reduction constructs the surjection that transfers finiteness of a
minimal-parabolic double-coset quotient to the literal rational-point quotient
for any two parabolic subgroups. It retains rational Bruhat decomposition,
generic minimality, and rational conjugacy of minimal parabolics as explicit
hypotheses. It does not prove those propositions or the closed
`RepresentedParabolicDoubleCosetStatement`.

For a group `Γ`, subgroups `A`, `H`, `K`, and elements `x`, `y` such that
`x⁻¹ A x ≤ H` and `y⁻¹ A y ≤ K`,
`conjugateContainingDoubleCosetMap` sends `[g]` to `[x⁻¹ g y]`.
If `b = p a q` with `p,q ∈ A`, the translated elements differ by
`x⁻¹ p x ∈ H` and `y⁻¹ q y ∈ K`. This establishes well-definedness.
The class of `x g y⁻¹` maps to the class of `g`, proving surjectivity.
`finite_doubleCosets_of_conjugate_containment` then transfers finiteness.

For actual group schemes over a field, `finite_rationalBruhatDoubleCosets`
combines the canonical map from `relativeWeylGroup i` with Bruhat covering and
the published unconditional `IsConnectedReductive.finite_relativeWeylGroup`.
Only covering is needed for finiteness, although the supplied Bruhat predicate
also includes separation.

The final reduction chooses an actual maximal split torus and a generic
integral cocharacter. The generic-minimality hypothesis identifies its dynamic
parabolic as minimal. The published proof `parabolicContainsMinimalStatement`
and the supplied minimal-parabolic conjugacy move a conjugate of that same
minimal parabolic into each supplied parabolic, on every test scheme.
Evaluation on `Spec k` gives the containment assumptions for the group
construction. The two output subgroups are precisely
`(rationalPoints.map p).range` and `(rationalPoints.map q).range`.
No rational Levi, topology, perfectness, characteristic restriction, or
nonempty-root condition is used.

The mathematical provenance is the finite Weyl indexing argument underlying
Borel–Tits, *Groupes réductifs* (1965), Corollary 5.20, printed p.102 / PDF p.49,
and Renard, *Représentations des groupes réductifs p-adiques* (2026), V.4.5,
printed pp.119–120 / PDF pp.125–126. This is an internal consequence of their
Bruhat and conjugacy inputs, rather than a formal proof of those inputs.
