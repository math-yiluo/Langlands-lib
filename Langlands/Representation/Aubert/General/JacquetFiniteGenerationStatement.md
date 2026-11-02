# Compact-quotient finite generation for actual Jacquet restriction

`Langlands.Aubert.General.JacquetFiniteGenerationOfCompactQuotientStatement`
is the finite-generation assertion used in Renard VI.1.3, printed page 136
(PDF page 142), specialized to the published intrinsic Haar-normalized
Jacquet functor. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, the French version
dated 9 July 2026, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For actual subgroups `P`, `M`, and `U` of a locally compact nonarchimedean
group `G`, the statement assumes the published semidirect decomposition
`P = M ⋉ U`, closedness of `U`, and compactness of the actual left quotient
`Induction.LeftQuotient P`, whose elements are the classes `P g`.
Every smooth complex representation finitely generated over `ℂ[G]` then
has an actual normalized Jacquet module finitely generated over `ℂ[M]`.
The group universe `uG` and representation-carrier universe `uV` are
independent; the functor preserves `uV`.

This is an internal generalization of the source's reductive-group
formulation. The finite-generator argument uses smoothness and finitely
many double cosets `P \ G / K`, obtained from compactness of `P \ G`.
It requires no reductive structure or separate compactness of `K`.
The normalization is the published inverse half Haar-modulus character
on the actual Levi subgroup, rather than an arbitrary replacement action.

The additional compactness hypothesis is intentional in this intermediate
statement. It does not prove compactness on the rational points of a
reductive group, admissibility, Howe's criterion, or the closed
`DynamicJacquetFiniteLengthStatement`. Those remain separate inputs to
the intended finite-length proof.
