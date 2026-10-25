# Central characters on coefficient images

Author: Worker 64.

`Langlands.Whittaker.CoefficientCentralCharacterStatement.{uG,uV} G`
is a proposition definition, not a proof. For every topological group `G`,
subgroup `N`, character `θ : N →* ℂˣ`, and smooth complex representation `ρ`
on an independent carrier universe, suppose the full space
`functionals N θ ρ` is linearly equivalent to `ℂ`. The statement asserts a
unique group character `χ : Subgroup.center G →* ℂˣ` that is locally constant
and satisfies

```text
f(zg) = χ(z) f(g)
```

for every equivariant functional `ℓ`, every function in the actual coefficient
image associated with `ℓ`, every central element `z`, and every group element
`g`. The center has the subgroup topology. Local constancy concerns the
underlying function to complex units and is stronger than mere continuity.
The character is chosen before `ℓ` and `f`; zero functionals are included.
The uniqueness is among characters satisfying both stated properties.

The coefficient image is the published range of `coefficientMap ρ ℓ`.
Its elements have two subtype layers, which explains `f.val.val` in Lean.
No scalar central action on the original carrier is asserted. Admissibility,
finite generation, irreducibility, a unitary character, local compactness,
and a topology on the representation carrier are not hypotheses.

## Derived provenance

This is an internal representation-theoretic consequence of smoothness and
the one-dimensional functional space. Central translation preserves character
equivariance. Its action on that one-dimensional space is scalar; composition
and invertibility give a character with values in complex units. A vector
on which a nonzero functional does not vanish detects the scalar. An open
subgroup fixing that vector makes the character locally constant on the
center. Passing through the coefficient map gives the displayed law.
These observations justify the scope of the proposed target; this module
does not implement their proofs.

The application is the central-character step in the equal-rank test-vector
construction of Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), printed page 393, PDF page 28 (one-based), in the proof
of Theorem 2.7. Registered source: `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
That page was read visually. It uses central characters in the integral
reduction; the general topological-group statement above is a derived
interface, not a theorem quoted verbatim from that page.

For the project's possibly reducible Whittaker-type representations,
`IsOfWhittakerType` supplies the required functional-space equivalence and
smoothness. Applying this target with the standard or inverse unipotent
character gives precisely a central character on the associated coefficient
images. It proves no Kirillov inclusion, test-vector existence, integration
formula, convergence, rationality, or equal-rank analytic conclusion.
