# Composition of finite relative local refinements

This module continues the derived refinement calculus of
[Refinement.md](Refinement.md). Its original conventions are Berkovich,
*Étale cohomology for non-Archimedean analytic spaces* (1993), §1.1,
printed pp.13–14 (PDF pp.10–11), registered as
`berkovich-1993-etale-cohomology`. The retained original is
`Berkovich--Etale cohomology for non-Archimedean analytic spaces--1993.pdf`,
SHA-256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These pages were reread for this unit; no source-specific project errata file
was found. The two results here are derived consequences of the finite
relative-neighborhood definition, rather than numbered source theorems.

`LocallyRefines.mono` enlarges the refining family and shrinks the family
being refined. It retains exactly the same finite witnesses, containments,
point memberships, and relative neighborhood statements.

`LocallyRefines.trans` composes a refinement of `τ` by `υ` with a refinement
of `υ` by `κ`. At `x ∈ U ∈ τ`, it takes the finite first witness `ξ` and a
finite second witness inside each `V ∈ ξ`. Their union is a finite family
of members of `κ`, each contained in `U` and containing `x`. Since the union
of `ξ` is a neighborhood within `U`, `nhdsWithin_le_of_mem` reduces the
required relative neighborhood statement to the union of `ξ`.
`nhdsWithin_sUnion` expresses the neighborhood filter within this finite
union as the supremum of the individual relative filters. Each second
witness union belongs to its corresponding filter and is contained in the
total witness union, giving the result.

The proofs work for arbitrary subset families on any topological space.
They do not require compactness, openness, a net, or an analytic atlas, and
all neighborhoods are relative to the indicated actual subspaces.
