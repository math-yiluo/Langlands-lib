# Canonical face terms with a fixed torus and positive base

This derived unit compares every actual canonical face-filtration term for
two split parabolic face charts with the same ambient coordinate torus, root
datum and positive base. Their root parametrization families, enumeration,
auxiliary regular cocharacter and original nonzero cocharacter values may
differ. The original cocharacters must have the same zero-root face: their
coordinate pairings vanish on exactly the same roots. Both families carry
the actual `IsRootParametrization` certificates. The ring is arbitrary and
the range equalities hold on all scheme tests.

`faceHeight_eq_of_simple_zero_iff` proves that the integral linear face height
on a fixed base depends only on the simple roots where the coweight vanishes.
The proof compares its values on the integral simple-root basis.
`sameBaseIndexEquiv` identifies the two actual root-index enumerations through
the common positive-root labels. `sameBase_weight_eq` then uses the charts'
exact face-weight formulas and original coordinate-pairing identities to
identify their unscaled natural weights.

`sameBase_root_range_eq` uses the two actual root-parametrization certificates:
both homomorphisms represent the same relative root subgroup of the same
ambient torus. It therefore identifies their ambient ranges without choosing
any scalar reparametrization. `range_inclusion_comp_sameBase` applies the
ambient generated-root comparison to prove equality of every filtration term's
ambient range. This eliminates the root-parametrization, ordering and regular
cocharacter choices under the stated fixed-base hypotheses.

`sameBaseTermIso` constructs the actual representative comparison at every
level; its companion theorem preserves exactly the original ambient maps.
The construction uses the monomorphic inclusions of the actual regular
dynamic groups, not an assumed comparison between the filtration terms.

Provenance is the integral simple-root basis, existing face-height and actual
root-parametrization definitions, constructed split face charts, the generated
ambient-root comparison and represented-subgroup uniqueness. Comparing
different positive bases or maximal tori and global descent remain outside
this unit's assertions.
