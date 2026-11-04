# Kernel domination from a parametrization over a quotient

This internal construction starts with group homomorphisms `φ : D → Q`
and `q : H → Q` over any scheme `S`, and a morphism of schemes over `S`
`p : D → H` satisfying `q ∘ p = φ`. Multiplicativity or identity preservation
of `p` is not assumed. `KernelDomination.parametrization` is an actual
morphism from `D ×[S] ker(φ)` to the actual represented kernel `ker(q)`.
It sends `(d,k)` to `p(d)⁻¹ p(dk)`. The inclusion formula is proved as an
equality of morphisms of schemes over `S`, without a commutativity premise.

The auxiliary `pairMap` applies `p` to both entries of the fiber product
`D ×[Q] D`. For arbitrary schemes over `S`, it is quasi-compact whenever
`p` is quasi-compact. If in addition `p` is schematically dominant and
both maps to `Q` are flat, the induced map to `H ×[Q] H` is schematically
dominant. The proof factors it through `H ×[Q] D`; each factor is a base
change of `p`. The corresponding projection from the intermediate or
target fiber product is flat by the stated flatness of `φ` or `q`.
The categorical pullback squares are proved by pullback pasting and are
preserved when forgetting the base. Mathlib's flat-base-change theorem
for schematic dominance then applies twice.

`differenceSection q` sends a kernel point `k` to the pair `(1,k)` in
`H ×[Q] H`. Its composite with the published kernel-pair difference is
the identity. The ideal-sheaf kernel of that difference is therefore zero,
since it is contained in the kernel of its composite with this section.
Thus the difference is schematically dominant without flatness hypotheses.

`parametrization_isSchemeTheoreticallyDominant` combines the preceding
map on pairs, the published kernel-pair isomorphism for `φ`, and the
kernel-valued difference for `q`. Its hypotheses are exactly schematic
dominance and quasi-compactness of `p` and flatness of `φ` and `q`.
`parametrization_one` also proves that `(1,1)` maps to the identity:
the two values of `p` coincide there and cancel. No pointedness premise
on `p` is needed.

The provenance is internal. The construction uses the published
`KernelPair` isomorphism and represented-kernel difference, categorical
pullback operations, and Mathlib's ideal-sheaf definition of schematic
dominance and flat-base-change theorem. No additional structural theorem
is assumed. The base is any scheme, so the result in particular retains
every field and characteristic.

This contribution does not construct a torus quotient, prove splitness,
or prove maximal-torus conjugacy. The source of the constructed map is
`D × ker(φ)`; even if `D` is a split torus, `ker(φ)` need not be a torus,
smooth, or connected. Extracting a split-torus domination of a unipotent
kernel requires further arguments. The source group `H` is additionally assumed quasi-compact over `S` for
`difference_quasiCompact`, `parametrization_quasiCompact`, and
`parametrization_isDominant`. Under the kernel-pair isomorphism the difference
is the second projection from `H ×[S] ker(q)`. That projection is a base
change of `H → S`, hence quasi-compact. Quasi-compactness then passes to the
full parametrization, provided `p` is quasi-compact. Combining this with its
schematic dominance proves topological dominance. No reducedness premise on
either kernel is used in this deduction.
