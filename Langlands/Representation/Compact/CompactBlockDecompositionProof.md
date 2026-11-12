# Projectivity, injectivity and compact block decompositions

Worker 141 proves exactly
`Langlands.Renard.CompactRepresentation.CompactBlockDecompositionStatements`
by the theorem `compactBlockDecomposition`, with independent group universe
`u` and carrier universe `v`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
IV.1.6–IV.1.7, printed pages 94–95 / PDF pages 100–101. Both pages were read.
The category-decomposition predicate is the published interpretation of A.IX.

The aggregate theorem is the conjunction of five exact proofs, implemented in
separate paired modules:

1. `compactProjectiveInjective` proves ambient projectivity and injectivity of
   compact irreducibles. It reuses published projectivity. Its injectivity
   proof dualizes a monomorphism to an epimorphism, lifts using projectivity of
   the compact smooth contragredient, and recovers the extension using Hom
   duality and bijective evaluation into the admissible target's smooth bidual.
2. `compactPartSemisimple` uses the published exhaustion theorem to obtain
   compact coefficients from the compact-constituent predicate, then applies
   published semisimplicity. The Serre full-subcategory inclusion preserves
   monos and epis and transfers ambient projectivity and injectivity.
3. `isotypicSplitting` uses the intrinsic class projector's actual kernel and
   range coproduct. The proved comparisons identify isotypic objects with
   identity projector action and avoiding objects with zero projector action;
   naturality gives both off-diagonal Hom vanishings.
4. `finiteIsotypicSplitting` uses all selected projectors and `id` minus their
   sum, indexed by the exact published `Option S`. They are orthogonal,
   idempotent and sum to identity. Their actual range cofan is a coproduct;
   naturality and orthogonality give all required off-diagonal vanishings.
5. `compactPartDecomposition` uses compact-part exhaustion by all intrinsic
   compact-isotypic ranges. Orthogonality and exhaustion imply finite support
   on each vector and identity total sum. The resulting actual coproduct
   restricts to the compact full subcategory, since its ranges are
   subrepresentations of the original object. Distinct components are Hom
   orthogonal.

The supporting `ProjectorCofan` construction proves the coproduct universal
property by summing the component maps after projection. It keeps every object
in the fixed carrier universe, even when the index type is larger, and assumes
no global oversized coproducts. The compact-part decomposition uses no
additional finiteness of fixed-level irreducible classes.

The aggregate theorem adds no hypothesis and preserves every published object,
the statement's Lean/Markdown pair and its import closure. Only standard Lean
logical axioms are used. This file assembles the implemented proofs; their
companions give the detailed proof routes, which need not coincide with the
source's reduction to the semisimple isotypic category.
