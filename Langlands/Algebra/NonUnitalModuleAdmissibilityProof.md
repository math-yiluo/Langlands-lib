# Admissibility and the actual nondegenerate dual

Worker 6 supplied the complete proof draft. Worker 1149 audited the governing
source, the exact published statement and the imported constructions, and added
this attribution and submission record.

This proof establishes the entire published
`NonUnitalModuleAdmissibilityStatements.AdmissibilityDuality` for the original
nonunital module and its actual nondegenerate dual, with independent algebra
and carrier universes. It imports the exact public statement and all public
comparison prerequisites unchanged. The two helper pairs provide canonical
reflexivity and dual simplicity; this entry pair proves dual admissibility
and assembles all three conclusions.

The source is Renard's French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.5.1 unnumbered corollary and its proof, printed p.26 / PDF32. The nearby
reflexivity proof incorporates the correction in registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF2. This part of the corollary uses the fixed-space identification from
I.4.1 rather than deriving dual admissibility from reflexivity alone.

Every idempotent of the opposite algebra is the opposite of its original
unop idempotent. For that original e, the published `fixedPartDuality`
provides a complex-linear equivalence from the actual opposite-e-fixed
subgroup of the nondegenerate dual to the ordinary complex dual of the
actual e-fixed subgroup of M. The latter is finite-dimensional by
admissibility. Injectivity of the equivalence therefore proves the fixed
subgroup finite-dimensional. The published equality
`rightFixedModule_eq_canonical` transports the whole coefficient structure
to precisely the canonical module required by admissibility over A.op.
The full algebraic dual of M never replaces the nondegenerate dual.

The canonical reflexivity proof is in the adjacent
`NonUnitalModuleAdmissibilityReflexivityProof` pair. The adjacent
`NonUnitalModuleAdmissibilitySimplicityProof` pair proves the simplicity
equivalence by actual-dual separation and exactness, together with this
canonical reflexivity result. Its alternate categorical route is explained
in that pair's Markdown.

The closed theorem `admissibilityDuality` introduces all original algebra
and module parameters quantified by `AdmissibilityDuality` and combines
these three proved conclusions. It preserves independent algebra and
carrier universes, the exact canonical evaluation, the original actions
and the actual nondegenerate-dual objects throughout.

The exact statement, the fixed-bidual comparisons and the import compatibility
correction are published dependencies. The proof directory contains only this
entry pair and the two new helper pairs; it contains no target or dependency
overrides. Complete closed interface examples check the aggregate at arbitrary
independent `uA,uM` and at both unequal pairs `(0,1)` and `(1,0)`. Development
compilation does not establish independent semantic acceptance or publication.
