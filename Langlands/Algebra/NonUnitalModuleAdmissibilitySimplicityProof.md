# Simplicity and the actual nondegenerate dual

Worker 6 supplied the complete proof draft. Worker 1149 audited the governing
source, the exact published statement and the imported constructions, and added
this attribution and submission record.

This proof establishes
`NonUnitalModuleAdmissibilityStatements.AdmissibleSimpleIffDualSimple`.
It retains the original nondegenerate module category and the published
`dualObject`, with independent algebra and carrier universes. The statement and fixed-bidual comparison dependencies are imported unchanged
from the published Library.

The source is Renard, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
I.5.1 unnumbered corollary and proof, printed p.26 / PDF32. The adjacent
canonical-reflexivity proof incorporates the converse argument corrected in
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF2.

The implemented route uses categorical exactness and separation, rather
than constructing the orthogonal submodule in Renard's proof. A private
general lemma proves that a faithful contravariant zero-preserving functor
between abelian categories that sends monomorphisms to epimorphisms
reflects simplicity. A nonzero monomorphism into the original object maps
to a nonzero epimorphism from the simple dual object, hence to an
isomorphism. Faithfulness reflects its monomorphism property back to an
epimorphism of the original category. The original monomorphism is
therefore an isomorphism. The other direction in the definition excludes
the zero object using the nonzero identity of the simple dual.

The published actual-dual separation theorem proves faithfulness of each
of the actual left-to-right and right-to-left functors. The published
original-action exactness results provide precisely the required reversal
of monomorphisms. No substitute functor or assumed equivalence appears.
Thus simplicity of the actual dual implies simplicity of the original
module without a finiteness premise. When the original module is
admissible, the adjacent canonical-reflexivity theorem makes the
actual evaluation an isomorphism in the original nondegenerate category.
Simplicity transports from the original module to its actual bidual.
Applying the right-to-left reflection argument then proves simplicity of
the actual first dual. The recovered scalar structures and the explicit
double-opposite action are those of the published constructions.

The proof imports the public exactness closure, including the independently
published import compatibility correction. The adjacent reflexivity proof
and this proof are helper pairs for the exact aggregate target in
`NonUnitalModuleAdmissibilityProof`. This route uses no assumed duality
equivalence, no orthogonal-submodule axiom and no dimension premise beyond
the source admissibility hypothesis in its forward simplicity implication.
