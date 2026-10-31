# Closure of nondegenerate original modules

Workers 6 and 691. Worker 6 authored the shared proof draft; Worker 691
checked the original passages and published APIs, added the named zero
certificate, and checked the complete theorem and reusable interfaces.
This proof establishes the published closed closure target using the actual
original category and the published coordinatewise products.

The target is the complete `NondegenerateModuleClosureStatement.{uA,uM}`:
zero containment and closure under original ambient monomorphisms,
epimorphisms and finite products over every idempotented original ring.
Ring and carrier universes remain independent. The Lean file checks the
complete theorem at arbitrary universes and at the unequal specializations
`(0,1)` and `(1,0)`. No original unit-action law, nontriviality, field,
commutativity, finite generation or finite dimension is required. Zero rings
and zero carriers are included.

The reusable lemmas in `Langlands.Algebra.NonUnitalModuleCat` are:

- `isNondegenerate_of_isZero` and `nondegenerateProperty_containsZero`;
- `nondegenerateProperty_isClosedUnderSubobjects`;
- `nondegenerateProperty_isClosedUnderQuotients`;
- `isNondegenerate_concreteProduct`;
- `nondegenerateProperty_isClosedUnderFiniteProducts`.

The zero, subobject and quotient lemmas hold over arbitrary nonunital rings;
only the finite-product lemmas need `IsIdempotented A`. The final theorem is
`Langlands.Algebra.nondegenerateModuleClosureStatement`, whose full unapplied
type is exactly the already published proposition.

An ambient zero object's identity and zero endomorphisms agree. Evaluation
shows that every vector is zero, and the zero idempotent fixes it.
For a monomorphism, the published original-map injectivity criterion reflects
the equality saying that an idempotent fixes the image vector. For an
epimorphism, the published integer-unitization equivalence gives an ordinary
module epimorphism with the unchanged underlying additive map; Mathlib's
surjectivity criterion lifts a target vector. An idempotent fixing the lift
also fixes its image by equivariance.

For a finite coordinatewise product, choose a fixing idempotent for each
coordinate. The published finite upper-bound theorem supplies a common
idempotent, and `Idempotent.smul_eq_of_le` shows it fixes all coordinates.
This includes the empty family. For an arbitrary limiting cone on a finite
discrete diagram, assemble its legs into an original map to this concrete
product. The limit's joint cancellation law proves that this map is mono.
The subobject result then proves nondegeneracy of the cone vertex. Thus the
proof addresses every ambient limiting cone.

The route is an internal derivation from Renard I.1.2, printed p.7/PDF13,
the original module conventions and idempotent order on printed pp.5–6/
PDF11–12, the finite-upper-bound assertion in I.1.2, and the explicit zero
and finite-product obligations from A.VI.1, printed p.261/PDF267. Worker 691
independently read these passages and A.VI.2, printed p.262/PDF268. The
source is the registered French 9 July 2026 book,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The zero and product clauses repair the missing hypotheses in the source's
unrestricted full-subcategory criterion, as explained in the published
`notes/renard/appendix-a-corrections.md`; they are not separately numbered
source assertions. The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was
checked at PDF1–3 and PDF18–19. It concerns the earlier edition and does not
replace the governing original or prove this conjunction.

The quotient argument uses `IntegerUnitization.equivalence` only to infer
surjectivity of the unchanged original map. It does not replace the category
or assume that the old ring unit acts identically. The subobject proof uses
`NonUnitalModuleCat.mono_iff_injective`; the product proof uses
`IsIdempotented.finite_family_upper_bound`, `Idempotent.smul_eq_of_le`, and the
published `NonUnitalModuleCat.concreteProductLift_π`. The finite-product
certificate constructs the Mathlib closure class directly. Its temporary
subobject certificate is the lemma proved in this module, not an assumption.

The nondegenerate abelian structure and its inherited Hom groups, inclusion
and part-functor exactness, adjunctions and other categorical comparisons
remain later obligations.
