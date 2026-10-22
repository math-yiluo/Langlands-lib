# Cuspidality and Weyl transport on actual product Levis

Author: Worker 14. This pair supplies concrete data for the cuspidal-support
theorems of Bernstein and Zelevinsky. It does not state their classification,
finite-length, or Hom-space conclusions.

`IsLeviQuasicuspidal B rho` tests an actual complex representation of the
product Levi of `B` on every proper standard block refinement. Properness
means that the actual refined parabolic subgroup differs from the full
Levi. Vanishing means that the actual quotient by the span of
`rho(u)v-v`, for the refined unipotent radical, is a subsingleton.
These are the product subgroups constructed in `Geometric.WeylDefinitions`.
The predicate imposes neither admissibility nor smoothness.

`IsLeviCuspidal` adds the published admissibility predicate, which already
includes smoothness. Sourced theorems about quasicuspidal representations
must impose smoothness separately; irreducibility is added where required.
This retains BZ77's distinction between quasicuspidal and
cuspidal representations. The existing
`GeneralLinear.IsSupercuspidal` is reused as an imported construction; it is
not redefined. That predicate concerns a single general linear group and
tests conjugates as well. The current predicates concern the product
Levis and the standard refinements used in BZ77. No equivalence between
those two presentations is assumed here.

The two equivalence-invariance lemmas use the published actual equivalence
of Jacquet quotients and the admissibility-equivalence theorem.
Representation carrier universes are independent.

`ConjugatesLevi B C w` is equality of the image of the source block diagonal
subgroup under the actual permutation-matrix conjugation with the target
block diagonal subgroup. `ConjugatingPermutations` is its finite subtype
inside the symmetric group. No unspecified relation stands for conjugacy.

`leviConjugation` constructs the multiplicative equivalence of product
Levis using their existing embeddings into the ambient matrix group,
actual conjugation on the source image, the stated equality of subgroup
images, and the inverse target embedding. Its value under the target
embedding is proved to be `w m w^-1`; the inverse equivalence is proved to
give `w^-1 m w`.
`transport` therefore acts on a target element by the original
representation evaluated at inverse conjugation. `transportMap` retains
the linear map of an intertwiner and proves its equivariance by evaluation.
When the field is a topological ring, both directions of conjugation are
proved continuous using the published continuous Levi embeddings and
equivalences. Smoothness of transport follows from continuous pullback.
`transportFunctor` packages this construction on the actual smooth
representation categories, with the transported intertwining maps and
proved identity and composition laws.

`LevisAssociated` means that the actual conjugating-permutation subtype is
nonempty. `RepresentationsAssociated` requires an actual representation
equivalence after transport by such a permutation. The latter automatically
includes association of the Levis.

`MinimalConjugatingPermutations` restricts the finite minimal-representative
subtype from `WeylDefinitions` to permutations carrying the entire source
Levi onto the target Levi. `AssociatingPermutations` further requires an
actual equivalence of the transported source representation with the target.
The subtype is finite without choosing representatives. Its identification
with the right-coset set in BZ77 is a separate theorem obligation; the
definitions assume neither bijectivity nor any numerical Hom bound.

## Source and provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), sections 2.1-2.4 and 2.6-2.9, printed pages 446-448
(PDF pages 7-9), and section 2.13, printed page 449 (PDF page 10).
These original pages were read directly, including a fresh reading of their
retained text on 2026-10-20. Source ID:
`bernstein-zelevinsky-1977-induced-i`; original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 2.2 identifies standard subgroups of a product Levi with refinements
of its ordered partition. Section 2.4 defines quasicuspidality by vanishing
of the Jacquet functors for proper standard subgroups, and cuspidality by
adding admissibility. Normalizing a Jacquet action does not change the
underlying quotient module or the meaning of vanishing; the predicate uses
that quotient directly.

Sections 2.6-2.7 define association through Weyl conjugation and specialize
the Weyl group of `GL_n` to coordinate permutations. The target action
composes the original representation with inverse conjugation. Section 2.9
uses the permutations that associate the two representations; section 2.13(c)
identifies the minimal conjugating representatives with the relevant right
cosets. The latter identification is not asserted as proved in this pair.

The predicates use actual fields and representations without requiring a
local-field topology merely to define the algebraic objects. Admissibility
uses the given field topology. Future sourced theorem targets must retain
the actual p-adic-field, positive-rank and smooth complex hypotheses.
The subgroup-image equivalence, its continuity, the smooth transport functor,
and the two invariant predicates are internal constructions with proved
intrinsic laws. No theorem truth is an input.

## Dependencies and remaining obligations

The pair imports `Geometric.WeylDefinitions` and the published
`Classification.Supercuspidal` and `Smooth.Transfer.PullbackProof` modules
by Lean name. These dependencies are published and their existing constructions
are reused without modification.

The minimal right-coset identification, compatibility
with the single-group supercuspidal predicate, and all cuspidal-support
theorems remain separate obligations.
