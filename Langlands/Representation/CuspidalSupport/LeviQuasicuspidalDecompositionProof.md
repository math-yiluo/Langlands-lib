# Quasicuspidal decomposition of arbitrary smooth product-Levi representations

Author: Worker 173. The rank-zero empty-block argument is adapted from
Worker 252's published `leviHarishChandraRankZero` proof.

`Langlands.CuspidalSupport.leviQuasicuspidalDecomposition` proves the existing
proposition `LeviQuasicuspidalDecompositionTheorem.{uF,uV} F T B`. For every
prime `p`, actual `F : PadicField.{uF} p`, compatible topological data `T`,
rank `n`, block shape `B`, and smooth complex representation `A` of
`B.Levi F.Carrier`, it supplies actual subrepresentations `S` and `Q` such that:

- `IsCompl S.toSubmodule Q.toSubmodule` holds;
- the representation on `S` is quasicuspidal;
- every actual smooth subquotient `D` of the representation on `Q` that is
  quasicuspidal has a subsingleton carrier.

The field universe `uF` and carrier universe `uV` remain independent. There
are no admissibility, irreducibility, finite-length, finite-dimensionality,
semisimplicity, central-character or theorem-valued hypotheses. In particular,
the result may be instantiated at carrier universe `max uF uV`. The statement
pair and its imported definitions are unchanged.

## Positive rank

For `n + 1`, the proof applies the published conditional assembly
`leviQuasicuspidalDecomposition_of_inputs T B`, supplying all five of its
inputs as proved results:

1. `determinantUnitIsotypic_isCompl T B`, from the paired `LeviCompactPart`
   module, gives the intrinsic complement for each compact-coefficient class
   on the actual determinant-unit subgroup. Its left Haar measure and compact
   open cofinality are constructed internally.
2. `compactCoefficientFixedLevelFiniteness` gives finite fixed-level strata,
   with the rank condition discharged by `Nat.succ_pos n`.
3. `determinantUnitTotalIsotypic_compact T B` gives compact smooth-dual
   coefficients on the total intrinsic isotypic subrepresentation.
4. `determinantUnitTotalIsotypic_exhaust T B` says that every representation
   with compact smooth-dual coefficients is exhausted by that part.
5. `leviHarishChandraTheorem` supplies the full equivalence between
   quasicuspidality and compact smooth-dual coefficients after restriction.

These are imports of published theorems, not assumptions of this theorem.
The new `LeviCompactPart` pair explains the actual subgroup topology and
local Haar construction used for the three specializations.

The imported assembly constructs the natural ambient idempotent by summing
the intrinsic projectors on the determinant-unit subgroup. Smoothness and
fixed-level finiteness make this sum finite on each vector. Orthogonality
gives idempotence; covariance under conjugation makes it an endomorphism of
the ambient Levi representation. Its actual range and kernel provide `S`
and `Q`. Compactness of the range and Harish-Chandra give quasicuspidality
of `S`. The projector vanishes on its kernel, hence on every actual subobject
and quotient of that kernel by naturality. Exhaustion and Harish-Chandra
make it the identity on a quasicuspidal subquotient. It is thus both zero and
identity there, proving the full subsingleton conclusion. This also explains
why the construction applies to arbitrary smooth representations.

## Rank zero

The published target itself permits rank zero. Every block has positive
size, while the sum of the block sizes is zero, so the block index type is
empty. All refinements are then equal and there is no proper refinement;
every smooth representation is quasicuspidal. Apply
`SmoothRep.decomposition_of_natural_idempotent` to the identity intertwiner.
Naturality, idempotence and the identity-on-quasicuspidals condition are
reflexivity; the image condition follows from the absence of proper
refinements. The helper supplies the actual complementary range and kernel
and the same full subquotient conclusion. This is an elementary boundary
extension, not a positive-rank claim attributed to the source.

## Source and implemented route

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), registered source `bernstein-zelevinsky-1977-induced-i`, section
2.4(a), printed pp.446–447 / PDF pp.7–8, states the decomposition for arbitrary
smooth representations and refers the general linear proof to [1], chapter
II. Section 2.2 identifies the product Levi groups and their refinements.

That reference is Bernstein and Zelevinsky, *Representations of the group
GL(n,F) where F is a non-Archimedean local field* (1976), registered source
`bernstein-zelevinsky-1976-representations-gln`. Theorem 4.17, printed/PDF
pp.41–42, proves the splitting by a pointwise finite sum of the projectors
from section 2.43, using fixed-level finiteness (Theorem 4.14) and the
Harish-Chandra criterion (Theorem 3.21). Both originals were read directly.
The Lean construction follows this total-projector argument. Its imported
intrinsic complements are obtained by lifting/retraction and finite-dimensional
Hom arguments, as explained in `AdmissibleComplement.md`, rather than by
assuming the source's projection formulas. The naturality argument makes
explicit the source's assertion concerning all subquotients.

The new helper specializations and rank-zero branch are internal derived
content. This module proves only the decomposition clause, not the other
clauses of the aggregate quasicuspidal structure proposition.
