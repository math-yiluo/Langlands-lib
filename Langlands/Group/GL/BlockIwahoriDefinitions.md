# Actual block Iwahori interfaces

Authors: Worker 114 and Worker 118. This module supplies one construction API
for the actual general linear groups and ordered positive block shapes already
published in `Blocks` and `OppositeBlocks`. It preserves those definitions.
All declarations below are in `Langlands.GeneralLinear.BlockShape`.

## Scalars and actual factors

For `B : BlockShape n` and a commutative ring `R : Type u`,
`blockScalarLevi R` sends a tuple `a : Fin B.length → Rˣ` to the product-Levi
element whose i-th block is the scalar matrix `a i`. `blockScalarInLevi R`
composes this with the existing equivalence to the embedded common Levi;
`blockScalar R` composes it with the existing embedding in the actual `GL_n(R)`.
All three are monoid homomorphisms, so their identity, multiplication and inverse
laws are genuine laws of the constructed maps. The displayed coercion and block
entry lemmas identify them with the existing block diagonal matrices. Block
scalars commute with the whole product Levi, as proved entrywise from the
existing scalar-matrix commutation lemma. The two radical-preservation lemmas
specialize the published normalization by that same Levi.

For any actual subgroup `K` of `GL_n(R)`, `iwahoriLower R K`,
`iwahoriLevi R K` and `iwahoriUpper R K` are literally the subgroup infima
`K ⊓ B.oppositeUnipotentSubgroup R`, `K ⊓ B.leviSubgroup R`, and
`K ⊓ B.unipotentSubgroup R`. Their membership lemmas unfold these infima.
The function `iwahoriProduct R K` sends a triple `(l,m,u)` to `l*m*u` as an
element of `K`. Its range certificate uses subgroup multiplication closure;
the coercion lemma is definitional and the identity lemma uses the group laws.
It is a map of sets, with no direct-product group law asserted. This algebraic
API also applies to the underlying subgroup of every open subgroup.

## Scalar entry formulas

The block-scalar matrix is proved to equal the diagonal matrix whose entry at
standard coordinate `k` is `a (B.indexEquiv.symm k).1`
(`coe_blockScalar`). The proof uses the existing same-block and distinct-block
entry formulas and the bijection between block coordinates and standard
coordinates. `blockScalar_mul_apply` and `mul_blockScalar_apply` then apply
Mathlib's diagonal multiplication formulas to obtain the row and column
multipliers.

Consequently `blockScalar_conj_apply` evaluates actual conjugation on the
`(i,j)` block as multiplication by the field/ring element underlying the unit
`a i * (a j)⁻¹`. `blockScalar_inv_conj_apply` evaluates inverse conjugation by
`(a i)⁻¹ * a j`. Both hold for arbitrary ambient matrices in the general
linear group and for all block indices, including diagonal blocks. On the
lower `(j,i)` block for `i<j`, inverse conjugation therefore multiplies by
`(a j)⁻¹ * a i`, the same contracting ratio as the upper `(i,j)` block.
These elementary calculations are internal algebraic derivations from the
published Blocks and OppositeBlocks constructions, valid over a commutative
ring and hence over every field realization used here. They introduce no
positivity or nonempty-rank assumptions.

## Chambers and the factorization predicate

For every prime `p`, every algebraic finite p-adic field `F : PadicField.{u} p`,
and every supplied `T : F.TopologicalData`, `blockScalarRatio T i j` is the
homomorphism on scalar tuples with value
`T.normalizedAbsUnits (a i * (a j)⁻¹)`. It uses the published
residue-cardinality-normalized absolute value, not a different norm.
The homomorphism multiplication proof rearranges commuting field units and
applies multiplicativity of that absolute value.

The following are transparent Prop-valued definitions, universally quantified
over **all pairs** `i < j` of block indices:

- `IsWeaklyContracting T a`: the real-valued absolute ratio is at most `1`.
- `IsStrictlyContracting T a`: the real-valued absolute ratio is less than `1`.
- `IsDeeplyContracting T ε a`: the real-valued absolute ratio is less than `ε`.

The deep predicate contains just the ratio inequalities. A consumer requiring
`0 < ε` and `ε ≤ 1` states these separately, exactly as the existing
`CanonicalPairingAsymptotics` does. Strict contraction implies weak contraction;
a deep bound with `ε ≤ 1` implies strict contraction. The identity and every
constant scalar tuple are weakly contracting. In particular there is no bound
on central scalar size. The weak chamber is closed under pointwise
multiplication, by the ratio homomorphism law and multiplication of nonnegative
real numbers bounded by one.

`HasBlockIwahoriFactorization T` first installs **the supplied** `T.topology`
on `F.Carrier`, so its argument is an actual `OpenSubgroup (GL_n(F))` with the
induced matrix-unit topology. For that `K` the predicate is the conjunction of:

1. Bijectivity of `iwahoriProduct F.Carrier K.toSubgroup`.
2. For every weakly contracting scalar tuple `a`, forward conjugation
   `blockScalar(a) * g * blockScalar(a)⁻¹` carries `K ∩ N` into itself, and
   inverse conjugation `blockScalar(a)⁻¹ * g * blockScalar(a)` carries
   `K ∩ Nop` into itself.

The containment conditions are spelled out as element-membership implications;
these are exactly the subgroup containments in question. The three projection
lemmas expose bijectivity and each containment. Compactness is separate:
applications to compact open groups additionally require the actual
`IsCompact (K : Set (GL_n(F)))`. No canonical-lift, representation, pairing,
admissibility or duality hypothesis or conclusion is built into this predicate.

The field/ring universe is explicit and unconstrained; no representation-space
universe occurs in this geometry interface. The rank is every natural `n`,
with no `n+1` shift or positivity premise. Empty shapes and rank zero are allowed
by `BlockShape`; one-block shapes are allowed as well. With at most one block
all three chamber predicates are vacuous. The deep-vacuity lemma proves this
for every real `ε`, by showing that two strictly increasing indices cannot
exist. The code imposes no artificial positivity condition in this degenerate
case. No existence theorem for factorizing subgroups is asserted here.

## Source and scope

The source is Bill Casselman, *Introduction to admissible representations of
p-adic groups*, Chapter III: *Induced representations and the Jacquet module*,
revision April 29, 2019, section 4, page 5. It is registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The source defines Iwahori factorization for a compact open subgroup by the
ordered multiplication bijection and the two conjugation containments for its
strict chamber `A_P^{--}`. Its Lemma III.4.1 then gives a basis of such subgroups.
Sections 5–6, pages 5–8 use them in canonical lifts and the canonical pairing.

The present weak-chamber containment requirement is a **stronger internal
specialization** intended for concrete GL congruence groups. For the upper
block parabolic, the root corresponding to a block entry `(i,j)` with `i<j`
has scalar ratio `a_i/a_j`; this fixes the contracting orientation. Weak
contraction allows equality at the walls, while strict contraction requires all
these ratios to have absolute value less than one. Requiring containment on the
weak chamber implies the source's strict-chamber containments, because strict
contraction implies weak contraction. The stronger assertion is not attributed
to Casselman's general definition or inferred from Lemma III.4.1.

Thus this is derived construction provenance: actual existing block groups,
explicit scalar characters and intersections, and a transparent strengthened
predicate. The general source motivates it; elementary Lean proofs establish
the implemented algebraic laws. Cofinal existence, deep-contraction geometry,
stabilization, canonical lifts and Jacquet duality remain separate statements
and proofs.
