# A canonical Jacquet section on actual standard chambers

`Langlands.Jacquet.StandardCanonicalSectionStatement` is a proposition target
for the uniform single-operator construction and independence assertion in
Renard VI.6.1. It is a statement, not a proof.

The original source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The author read VI.6.1, printed pp.176–177 / PDF pp.182–183. The specific
target starts with (VI.6.1.2) on printed p.177 and includes the subsequent
single-image isomorphism, direct sum, and independence Proposition. The
weak Jacquet theorem on the preceding page is a prerequisite, not the
independence assertion itself.

## Actual data and structural inputs

The field `F` is any nonarchimedean local field, in either characteristic.
The group `G` is the shared actual connected reductive group scheme over
`Spec F`. Its affine structure and smoothness come from `hG`. The topology
on `rationalPoints G` is exactly `rationalPointTopology F G.X`;
`rationalPoint_isTopologicalGroup F G` supplies its topological group law
using finite type from smoothness. The representation carrier has an
independent universe `uV`, with `uF` for the field and group schemes.

The statement fixes an actual maximal split torus `i : S.toGrp ⟶ G`, a
generic cocharacter `ν`, and an index `J ⊆ simpleRelativeRoots i ν`.
It retains existence of an actual standard cocharacter for `J` as the
named algebraic input `_hstandard`. This is the first conclusion of the
shared `StandardCocharacterStatement`, not a representation-theoretic
assumption. A compatible split component `q : A.toGrp ⟶ S.toGrp` satisfies
the existing `IsCompatibleStandardSplitComponent`: it is an actual split
subtorus, represented inside the actual standard Levi as its maximal
central split torus, with commuting algebraic inclusions.

The subgroups `N` and `M` are precisely `standardUnipotentPoints i ν J`
and `standardLeviPoints i ν J`. The named premise `hMN` retains their
algebraic normalization `M ≤ normalizer N`, required by the existing
coinvariant action. It assumes no representation conclusion. The compact
open subgroup `K` satisfies the existing
`StandardParabolicBasisMember i ν J q K.toSubgroup`. This is the local
instance of the retained Chapter V, V.5.2(ii)–(iv), inputs: the ordered
Iwahori intersection decomposition and the normalization, contraction,
exhaustion, uniform compact containment, and neighborhood cofinality
clauses for the same literal subgroups and actual character chambers.
Those structural assertions are not proved by this target. The global
simultaneous basis and special compact subgroup construction remain
separate; no new basis or special compact is chosen here.

These input definitions use Renard V.2.5, printed p.107 / PDF p.113,
V.3.14, printed p.113 / PDF p.119, V.3.21–V.3.23, printed pp.116–117 /
PDF pp.122–123, and V.5.2, printed p.123 / PDF p.129. The Chapter V
structural ledger retains the external provenance and discharge obligations.

The representation `ρ` is an admissible smooth complex representation.
There is no additional finite-dimensionality hypothesis: finite
dimensionality of its actual `K`-fixed vectors follows from admissibility.
No splitness or quasi-splitness of `G`, restriction on the characteristic,
proper-parabolic condition, positive rank, or central-character hypothesis
is added. Empty root and character sets are allowed.

## Maps and uniform conclusions

Write `W = fixedVectors ρ K.toSubgroup`,
`Q = fixedVectors (Jacquet.action ρ N M hMN) (K.toSubgroup.comap M.subtype)`,
and `j = fixedJacquetMap ρ N M hMN K.toSubgroup`. These are the actual
fixed-vector modules and the actual quotient restricted to them. The action
on `Q` is unnormalized, as in this source section. For an actual point `t`,
write `C_t = compressedAction ρ hρ.1 K hK t`; this is the normalized compact
average of `ρ(t)v` on `W`, Renard's `π(a_{t,K})`.

The conclusion chooses one threshold `0 < ε ≤ 1` and one linear section
`s : Q →ₗ[ℂ] W`, before quantifying every point of
`standardComponentCAepsilon i ν J q ε`. This chamber is the image of the
published common-uniformizer section of `A(F)`, with every restricted
outside-`J` simple character of norm strictly below `ε`. It is not all of
`A(F)` and does not have an extra weak-chamber restriction. Choosing
`ε ≤ 1` by shrinking the source threshold ensures the strict/weak
inequalities needed for contraction and multiplication. The conclusion
also supplies a point in that chamber, so its uniform clauses are not
allowed to hold only because the chamber is empty.

For every such `t`, the conclusion gives:

1. `ker j ≤ ker C_t`, the uniform annihilation assertion (VI.6.1.2), and
   then the equality `ker C_t = ker j`.
2. `IsCompl (ker C_t) (range C_t)`, encoding both zero intersection and
   sum equal to all of `W`.
3. Bijectivity of the existing `compressedImageJacquetMap` on the image
   of this single `C_t`, onto `Q`.
4. `range C_t = stableImage ... t` and
   `powerKernelSup ... t = ker j`, explicit derived comparisons with
   the published all-power constructions.
5. `range s = range C_t` and equality of `s` with every
   `compressedImageLift ... t ... hb`, for every proof `hb` of the
   restricted quotient's bijectivity.

The section satisfies `j.comp s = LinearMap.id`. Since the same `s`
works for the entire chamber, the range equality gives equality of the
single compression images for any two allowed points; the kernel equality
likewise gives equal kernels. Thus the direct sum and inverse section are
independent of `t`. The bijectivity witnesses in the final clause are
available from conclusion 3; they are not additional assumptions on `ρ`.
Neither uniform annihilation, single-image bijectivity, complementarity
nor independence occurs among the structural premises.

The two all-power comparisons in conclusion 4 are internal consequences
of the source's direct sum: the compression kills its kernel and is
invertible on its invariant image. They are included to connect the
single-image result to the existing Library interface. They do not
identify the single image with an intersection merely by definition.

## Remaining proofs and scope

The proof must derive the uniform kernel threshold, using the compact
radical averaging argument or an equivalent finite-dimensional argument
from the actual uniform contraction clauses. The published generic
Iwahori-contraction results already supply the stable-image Jacquet
bijection under their explicit inputs; that alone does not give equality
of images for different elements. The source proves this using
multiplicativity for commuting component points and equal dimensions.
The existing `compressedImageLift_eq_of_range_eq` supplies section
uniqueness only after that range equality is proved.

The source's Proposition compares points in the same component chamber.
This target does not assert independence of the choice of maximal split
torus, algebraic presentation, compatible split component, uniformizer,
or `K`. Nor does it prove the general special compact/basis existence,
normalized Jacquet admissibility, the nonadmissible version in VI.9.1,
the opposite pairing, or any second-adjointness statement.
