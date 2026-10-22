# Compact smooth-dual coefficients and irreducible smooth classes

Worker 202 constructs the compact-coefficient condition and the genuine
isomorphism classes needed as definition prerequisites for
Bernstein–Zelevinsky (1976), §§2.43 and 4.14. This unit proves only intrinsic
transport and quotient laws. It proves no projector, decomposition,
admissibility, or finiteness theorem.

## Coefficients and transport

For an actual group `G : Type uG` with a topology, a complex representation
`ρ : Representation ℂ G V` on `V : Type uV` has
`Langlands.HasCompactSmoothDualCoefficients ρ` precisely when

\[
 \forall v\in V,\ \forall\ell\in V^*,\qquad
 \ell\text{ is smooth for }\rho^\vee
 \ \Longrightarrow\
 \bigl(g\mapsto\ell(\rho(g)v)\bigr)\text{ has compact support}.
\]

Here `Module.Dual ℂ V` is the full algebraic dual and
`IsSmoothVector ρ.dual ℓ` means that some open subgroup fixes `ℓ` under
`(ρ.dual g ℓ)(v) = ℓ (ρ g⁻¹ v)`. The coefficient is the existing
`matrixCoefficient`; compact support is Mathlib's `HasCompactSupport`,
compactness of the closure of the nonzero locus. The carrier has no topology
and may have arbitrary dimension. The predicate itself does not require
smoothness of `ρ`; its bundled uses below do.

`hasCompactSmoothDualCoefficients_iff_of_equiv` transports the predicate along
an actual `Representation.Equiv`, with independent source and target carrier
universes `uV` and `uW`. Its forward proof chooses a preimage of each target
vector under the surjective equivalence. Coefficient naturality
(`matrixCoefficient_intertwining`) identifies its coefficient with the source
coefficient of the pulled-back functional. `dualIntertwining` and
`isSmoothVector_map` show this functional is smooth. The source compact-support
hypothesis therefore applies. The same argument for the inverse equivalence
proves the converse; no finite-dimensional duality is used.

## Actual objects, classes, and fixed-subgroup strata

`irreducibleCompactCoefficientProperty G` is the conjunction of
`A.IsIrreducible` and `HasCompactSmoothDualCoefficients A.representation` on
actual `SmoothRep ℂ G` objects. Irreducibility is the existing simplicity
condition on invariant submodules, including nonzeroness.
`IrreducibleCompactCoefficientRep G` is its full subcategory. In particular,
smoothness is proved data of the underlying object. No admissibility, finite
dimension, finite length, unitarity, or prescribed central character is added.

`CompactCoefficientClass.{uG, uV} G` is the quotient of this full subcategory
by the existing `isIsomorphicSetoid`. Carriers are in the fixed universe
`Type uV`, independent of `uG`; the class type lives in
`Type (max uG (uV + 1))`. The construction makes no resizing or smallness claim
and does not select representatives. In particular `uV` can be instantiated
with a universe maximum required by a consumer.

In the namespace `CompactCoefficientClass`, `ofRep` sends a representative
to its quotient class. `ofRep_eq_iff` says that two such classes agree exactly
when there exists an actual categorical isomorphism of the representatives.
Because both categories are full subcategories of the representation category,
these are actual equivariant linear isomorphisms.

For any subgroup `K : Subgroup G`, `HasFixedVector K` descends the condition
`fixedVectors A.obj.representation K ≠ ⊥` to this quotient. To show
representative independence, the quotient lift maps a categorical isomorphism
to the underlying smooth category, converts it to a representation equivalence
with `SmoothRep.equivOfIso`, and applies the published
`fixedVectors_ne_bot_iff_of_equiv`. Propositional extensionality then supplies
the equality required by `Quotient.lift`. `hasFixedVector_ofRep` is the
definitional evaluation law. `hasFixedVector_ofRep_iff_exists` uses the
submodule nonbottom criterion to identify it explicitly with the existence of
a nonzero `K`-fixed vector. `fixedStratum K` is the set of classes satisfying
this property. The subgroup need not be open or compact, and no finiteness of
this set is asserted.

## Original source, conventions, and scope

The registered original is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local field*,
Russian Mathematical Surveys **31**:3 (1976), 1–68, English translation.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- SHA256: `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original: `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Read locators: §§2.39–2.40, printed/PDF p.26 (matrix elements and condition
  (a) defining a finite representation); §§2.42–2.44, pp.26–28 (the subsequent
  projector and splitting use); §4.14, p.41 (nonisomorphic finite irreducible
  representations with nonzero fixed level).

The source calls this compact-support condition “finite”; it does not mean
finite dimension. The formal name avoids that ambiguity. Its coefficient is
`g ↦ ℓ (ρ g⁻¹ v)`, whereas the imported coefficient uses `g`.
For a topological group, inversion is a homeomorphism, so these two functions
have compact support simultaneously. On a smooth representation the
coefficients are locally constant, so the nonzero locus is closed and the
source's support convention agrees with topological compact support.
The definitions themselves need only a group with a topology; the preceding
comparison of conventions applies when that topology makes it a topological
group, in particular in the original locally profinite setting.

The full subcategory and its quotient, the transport proof, and the subgroup
stratum are internal constructions of the source's objects, not additional
literature theorems. In §4.14 the group is specifically `G°` for a product of
general linear groups and the subgroup is a congruence subgroup; the source
expresses the fixed-level condition by a nonzero averaging operator. The
present unit constructs the fixed-space condition for any subgroup. It neither
constructs that averaging operator nor proves the comparison or §4.14's
finiteness conclusion. Similarly, §2.43's natural projectors require later
work under the source's extra hypotheses. No representation-theoretic theorem
is generalized to arbitrary groups here.

All prerequisites are imported from the published Library by Lean names:
`Category.ClassInvariants` supplies `SmoothRep`, the isomorphism-class
infrastructure and fixed-space transport; `MatrixCoefficient.LawsProof`
supplies coefficient naturality and the dual intertwiner;
`Smooth.Transfer.SubquotientProof` supplies smooth-vector transfer. Mathlib
supplies the complex field, compact support, and categorical quotient. Existing
published Lean/Markdown pairs are unchanged.
