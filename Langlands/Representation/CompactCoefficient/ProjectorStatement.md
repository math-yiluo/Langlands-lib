# Natural compact-isotypic projectors with intrinsic range and kernel

`Langlands.CompactCoefficientProjectorStatement` is a proposition definition,
not a proof or a chosen projector. It states existence of the natural projectors
of Bernstein–Zelevinsky (1976), §§2.42–2.44, with their range and kernel identified
with the published intrinsic subrepresentations. Orthogonality, compact
coefficients of the range, and fixed-vector vanishing are included as derived
conclusions.

## Hypotheses and quantifier order

The group and measure binders are exactly those of
`CompactCoefficientSemisimplicityStatement` and
`CompactCoefficientSplittingStatement`, in the same order:

```lean
(G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
[T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
[SigmaCompactSpace G] [MeasurableSpace G] [BorelSpace G]
(μ : Measure G) [Measure.IsHaarMeasure μ] [Measure.Regular μ]
[Measure.IsMulRightInvariant μ]
```

Thus `G` is a Hausdorff, locally compact, totally disconnected topological
group, countable at infinity. It has its Borel measurable structure and a
regular left Haar measure that is also right invariant. These express the
unimodular l-group hypotheses of §2.42. Section 1.1, p.6, defines l-groups by
a compact open subgroup basis; the equivalent locally compact Hausdorff
zero-dimensional condition agrees with total disconnectedness here.
Section 1.5, pp.6–7, defines countable at infinity as a countable union of
compact sets. The measure has no chosen normalization and does not occur
in the body of the proposition.

The universe parameters are `.{uG, uV, uW}`: `G : Type uG`,
class representatives have carriers in `Type uV`, and ambient representations
have carriers in `Type uW`. All three universes are independent. For each
choice of these universes and of the displayed group and Haar data, the
proposition asserts

```lean
∃ P : (c : CompactCoefficientClass.{uG, uV} G) →
    (A : SmoothRep.{0, uG, uW} ℂ G) →
      A.representation.IntertwiningMap A.representation, ...
```

This is one simultaneous family, followed by the six universally quantified
properties below. Its index `c` is the actual quotient of irreducible smooth
compact-coefficient representations, not a supplied list or a small skeleton.
The class type has universe `Type (max uG (uV + 1))`; the existential over the
family imposes no resizing or smallness assumption.

`A` is any actual smooth complex representation. Its underlying vector space
has no topology, and no admissibility, irreducibility, finite dimension, finite
length or compact-coefficient hypothesis is imposed on `A`. The source's
category `Alg G` (§2.1, p.15) consists of representations with open vector
stabilizers, which is the `IsSmooth` condition bundled in `SmoothRep`.
Both objects in the naturality clause lie in the same fixed ambient universe
`uW`; `uV` is not identified with `uW`. All maps are actual equivariant complex
linear maps, represented by `Representation.IntertwiningMap`.

## The six conclusions

Write \(P_{c,A}=P\,c\,A\), and use composition in the order
\((f\mathbin{\mathrm{comp}}g)(v)=f(g(v))\).

1. **Idempotence:** \(P_{c,A}\circ P_{c,A}=P_{c,A}\) as actual intertwiners.
2. **Intrinsic range and kernel:**
   \[
   \operatorname{range}P_{c,A}=I_c(A),\qquad
   \ker P_{c,A}=N_c(A),
   \]
   as equalities in `Subrepresentation A.representation`, where the unchanged
   published definitions are
   \[
   I_c(A)=
   \bigvee_{\substack{D:\,\mathrm{IrreducibleCompactCoefficientRep}\\
                     \mathrm{ofRep}(D)=c}}
       \ \bigvee_{f:D\to A}\operatorname{range}f,\qquad
   N_c(A)=
   \bigwedge_{\substack{D:\,\mathrm{IrreducibleCompactCoefficientRep}\\
                       \mathrm{ofRep}(D)=c}}
       \ \bigwedge_{f:A\to D}\ker f.
   \]
   The representatives `D` have carrier universe `uV`; all arrows in these
   formulas are actual intertwiners, even when their carrier universes differ.
3. **Naturality:** for every `c`, every `A B` in the ambient universe, and
   every actual intertwiner \(f:A\to B\),
   \[
   f\circ P_{c,A}=P_{c,B}\circ f.
   \]
4. **Orthogonality:** for every ordered pair \(c\ne d\) and every `A`,
   \(P_{c,A}\circ P_{d,A}=0\). Quantifying over ordered pairs also gives the
   reverse composition.
5. **Compact coefficients on the range:**
   `HasCompactSmoothDualCoefficients (P c A).range.toRepresentation`.
   This is the actual restricted action on the invariant range subtype.
   Explicitly, for each vector \(v\) in that range and every algebraic
   functional \(\ell\) on it that is smooth for its dual action,
   \(g\mapsto\ell(gv)\) has compact support. Smoothness of the range itself
   follows by restriction of the smooth ambient action.
6. **Fixed-vector vanishing:** for each `K : OpenSubgroup G` with
   `IsCompact (K : Set G)`, if
   `¬ CompactCoefficientClass.HasFixedVector K.toSubgroup c`, then
   \[
   v\in\operatorname{fixedVectors}(A,K)\ \Longrightarrow\ P_{c,A}v=0.
   \]
   `HasFixedVector` is the published quotient-invariant condition that a
   representative has a nonzero fixed vector. Its negation says that every
   representative's fixed space is zero.

These properties are conclusions of the existential. There is no
theorem-valued existence, complementarity or semisimplicity assumption,
unproved projector constant, or structure carrying the desired laws.

## Registered original and conventions

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys
**31**:3 (1976), 1–68, English translation.

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- PDF SHA-256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Read locators (printed and PDF page numbers agree): §§1.1 and 1.5, pp.6–7
  (group hypotheses); §2.1, p.15 (`Alg G`); §2.13, p.19 (smooth
  contragredient); §§2.39–2.40, p.26 (matrix elements and finite
  representations); §2.42, pp.26–28 (projector distributions under the stated
  hypotheses); §2.43 and Theorem 2.44, p.28 (natural projectors, image and
  complement).

The source's word “finite” means compact smooth-dual coefficients, not finite
dimension or finite length. Its smooth contragredient is the smooth part of
the full algebraic dual (§2.13). This is exactly what the published
`HasCompactSmoothDualCoefficients` tests. The source coefficient uses
\(g^{-1}\), whereas `matrixCoefficient` uses \(g\); inversion is a
homeomorphism, so compact support is equivalent. Smoothness makes these
coefficients locally constant; their nonzero loci are closed, so the source's
support convention agrees with `HasCompactSupport`.

## Derived rationale for the intrinsic formulas and consequences

This section explains the mathematical implication of the source. It is
not an implemented Lean proof.

Fix a representative \(D\) of `c`. Section 2.43 constructs an equivariant
idempotent on every smooth representation and states naturality for every
intertwiner. Its image \(M\) is an algebraic direct sum of copies of \(D\).
Theorem 2.44(a) identifies its kernel \(Q\) and gives
\(A=M\oplus Q\), where \(Q\) has no subfactor isomorphic to \(D\).
The source defines these subspaces by its projector, rather than by the
intrinsic supremum and infimum. Their identification here is part of the new
theorem obligation; the published `Isotypic` module does not prove it.

**Range.** The summand inclusions \(D\to M\to A\), composed with the
equivalences identifying each summand with \(D\), show \(M\subseteq I_c(A)\).
Conversely, for any intertwiner from a representative of `c` to \(A\),
its composite with the invariant projection \(A\to Q\) is zero: otherwise
irreducibility would embed that representative in \(Q\), contradicting the
no-isomorphic-subfactor property. Hence every generating range lies in \(M\),
and \(I_c(A)=M\). This argument uses actual maps between the independent
carrier universes; it does not assume that \(D\) is itself an object at
ambient universe `uW`.

**Kernel.** Every map \(A\to D'\) to a representative of `c` kills \(Q\):
a nonzero restriction \(Q\to D'\) would be surjective by irreducibility,
making \(D'\) a quotient, hence a subfactor, of \(Q\). Thus \(Q\subseteq N_c(A)\).
If a vector has a nonzero component in \(M\), a nonzero coordinate in the
direct-sum expression is detected by a coordinate map \(M\to D\).
Extend that map by zero on \(Q\); the resulting actual intertwiner
\(A\to D\) does not kill the vector. Therefore \(N_c(A)\subseteq Q\).
This uses finite support within the algebraic direct sum describing this
single isotypic image; it makes no claim about support across all classes.

An idempotent with these prescribed range and kernel is unique: it fixes
its range, kills its kernel, and these subspaces are complementary.
Consequently the source projectors are independent of the representative and
descend to the quotient `c`, giving the simultaneous family. The source's
normalization on \(D\) is the identity: in §2.42(a) its operator agrees with
compact-subgroup averaging on \(D\), and sufficiently small subgroups fix each
vector in §2.43. Alternatively, applying §2.44(a) to \(D\) makes the kernel
zero (a nonzero submodule of \(D\) would be all of \(D\)), and an injective
idempotent is the identity. The image assertion alone, allowing an empty
direct sum, would not establish this normalization.

**Orthogonality.** A nonzero map between irreducible representations is an
equivalence. Thus, when \(c\ne d\), every map from a representative of `d`
to one of `c` is zero. Every outgoing map \(A\to D_c\) therefore kills each
incoming range \(D_d\to A\), hence their supremum \(I_d(A)\).
So \(I_d(A)\subseteq N_c(A)\). The range and kernel identities now give
\(P_{c,A}P_{d,A}=0\).

**Compact coefficients.** A vector in \(M\) has only finitely many nonzero
coordinates in its direct sum of copies of \(D\). Pulling a smooth algebraic
functional on \(M\) back along each summand inclusion gives a smooth
functional on that copy: an open subgroup fixing the original functional
also fixes its pullback by equivariance. The coefficient of the vector is
therefore a finite sum of compactly supported coefficients, so it has compact
support. Transport along the direct-sum equivalence gives the exact range
predicate. This also agrees with §2.44(b)'s assertion that the submodule
generated by all such images is finite, and §2.40's inheritance by subfactors,
but no exhaustion theorem is needed for this argument.

**Fixed vectors.** Equivariance sends a \(K\)-fixed vector of \(A\) to a
\(K\)-fixed vector of \(M\). If `c` has no nonzero \(K\)-fixed vector, each copy
of \(D\) has zero fixed space. The coordinate projections from the direct sum
are equivariant, so every coordinate of that vector of \(M\) is zero.
Thus its image under \(P_{c,A}\) is zero. This argument in fact applies to any
subgroup; the stated conclusion is restricted to actual compact open
subgroups as required by the downstream finiteness application.

## Dependencies and boundary

The module imports the published
`Langlands.Representation.CompactCoefficient.Isotypic` unchanged, including
its `Classes` and `SubrepresentationLattice` dependencies.
Mathlib supplies Haar measure classes, open subgroups, actual intertwiners,
their invariant ranges and kernels, and the restricted action
`Subrepresentation.toRepresentation`. It uses no unproved Library statement
as an assumption. The compilation environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).

The existence proof remains separate. The statement does not assert
pointwise finite support over all compact-coefficient classes for arbitrary
`G`; the product-Levi fixed-level finiteness input is separate. It does not
assert total compact-object exhaustion, general outer-conjugation covariance,
compatibility between independently chosen ambient universe instances, or the
final Levi decomposition. These are not hypotheses used here either.
The already published conditional projection construction supplies useful
algebra only when complementarity is given; it does not establish this
existence proposition.

Authored by Worker 46. Worker 173 supplied the theorem interface and its
independent-universe and intrinsic-identification requirements.
