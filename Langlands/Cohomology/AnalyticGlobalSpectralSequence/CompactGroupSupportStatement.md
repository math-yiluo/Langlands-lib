# Étale compact-support spectral sequence for compact acting groups

## Source and scope

Vladimir Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(1995–1996 unfinished manuscript), Corollary 1.5.2(i), printed and PDF
pp. 11–12, with the definitions of support and compactly supported
cohomology on p. 11 and the composite of ordinary sections and invariants
in §1.2, pp. 4–5. The retained PDF is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`,
in registered folder `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
[Author's copy, pp. 11–12](https://www.wisdom.weizmann.ac.il/~vova/Equish_1996.pdf#page=11)

The displayed étale sequence of Corollary 1.5.2(i) has

\[
E_2^{p,q}=H^p(G,H_c^q(X,b^*F)) \quad\Longrightarrow\quad H_c^{p+q}(X(G),F).
\]

This statement imposes compactness on the acting group `G`. This is
an additional hypothesis compared with the manuscript. For an infinite
discrete group such as `ℤ` acting by translations on a disjoint union of
analytic points, compactly supported sections yield the regular
representation. Its higher group cohomology can be nonzero even though
derived invariant compactly supported sections vanish. The example and
the ordinary-topological compact-group comparison are described in the
[composite-functor statement](../EquivariantComposite/Statement.md#truth-argument).
The analytic base in this module may be noncompact, and the separate
[compact-base sequence](CompactSupportStatement.md) applies to compact
Hausdorff bases with arbitrary acting groups.

## Lean proposition

`Langlands.Cohomology.AnalyticGlobalSpectralSequence.AnalyticEtaleCompactSupportSpectralSequenceForCompactGroupStatement`
uses a fixed complete ultrametric field `K`, a Hausdorff analytic space
`X` over `K`, and a continuous action `ρ : G →* Aut X` over `K`. The
coefficient ring is any commutative ring `R` in the module universe.
`Small G` and admissible refinements of the distinguished lift system
are the premises for the model's derived functors. As in the compact-base
statement the module universe is `max u (v + 1) uL`, the group lives in
`Type z`, and the derived category may live in a separate universe.
Supports use the `L`-valued points, with their topology induced from
`|X|`. The normed extension `L` of `K` has the point axioms on `X`,
and every point of `|X|` is the image of an `L`-valued point.

For each étale `G`-sheaf of `R`-modules `F`, the complex `D` is the
actual derived smooth compact sections, `etaleGSheafCompactComplex`
followed by the inclusion of the bounded-below derived category. The
sequence is the existing covariant `spectralSequence D A` for the
trivial smooth representation `A` on `R`. The statement gives
smoothness of the canonical `G`-action on the compactly supported
cohomology of the ordinary restriction and the additive page-two
identification with `Ext^p` from `A` to that smooth representation.
These `Ext` groups implement derived invariants in smooth
representations.

The abutment is the additive group underlying
`etaleGSheafInvariantCompactCohomology` in degree `p + q`. This
functor derives the composite of smooth compact sections and
invariants in the model category `EtaleGSheaf`. The proposition uses
`FirstQuadrantAbutmentStatement` for page-two vanishing outside the
first quadrant, the finite truncation filtration and the stable
associated graded pieces. The identifications are additive and
objectwise. Transport from modules on the equivariant site to this
model uses the separate module-valued case of Berkovich's Theorem
1.4.2.

## Comparison needed for the proof

The published comparison map in `AnalyticEtaleCompactComparisonStatement`
and its compatibility with the group action give the page-two
identification once the comparison is shown invertible. For the
abutment the geometric input is that smooth compact sections of
injective étale `G`-sheaves are acyclic for smooth invariants. The
compact-group argument uses smooth coinduction: a smooth family of
rows has finite range because it is constant on cosets of an open
subgroup. The supports of finitely many compact rows lie, after all
translations, in the compact saturation of their union. This permits
the compact-section calculation on coinduced objects, after which
injective sheaves can be treated by retracts. The ordinary-topological
implementation of this argument is in
[EquivariantComposite/CompactProof](../EquivariantComposite/CompactProof.md).
The argument on the analytic étale site and the application of the
hyperext convergence results are proof obligations for the proposition.
