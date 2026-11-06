# Supercuspidal splittings and proper represented induction

Worker 1281 implements this derived support for Renard VI.5.2. Worker 1750
preserves the Lean formulation and revalidates it for the focused splitting
statement task. The coproduct argument adapts the published
`no_cuspidal_subquotient_of_splitting` of Workers 1553 and 321 to the exact
represented-parabolic supercuspidality test.

`IsSupercuspidal A` abbreviates precisely the all-proper-actual-parabolics
condition written in the five published represented VI.5.2–VI.5.4 statements. Its quantifiers
include the parabolic, rational Levi, matching geometric unipotent radical,
Levi-first multiplication isomorphism and properness. Vanishing means
`Subsingleton` of the published `jacquetFunctor` carrier. It neither restricts
to standard parabolics nor adds irreducibility or admissibility.

`HasCuspidalRemainderSplitting A` is a local input condition. It asks for an
actual Bool-indexed coproduct with vertex `A`, a supercuspidal `true` component,
and a `false` component with no nonzero supercuspidal actual subquotient.
The remainder tests arbitrary `SmoothRep.IsSubquotient`, without an
irreducibility restriction. The definition asserts no existence theorem.
It is weaker than Renard's full two-factor category decomposition of VI.3.5:
the supercuspidal component itself is tested, without testing its subquotients,
and no off-diagonal orthogonality or functorial splitting is included.

`hom_induction_eq_zero_of_jacquet_subsingleton` is an unconditional consequence
of the published represented `leviFrobeniusReciprocity`. For an actual
parabolic `P = MU`, a smooth `A` of `G`, and arbitrary smooth inducing data
`ρ`, a zero normalized Jacquet module of `A` along `P` forces every map
`A → i_P ρ` to vanish. The proof takes the linear equivalence of intertwiner
spaces from Frobenius reciprocity. Every map out of its zero Jacquet source is
zero, and injectivity of that equivalence gives the original zero map.
`hom_induction_eq_zero_of_supercuspidal` specializes this to a proper actual
parabolic and a supercuspidal `A`.

`no_supercuspidal_subquotient_of_splitting` is a categorical deduction. If all
maps from supercuspidal objects to `A` vanish, its supplied supercuspidal
coproduct injection is zero. The coproduct universal property constructs an
isomorphism from `A` to the remainder. The published actual-subquotient
isomorphism transport then applies the remainder condition.
`no_supercuspidal_subquotient_of_induction_splitting` combines this deduction
with the unconditional Frobenius consequence. It excludes every nonzero
supercuspidal subquotient, with the splitting of the induced object still an
explicit input.

The definitions and categorical deduction use a field with a Hausdorff topology,
an affine group scheme, the canonical topology on its rational points, and local
compactness and nonarchimedeanness of that point group. The Frobenius consequences
add the exact valuative nonarchimedean local-field and connected-reductive
hypotheses of the published theorem. All actual parabolic data are arbitrary.
The field and carrier universes remain independent; the vanishing-Hom theorem
also allows independent ambient and inducing carrier universes. Induction raises
the carrier universe by the maximum with the field universe. The Levi topology
and its instances are exactly the published ones.

This is derived support, not a proof of
`LeviInductionNoSupercuspidalSubquotientStatement`. Existence of the actual
splitting remains a separate prerequisite. The source argument being implemented
is Renard, *Représentations des groupes réductifs p-adiques*, French version
9 July 2026, VI.3.5 (printed pp.146–147 / PDF pp.152–153), VI.1.2 Proposition
(printed p.136 / PDF p.142), VI.2.1 Definition (printed p.137 / PDF p.143),
and VI.5.2 Lemma (printed p.173 / PDF p.179), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proof uses the current Library Frobenius theorem and elementary coproduct
and quotient algebra; it does not assume the source's decomposition theorem.
