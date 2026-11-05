# General compact-restriction converse

The closed proposition
`Langlands.Aubert.General.RationalPointFamily.RationalCompactRestrictionCuspidalStatement.{uF,uV}`
states the implication VI.2.1(c) implies (a) in the shared general reductive
framework. This is a statement unit; its proof remains a separate obligation.
It does not alter the whole-category VI.3.5 target. Workers 491 and 6
prepared this formulation.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, VI.2.1: the theorem begins on printed p.137 /
PDF p.143, and the implication (c) implies (a) is proved on printed p.138 /
PDF p.144. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proper-standard Jacquet convention follows Remark 1 on printed p.137.

The proposition copies the complete structural telescope of
`Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`:
an arbitrary nonarchimedean local field, an actual connected reductive group
scheme, an actual maximal split torus and generic cocharacter, the canonical
rational-point topology with the three explicit group topology premises,
`StandardCocharacterStatement`, the actual relative root system and closedness
of each actual standard unipotent subgroup. It installs the same root enumeration
and the same derived actual semidirect decompositions. Field and carrier universes
are independent. There is no restriction to characteristic zero, split groups,
nonempty root systems, irreducible or admissible representations, or finite length.

For every smooth complex representation `A`, the antecedent is
`HasCompactSmoothDualCoefficients` of its actual restriction to
`Plancherel.rationalCommonNormKernel G`. This quantifies over the entire smooth
dual of the restricted action and uses the subgroup topology. The conclusion is
the existing `IsCuspidal` predicate for every proper actual standard Jacquet
functor. Compactness is the antecedent of the implication being proved, not a
structural hypothesis of VI.3.5.

The source proof chooses, for an arbitrary proper standard parabolic and vector,
a compact open fixing subgroup with Iwahori decomposition, and a strictly
contracting element in the common norm kernel (V.3.25). Its powers escape compact
sets. Compact coefficients and averaging force an eventual averaged zero; the
contraction and Jacquet relations then imply that the vector maps to zero.
All existence, averaging, contraction, compact escape and actual Jacquet
comparisons remain proof obligations here. No special compact witness or
representation-theoretic conclusion is added to the telescope.

`Langlands.CuspidalSupport.LeviHarishChandraConverseTheorem` and its proof provide
a possible proof route for product general linear groups over `PadicField`.
They have different field, group, norm-kernel and quasicuspidality predicates;
they do not prove this general proposition. The published
`RationalCuspidalCompactRestrictionStatement` targets only the forward
implication and retains extra chosen geometric antecedents. Neither that
statement nor its proof supplies this converse.
