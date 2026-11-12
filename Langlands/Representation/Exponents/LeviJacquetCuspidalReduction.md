# Cuspidal vanishing from the represented geometric lemma

Author: Worker 1781. This supporting contribution implements the consumer deduction in Renard
VI.5.3(i), printed p.173 / PDF p.179, from the exact represented geometric
lemma. It is conditional on that still separate theorem and does not discharge
the unconditional target. The Prop-valued definition
`LeviJacquetInductionVanishingGeometricReductionStatement` names this
implication. The theorem
`leviJacquetInductionVanishing_of_geometricLemma` proves it by an explicit
argument from `RepresentedGeometricLemmaStatement`.

The original is Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original VI.5.1–VI.5.4 and VI.2.1, VI.3.5–VI.3.6 passages were read
directly.

The geometric-lemma intersection data identify the two intersection Levi
groups by conjugation by the representative `z`. If the source intersection
parabolic is the whole group `M`, its rational Levi inclusion is an
isomorphism, by the published `FullParabolicLevi` result. Composing its
inverse with the inverse intersection isomorphism realizes `M` as a Levi
subgroup of `L`, with the ambient equation for conjugation by `z⁻¹`.
Consequently the nonconjugacy hypothesis of VI.5.3(i) makes every source
intersection parabolic proper. Supercuspidality kills its Jacquet module.
Pullback and induction on its zero carrier remain zero. The evaluated actual
finite filtration, and the natural isomorphisms of its graded pieces, then
make the total Jacquet module zero.

The reduction retains the original field and carrier universes and every
quantifier in the conclusion statement. It assumes the full proposition
`RepresentedGeometricLemmaStatement` explicitly, without replacing its
scheme-level intersection or normalized graded-piece obligations by weaker
surrogates.

The local instances have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and local
instance scope are unchanged.
