# Subrepresentation splitting from actual Bernstein support uniqueness

Author: Worker 167, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`).
This is a conditional supporting construction. The published
`BernsteinInertialSupportUniquenessStatement` is an explicit premise of every
result; this module does not prove it or either unconditional VI.7.2 target.

`bernsteinSubrepresentationCofanIsColimit` specializes the actual inverse-image
cofan construction to a supplied coproduct whose component at `s` satisfies
the original `bernsteinBlockProperty s`. Its vertex is the actual invariant
subspace of that supplied coproduct; its components are the inverse images
under the original cofan legs. If an irreducible actual subquotient appeared
in two original components, their block conditions would give two inertial
supports of its specified `SmoothRep.universeLift.{uF}`. The named uniqueness
premise identifies the indices. Thus distinct components share no irreducible
actual subquotient, and the generic coproduct restriction theorem applies.

`bernsteinSplitSubrepresentation_of_supportUniqueness` states the resulting
component-splitting conclusion in the exact `Renard.IsCoproductOfComponents`
form used by the first Lemma of VI.7.2. Each restricted component remains
in its original block by actual subquotient transitivity. The support
predicate is applied to the prescribed universe lift throughout; there is
no replacement partition, supplied projector or alternative block property.

`bernsteinBlock_offDiagonalHomsZero_of_supportUniqueness` proves the
Hom-vanishing part of the decomposition under the same prerequisite and
without a global splitting assumption. A nonzero morphism has an
irreducible actual subquotient of its image. That is an actual subquotient
of both its source and target. Their block conditions and uniqueness
contradict distinct indices.

All results retain the nonarchimedean local field, actual connected
reductive standard family, canonical rational-point topology and independent
field/carrier universes. Neither existence of support nor a statement
covering all irreducibles is needed for these conditional steps. To obtain
the exact unconditional `BernsteinSplitSubrepresentationStatement`, the
named uniqueness proposition must still be proved uniformly at the original
quantifiers. The full decomposition additionally requires the objectwise
coproduct existence theorem.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.7.2, first Lemma, printed p.182 / PDF
p.188, and off-diagonal vanishing after (VI.7.2.2), printed p.184 / PDF
p.190. The support partition is recalled at the end of VI.7.1, printed
p.181 / PDF p.187. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 167 read these pages. This is a derived specialization of
`DisjointConstituentCoproduct`, with its prerequisite recorded explicitly;
it does not discharge the support association or uniqueness assertions
used by the source.
