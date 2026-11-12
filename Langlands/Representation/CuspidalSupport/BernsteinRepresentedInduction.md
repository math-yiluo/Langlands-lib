# Actual represented and Bernstein standard induction

`bernsteinStandardRepresentedInductionFunctor` uses the original choice-free
standard parabolic, Levi and radical schemes, the published geometric
certificates and the canonical rational-Levi point topology to define actual
represented induction. The entry construction
`bernsteinStandardRepresentedInductionIso` identifies its value on every
smooth representation of that rational Levi with the published literal
standard normalized induction of its canonical pullback. No irreducibility,
cuspidality, finite length, admissibility or association premise is needed.
The carrier universe is the saturated `max uF uV`, as in the original
Bernstein support relation; field and carrier parameters remain independent.

The proof uses the published equality between the represented standard
point images and the literal standard parabolic, Levi and unipotent
subgroups. Both canonical Levi homeomorphisms send each original rational
point to the same ambient point under the original algebraic Levi inclusion.
The generic `rationalInertiaInductionIsoOfEmbeddedLevi` then applies: after
identifying the subgroups and both inverse transport maps, the normalized
induction functors coincide. The implicit subgroup parameters are specified
explicitly to keep Lean's comparison of the original schemes small.

`bernsteinRepresentedInduction` evaluates this functor on an actual
`BernsteinCuspidalDatum`. `bernsteinRepresentedInductionIso` specializes the
entry comparison to give an isomorphism with the original `bernsteinInduction`.
These constructions use no support comparison and prove no decomposition.
The bundled `BernsteinRepresentedCuspidality` pair separately supplies actual
supercuspidality of these data for later use of represented VI.5.4.

This is an internal comparison of the Library's actual-object interfaces.
The source motivation is Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.5.4, printed pp.173–174 /
PDF pp.179–180, and VI.7.1–VI.7.2, printed pp.181–184 / PDF pp.187–190.
Those original passages were read. Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
