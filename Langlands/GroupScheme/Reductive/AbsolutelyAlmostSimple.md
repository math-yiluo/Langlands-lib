# Absolute almost-simplicity over a field

Author: Worker 1783.

`Langlands.GroupScheme.IsAbsolutelyAlmostSimple G` is the conjunction of the
published `IsAlmostSimple G` and `IsAlmostSimple` for its base change along
`toAlgebraicClosure k`. It uses exactly the algebraic closure and the
`GroupScheme.baseChange` functor used in `IsConnectedReductive`. The field
`k : Type u` and universe `u` are arbitrary. No characteristic, perfectness,
infinitude or topology condition is imposed.

The source is J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, Definition 19.7 and Notes, printed p.399 /
PDF p.415. The Notes identify geometrically almost-simple groups with
absolutely almost-simple groups. The printed parenthetical ordering of
“simple” and “almost-simple” in the geometric clause is reversed; this
definition uses the almost-simple branch consistently. The meaning of
`IsAlmostSimple` is the published one, based on Milne's official correction
to Definition 19.7, registered as
`milne-2017-algebraic-groups-errata-2026-11-02`, entry for p.399: semisimplicity,
noncommutativity, and the absence of proper nontrivial smooth connected
normal subgroups. It does not silently impose a condition on nonsmooth
normal subgroup schemes.

The conjunction records both the ground-field and geometric conditions
explicitly; no descent equivalence or independence of the chosen algebraic
closure is asserted or proved here. Borel–Tits, *Groupes réductifs* (1965),
registered source `borel-tits-1965-groupes-reductifs`, 6.17–6.21, printed
pp.111–113 / PDF pp.58–60, is the structural application: the factor in
6.21(ii) is almost-simple over the algebraic closure, while the original
group is only assumed almost-simple over its ground field.
