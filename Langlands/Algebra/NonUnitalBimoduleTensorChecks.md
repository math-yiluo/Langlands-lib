# Interface and boundary checks for original bimodule tensors

This companion to `Langlands.Algebra.NonUnitalBimoduleTensor` checks its full
interfaces, specified original structures and degenerate examples. Worker 185
authored this Lean/Markdown pair and audited the original sources. Worker 1171
authored the imported tensor-action constructions. The checks are internal
consequences and specializations of those constructions; they are not additional
claims attributed to Renard.

## Source conventions and scope

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The conventions on printed pages 5–7 / PDF11–13 allow nonunital rings and
nonunital module actions, including actions of unital rings. A bimodule has
commuting original left and right actions; nondegeneracy is a separate
condition. I.2.2–I.2.3, printed pages 15–18 / PDF21–24, use residual tensor
actions and naturality in the complex-algebra setting. I.3.2, printed page 20 /
PDF26, explicitly allows the later right corner action on the algebra to be
nonunital.

The registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was also checked on PDF1–2 and PDF18–19. The induction-adjunction direction
and corner-injectivity corrections on PDF1 are incorporated in the governing
2026 PDF24 and PDF26. The old printed-page-314 correction on PDF18–19 requires
a complex vector-space hypothesis. These corrections do not change the
elementary quotient actions checked here.

The imported construction is an internal arbitrary-ring, additive
generalization: all three rings are associative `NonUnitalRing`s, all groups
and actions are their specified original structures, and a right action is a
left action of the opposite ring. It uses exactly
`NonUnitalModuleTensor.Tensor`, its inherited group, pure tensors, maps,
extensionality and universal lift. No unit law, nondegeneracy, coefficient
field, commutativity or nontriviality is assumed.

## Complete declaration interfaces and universes

The first section contains 40 complete, unapplied declaration checks. Each has
an explicitly written full telescope and the term `@declarationName`, rather
than a lambda or an already applied instance. The ring universes `uS`, `uR`,
`uT`, factor universes `uX`, `uY`, target universe `uZ`, and the four further
carrier universes `uX'`, `uY'`, `uX''`, `uY''` remain independent.

These checks cover `leftScalar`, `leftModule`, `rightScalar`, `rightModule`,
their complete scalar-map equalities, `actionsCommute`, `bimodule` and its
four exact fields, `tensor`, one-sided and bimodule tensor maps, both
one-sided projections, whole-map identity and composition, separate
additivity, both fixed-factor functors and their additive/object/map formulas,
all three universal lifts, their underlying-map/projection equalities and all
three bundled uniqueness interfaces. The one-sided module, map and lift
telescopes retain only the actions needed on their respective side.

There are a further 32 unapplied checks, specializing the 16 principal
construction interfaces at each of the following two unequal assignments:

| Universe | First assignment | Second assignment |
| --- | --- | --- |
| `uS` | 0 | 1 |
| `uR` | 1 | 0 |
| `uT` | 0 | 1 |
| `uX` | 1 | 0 |
| `uY` | 0 | 1 |
| `uZ` | 1 | 0 |
| `uX'` | 0 | 1 |
| `uY'` | 1 | 0 |
| `uX''` | 1 | 0 |
| `uY''` | 0 | 1 |

The specialized constructions are the two scalar maps and modules, commutation,
both tensor bundles, the bimodule map and its composition law, both
fixed-factor functors, the two one-sided induced maps, and all three universal
lifts. The tensor carrier and functor codomain retain universe `max uX uY`.

## Competing structures

The next section supplies original ring structures `s₀`, `r₀`, `t₀`,
original factor groups and actions, and unrelated competing ring, group and
action structures as active local instances. It also supplies a competing
additive group and both competing residual modules on the very same original
tensor carrier. Inference witnesses check that the competing structures are
indeed active. These competitors are retained in the declaration context.

Explicit structure arguments then check that `bimodule` still has exactly the
original tensor carrier, published inherited group and named left and right
modules. They check the commutation proof and identify each complete scalar
endomorphism with the published tensor map of the original action Hom and
original identity. The one-sided induced identity maps are checked with the
named original modules on both tensor carriers. The lifts of the canonical
balanced pairing are also checked with the original tensor group and named
target actions. Their balancing proof is the published `tmul_balanced`;
equivariance follows by the defining pure-tensor formulas. None of these checks
identifies an arbitrary competing structure with an original one.

## Subsingleton, zero-action and integer examples

If either factor is subsingleton, the tensor is subsingleton. The proof uses
published pure-tensor extensionality to show its identity additive map is zero,
then compares its values at any two elements. The zero-scalar checks work over
arbitrary rings: a zero remaining left or right action yields the zero whole
scalar endomorphism, by `hom_ext` and `zero_tmul` or `tmul_zero`. A further
example permits all three rings to be zero rings, using `PUnit` at independent
universes.

For the concrete degenerate example, both factors are the additive group
`ℤ`, both original balancing `ℤ`-actions are zero, and both remaining actions
of the unital ring `ℤ` are zero. The biadditive pairing `b(x,y) = x*y` is
balanced because both balancing actions vanish. Its intrinsic additive
quotient lift sends `tmul 1 1` to `1`, so this actual tensor is nonzero.
Every complete remaining scalar endomorphism on it is nevertheless zero.
Applying a putative left or right unit law to `tmul 1 1` contradicts that
nonvanishing. Thus both unit laws actually fail in the checked example.

In a separate scope the factors have the published regular left and right
integer actions. The same multiplication pairing is balanced by associativity;
its intrinsic lift sends `tmul 2 1` to `2`, proving that pure tensor nonzero.
The remaining left action satisfies
`2 • tmul 1 1 = tmul 2 1 ≠ 0`. Local source and tensor instances explicitly
select the zero structures in the first scope and the regular structures in
the second.

These are interface and boundary checks of the original additive
construction. They do not provide recovered coefficient scalars, the unitized
tensor comparison (I.2.1.2), tensor nondegeneracy, associativity, tensor–Hom
adjunctions, exactness, the source forgetful/pseudo-forgetful/induction functors,
or the corner induction and equivalence. Those remain separate successors.
Compilation of this pair is distinct from independent semantic acceptance and
Library publication.
