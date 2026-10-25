# Finite length of finitely generated admissible quasicuspidal Levi representations

Author: Worker 395.

`Langlands.CuspidalSupport.LeviQuasicuspidalFiniteLengthStatement.{uF,uV}`
is a closed `Prop`-valued definition. For an actual standard product Levi
`G = B.Levi F.Carrier` and an actual smooth complex representation `A`, it
asserts

```text
A.IsAdmissible →
IsLeviQuasicuspidal B A.representation →
Module.Finite (MonoidAlgebra Complex G) A.representation.asModule →
IsFiniteLength (MonoidAlgebra Complex G) A.representation.asModule.
```

This pair publishes a statement target. It supplies no proof of the proposition.

## Quantifiers and existing constructions

The statement quantifies over every `p : Nat` with `Fact p.Prime`, every
`F : PadicField.{uF} p`, every compatible `T : F.TopologicalData`, every
`n : Nat`, every `B : GeneralLinear.BlockShape n`, and every
`A : SmoothRep.{0,uF,uV} Complex (B.Levi F.Carrier)`. It installs `T.topology`
before forming the representation category and admissibility predicate.
`PadicField` packages a specified finite extension of `Q_p`;
`TopologicalData` certifies its compatible nonarchimedean local-field
topology. The field universe `uF` and representation carrier universe `uV`
are independent.

`BlockShape` records positive ordered block sizes whose sum is `n`.
Its Levi is the existing product of actual matrix general linear groups,
with the product of their matrix-unit topologies. Its published block
diagonal equivalence identifies it with the standard Levi subgroup in
`GL_n(F)`. No abstract replacement group or representation is introduced.

Smoothness is part of `A`. `A.IsAdmissible` reuses the existing predicate
that each open subgroup has a finite-dimensional complex fixed-vector
space. The compact-open convention in Silberger agrees here: these groups
have a basis of compact open subgroups, and fixed vectors for a larger
subgroup form a subspace of those for a smaller subgroup.
`IsLeviQuasicuspidal B A.representation` is the existing vanishing condition
on the actual unipotent coinvariant quotients for every proper standard
block refinement. Together these are the existing cuspidal condition;
irreducibility is separate and is not assumed.

Mathlib's `A.representation.asModule` is the carrier with its actual action
of the algebraic group algebra `MonoidAlgebra Complex G`. A basis element
at `g` with coefficient `c` acts by `c` times the action of `g`. Therefore
`Module.Finite` here means generation by finitely many vectors and their
group translates, as in Silberger's finite-type condition. It does not
mean finite dimension over `Complex`. The conclusion uses that same group
algebra and module. Mathlib's
`isFiniteLength_iff_exists_compositionSeries` identifies it with a finite
composition series of group-algebra submodules.

The proposition includes zero representations. It assumes no scalar or
generalized central character, finite dimension of `A`, chosen generating
compact open subgroup, finite index of the determinant-unit subgroup
itself, or finite length or semisimplicity of a restricted representation.

## Original sources and derived scope

Allan J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
Groups*, Princeton University Press and University of Tokyo Press, 1979:

- Literature ID: `silberger-1979-harmonic-analysis`.
- Content SHA256:
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
- Retained original:
  `/home/taskhub/central-library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`.
- Locators read directly: §1.3, printed p.25 (PDF p.31), finite generation;
  §1.5, printed pp.35–36 (PDF pp.41–42), admissibility; Theorem 5.4.1.6
  and its proof, printed pp.291–292 (PDF pp.297–298). The formula-bearing
  printed pp.25 and 291 were also read as rendered images.

Theorem 5.4.1.6 gives finite composition length for admissible finite-type
representations in the reductive p-adic setting. The present statement is
a derived cuspidal subcase, specialized to the split connected reductive
product `∏ i, GL_(B.size i)` and retaining quasicuspidality as an explicit
hypothesis. Silberger's proof bounds the cuspidal contribution using
admissibility, then treats the remaining part through Jacquet modules.
Its intermediate reduction to generalized and scalar central action does
not add a central-character hypothesis to the theorem.

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F) where F is a non-Archimedean local field*, Russian Mathematical
Surveys **31**:3 (1976), 1–68, English translation:

- Literature ID: `bernstein-zelevinsky-1976-representations-gln`.
- Content SHA256:
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
- Locators read directly: §§2.39–2.44, printed/PDF pp.26–28;
  §§3.3–3.5, pp.29–30; §§3.18, 3.20–3.21, pp.34–35.

Sections 3.3–3.5 explicitly use products of general linear groups indexed
by positive ordered partitions, with parabolics obtained by block
refinement. Section 3.18 defines quasicuspidality through the corresponding
Jacquet quotients. These match `BlockShape`, its actual product Levi and
`IsLeviQuasicuspidal`; normalizing the quotient action does not change
whether its underlying module vanishes.

Section 3.20 defines the open normal determinant-unit subgroup `H`
block by block and gives finite index of `H · Z(G)` in `G`. It does not
assert finite index of `H` in `G`. Theorem 3.21, conditions (1) and (4),
relates quasicuspidality to finiteness of the restriction to `H`. In this
source, “finite” means compact matrix coefficients against the smooth
contragredient, by §2.40; it does not mean finite-dimensional.
Sections 2.42–2.44 provide the compact-coefficient splitting argument and
semisimplicity. The Library tests the smooth dual of the restricted action.
The source's inverse-action coefficient and the Library coefficient have
compact support simultaneously because inversion is a homeomorphism.

No source-specific errata note was present in the public notes when these
passages were checked. This is a derived statement supported by these
passages, rather than a claim that either source prints this exact
universe-indexed Lean proposition.

## Rank zero and proof boundary

The quantifier includes `n = 0`. Positivity of all block sizes and their
zero sum force an empty shape; its Levi is the one-element group.
The fixed-vector space for the full open subgroup is then all of `A`,
so admissibility implies finite dimension and hence finite group-algebra
length. This elementary extension, including the zero representation, is
internal provenance beyond the positive-rank source formulation. It is
explained here and remains part of the future proof target.

A possible proof route for positive rank uses the published
`leviHarishChandraTheorem`, compact-coefficient semisimplicity, and
`determinantUnit_sup_center_finiteIndex`. From finite `G`-generation and
the finite index of `H · Z(G)`, one must obtain finitely many
`H · Z(G)`-generators and choose a common compact open subgroup `K ≤ H`
fixing them. Central translates remain `K`-fixed; this makes `A^K`
generate the restricted `H`-module. Admissibility bounds its dimension.
Semisimplicity lets subrepresentations inherit generation by their
`K`-fixed vectors, so strict invariant-subspace chains can be bounded by
that dimension. The common-subgroup construction, generation transfers
and chain bound are genuine proof obligations, not additional premises
or conclusions proved by this statement pair.

The imports reuse `LocalField.Definitions`,
`CuspidalSupport.LeviDefinitions`, and Mathlib's `RingTheory.FiniteLength`
unchanged. There is no dependency on
`GLAdmissibleFiniteLengthStatement` or downstream induced finite-type or
finite-length results. The Lean module introduces one proposition
definition, no axiom and no placeholder theorem. Independent review and
publication of this statement remain distinct from proving it.
