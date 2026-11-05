# Simultaneous good reductive and parabolic spreading

This module defines actual paired model data and an unproved existence
proposition. The exact target is
`Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading.ExistenceStatement.{u}`.
It quantifies over every number field `F : Type u`, every actual group scheme
`G` over `Spec F` satisfying the published `IsConnectedReductive G`, and every
actual group-scheme homomorphism `p : P ⟶ G` satisfying the published
`IsParabolicSubgroup p`. These are its only mathematical premises.

The conclusion supplies a finite set `S : Finset (Langlands.Global.FinitePlace F)`
and nonempty `ModelData R F p`, where
`R = (S : Set (Langlands.Global.FinitePlace F)).integer F` is Mathlib's actual
S-integer subalgebra of `F` over its ring of integers. Finite places here are the
nonzero prime ideals of that ring, through the published height-one-spectrum
alias. Infinite places are already omitted by this indexing convention; no
extra choice of an arithmetic base ring is supplied. The inherited
`Algebra R F` is the subtype inclusion. The fraction-ring instance for
subalgebras of a fraction field, imported from
`Mathlib.RingTheory.Localization.AsSubring`, gives `IsFractionRing R F`.
These instances are inferred in the conclusion, rather than extra hypotheses.

## Actual paired models and comparison square

`ModelData` is also usable over an arbitrary domain `R` with its specified
fraction field `F`. It supplies `ambient : IntegralModel R F G` and
`parabolic : IntegralModel R F P`. Both are actual affine, flat, locally
finite type group schemes over `Spec R`. Their affineness also gives
quasi-compactness of the structure maps, so they are of finite type.
Their `genericIso` fields are group-scheme isomorphisms from their actual
pullbacks along `Spec.algebraMap R F` to the originally supplied `G` and `P`.

The field `inclusion : parabolic.Hom ambient p` reuses `IntegralModel.Hom`.
It supplies a single homomorphism of the integral group schemes and the exact
generic comparison equality

```lean
(baseChange (Spec.algebraMap R F)).map inclusion.hom ≫ ambient.genericIso.hom =
  parabolic.genericIso.hom ≫ p
```

Thus it extends this particular supplied inclusion, with both original groups
and their group operations retained. `closedImmersion` asserts
`IsClosedImmersion inclusion.hom.hom.hom.left` on its underlying scheme map.
The model's ambient group satisfies the published `IsReductive` predicate;
`parabolicSmooth` separately asserts smoothness of the structural morphism of
the parabolic model.

## Exact field-valued fibres

For every `k : Type u` with `[Field k] [Algebra R k]`, all three fibre fields
use the actual base morphism `Spec.algebraMap R k`. They assert:

- `fieldReductive`: the pullback of the ambient group satisfies the current
  `IsConnectedReductive` predicate;
- `fieldParabolic`: the base change of the same `inclusion.hom` satisfies the
  current `IsParabolicSubgroup` predicate;
- `fieldConnected`: the underlying scheme of the corresponding pullback of
  the parabolic model has `ConnectedSpace`.

This includes the canonical residue-field algebras at points of `Spec R`,
their algebraic closures, and every other field-valued point in the same
universe. A field-valued point can factor through a residue field and a field
extension; the expression above is its direct pullback. The generic
specialization `k = F` uses the canonical inclusion and the displayed square.
The set `S` and both models are chosen before all these field-valued tests.

The meanings of the existing predicates matter here. `IsReductive` over a
scheme means smooth and affine with geometric fibres satisfying
`IsPseudoReductive` over the chosen algebraic closures of residue fields.
`IsConnectedReductive` over a field means smooth, connected and affine with
trivial unipotent radical after base change to its algebraic closure. The
field parabolic predicate means a smooth closed subgroup whose algebraic
closure base change contains a Borel, through an actual factorization.
It does not carry a `ConnectedSpace` field for the parabolic group. Hence the
explicit connectedness conclusion is retained as its own field.

In the usual theory, reductive group schemes and parabolic subgroup schemes
have these stable fibre properties. Expressing that theory through the
Library's precise predicates still requires formal comparison and
base-change lemmas, including pullback composition and geometric
unipotent-radical/Borel comparisons. This module states their needed
consequences on the actual fibres; it does not prove those comparisons or
infer the fibre conclusions merely from finite-type group descent.

## Sources and derivation

The source is Getz and Hahn, *An Introduction to Automorphic
Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The relevant original passages are Proposition 2.4.8 and its proof, printed
pp.61-62 / PDF pp.78-79, and Proposition B.3.1 with its proof and
Theorems B.3.2-B.3.3, printed pp.544-547 / PDF pp.549-552. The registered
October 2026 errata `getz-hahn-2024-errata-2026-10`, SHA256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
were read in full (PDF pp.1-5); they do not amend these passages.

Proposition 2.4.8 begins with an actual model, obtains smoothness after
enlarging the finite set, and cites Conrad's reductive-group-scheme results.
The opening of section B.3 explicitly uses a schematic closure in a faithful
representation to obtain a reductive model after a finite enlargement.
Proposition B.3.1 then extends a supplied parabolic by its schematic closure
after another finite enlargement. Its statement includes a chosen Levi
decomposition, but Theorem B.3.3 supplies such a decomposition and a
cocharacter over the field. These are auxiliary choices in the source route,
not premises of the proposition here. Theorem B.3.2 supplies smoothness and
connected fibres of the dynamic parabolic and its parabolic property in the
reductive setting. The source proves more Levi and unipotent-radical data
than the present interface retains.

The paired `ModelData` and the universal field-valued formulation are an
internal derived packaging of these passages with the current Library
structures. They are not a verbatim numbered assertion in the book.
The source's cited Conrad, Poonen, Milne and Springer results are reported
here only as steps of the Getz-Hahn proof; this module does not independently
claim their formalization or cite unread originals as additional sources.

## Remaining proof and consumer obligations

No proof of `ExistenceStatement` is given here. Its proof must construct one
finite S-integer base, both models and the extending closed immersion;
establish reductivity and smoothness over that base; and justify all three
field-valued clauses using the exact existing predicates. Actual finite-type
group-object descent can contribute to this work but does not by itself
establish reductivity, parabolicity or connected fibres.

All quantifiers and data are universe-polymorphic in `u`; the tested fields
are explicitly in `Type u`. The proposition retains non-split and anisotropic
groups and the improper parabolic `P = G`. It assumes no positive rank,
properness of the parabolic, splitness, supplied cocharacter, Levi, model or
local decomposition.

The intended consumer is the integral Iwasawa family target
`Langlands.Global.IntegralIwasawaFamily.ExistenceStatement`. Local smooth
lifting, integral torsors, proper flag quotients and covering are separate
work coordinated with Worker 1654; adelic coordinate and gluing comparisons
belong to Worker 1430. Compactness, maximality and Iwasawa decompositions are
not conclusions of this module. Worker 1572 authored this statement and its
packaging for task `2a9028f9-18cc-46c2-9ffc-12753494e10d`, published by
Workers 1641 and 1654.
