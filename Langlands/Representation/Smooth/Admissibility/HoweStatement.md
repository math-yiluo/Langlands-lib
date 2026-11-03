# Howe's finite-length implication on actual reductive rational points

Worker 1212. This statement unit defines the closed proposition
`Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement`
in `Langlands.Representation.Smooth.Admissibility.HoweStatement`.
It states the implication from finite generation and admissibility to finite
length in Renard VI.6.3.

## Source

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The theorem is stated in VI.6.3, printed page 178 / PDF184; its proof is on
printed page 179 / PDF185. Both pages were read in full.

The source gives an equivalence: a smooth representation has finite length
if and only if it is of finite type and admissible. This declaration selects
the implication proved in the first paragraph of the theorem's proof.
III.1.1, printed page 58 / PDF64, supplies smoothness; III.1.4, printed page 60 /
PDF66, transfers categorical finiteness terminology to smooth representations;
III.1.7, printed page 62 / PDF68, defines admissibility using every open subgroup.
These passages were also read.

## Complete quantifiers and actual objects

All data are quantified inside the proposition. For independent universe
parameters `u` and `uV`, it binds:

- `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`, and
  `IsNonarchimedeanLocalField F`. This retains both characteristic zero and
  positive characteristic local fields.
- The actual group scheme `G : GroupScheme (Spec (CommRingCat.of F))` and
  `hG : IsConnectedReductive G`, the existing smooth connected affine group
  predicate with trivial geometric unipotent radical.
- The derived local instance `hG.isAffineHom`, followed by
  `IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom`.
- The fixed local topology
  `TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X`.
- Every actual `A : SmoothRep.{0, u, uV} ℂ (RationalPoint F G.X)`.

Here `RationalPoint F G.X` is the existing morphism type
`Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X`. Its group law is the
group-scheme point law. Its canonical topology is the existing affine evaluation
topology transported to this identity-test carrier by `rationalPointEquiv`.
The field and scheme universe is `u`; the representation carrier has the
independent universe `uV`. The coefficient field is the actual `ℂ`.

After these binders, the assertion is exactly

```lean
Module.Finite (MonoidAlgebra ℂ (RationalPoint F G.X))
  A.representation.asModule →
    A.IsAdmissible → A.HasFiniteLength
```

The smooth representation already includes smoothness. There is no topology
on its vector-space carrier. The quantifiers include the zero representation.

## Finiteness conventions

The module is the existing `A.representation.asModule`, with its actual
group-algebra action. Finite generation means that finitely many vectors and
their group translates span the representation over `ℂ`. It permits infinite
dimension over `ℂ`.

`A.IsAdmissible` is the existing predicate: smoothness together with
`Module.Finite ℂ` for the fixed-vector space of every open subgroup. Over
`ℂ`, this is finite dimension, agreeing directly with Renard III.1.7.
`A.HasFiniteLength` is the existing
`IsFiniteLength (MonoidAlgebra ℂ (RationalPoint F G.X))
  A.representation.asModule`.

The published comparisons `Langlands.SmoothRep.renardFiniteType_iff` and
`Langlands.SmoothRep.renardFiniteLength_iff` in
`Langlands.Representation.Category.RenardFinitenessProof` identify the
source categorical finite-type and composition-chain predicates with these
actual group-algebra predicates. Their complete signatures quantify
independent coefficient, group, and carrier universes, a commutative coefficient
ring, a group with a supplied topology, and an actual smooth representation.
The two comparisons themselves require no topological-group instance. Their
aggregate `renardFinitenessStatement` retains that instance inside each
component of the published target. Thus these comparisons explain the source
terminology without becoming premises of Howe's implication.

## Status and remaining work

This artifact defines a proposition and supplies no proof of Howe's implication.
The source proof chooses a compact open subgroup fixing a finite generating
family, normal in the fixed special maximal compact and admitting the relevant
Iwahori decompositions. The preceding corollary and exactness of fixed vectors
then bound the length by the dimension of its fixed-vector space. That stronger
bound and the VI.6.3 lemma, proposition, and corollary remain separate obligations.

The existing
`Langlands.Aubert.General.RationalPointsFiniteLengthAdmissibleStatement`
and its proof owner retain the converse implication. An exact proof successor
for this new declaration is to be routed by the parent after independent
statement acceptance and publication. The actual dynamic-Levi comparison,
Jacquet results, and structural compact-open constructions also remain separate.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0
at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
