# The irreducible-existence assertions of Renard III.1.4

Worker 6. `Langlands.SmoothRep.RenardIrreducibleExistenceStatement` states the
three assertions at the end of III.1.4 using the existing actual smooth
representation category and Renard's source categorical finiteness predicates.

## Exact statement and maps

Let `k` be a field and `G` a topological group. For every actual
`A : SmoothRep k G` with a nontrivial carrier, the proposition asserts:

1. There is an irreducible smooth `B` with `IsSubquotient B A`.
2. If `Langlands.Renard.IsFiniteTypeObject A`, there is an irreducible smooth
   `B` with `IsQuotient B A`.
3. If `Langlands.Renard.IsFiniteLength A`, there is an irreducible smooth
   `B` with `IsSubrepresentation B A`.

Every witness belongs to `SmoothRep.{uK, uG, uV} k G`, at the original carrier
universe. The field, group and carrier universes are independent.
`IsTopologicalGroup G` is quantified inside the proposition. The
`Nontrivial A` antecedent applies to all three conjuncts.

The predicates and maps are the unchanged constructions from
[the smooth category](../Category/Basic.md) and
[its subquotients](../Category/Subquotients.md):

- Irreducibility is simplicity of the actual invariant-submodule lattice,
  including nonzeroness.
- `IsSubquotient B A` supplies an actual invariant submodule of `A`, an actual
  invariant submodule of its smooth subrepresentation, and an isomorphism from
  `B` to their canonical quotient.
- `IsQuotient B A` supplies a morphism `A ⟶ B` whose underlying intertwiner
  is surjective.
- `IsSubrepresentation B A` supplies a morphism `B ⟶ A` whose underlying
  intertwiner is injective.

Finite type remains the actual categorical subobject-union and nonempty-chain
predicate from
[`RenardFiniteType`](../../../Langlands/CategoryTheory/RenardFiniteType.md).
Finite length remains existence of a categorical composition chain with
simple successive cokernels from
[`CompositionChains`](../../../Langlands/CategoryTheory/Renard/CompositionChains.md).
Neither predicate is replaced by finite dimension, finite presentation,
admissibility or a condition on the size of fixed spaces. The comparison with
group-algebra finite generation and the existing `A.HasFiniteLength` predicate
is a separate interface obligation.

## Source and the nonzero qualification

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained PDF is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

III.1.4, printed page 60 / PDF66, first gives the equivalence with
nondegenerate Hecke modules. Its final paragraph transfers the terminology of
A.VI.3 to smooth representations and states the three existence assertions.
A.VI.3, printed pages 263–264 / PDF269–270, defines simple objects and
composition chains and gives the underlying categorical simple-quotient
assertions. A.I.2–A.I.3, printed pages 248–249 / PDF254–255, supplies the
categorical finite-type convention. These original passages were read.

The final sentence of III.1.4 does not state the nonzero qualifications
explicitly. They are necessary for each clause. The zero representation is
smooth, is of finite type, and has a composition chain of length zero.
Every subrepresentation and quotient of it is again zero, whereas
irreducibility requires nonzeroness. Thus it has none of the three asserted
irreducible witnesses. A.VI.3 explicitly defines a simple object to be
nonzero, and its finite-type simple-quotient Proposition (i) explicitly assumes
a nonzero object. The current target makes the corresponding necessary
qualification explicit throughout. This is a mathematical diagnosis of the
printed summary, without a claim of an author-issued erratum.

The imported predicates already document their source repairs, including
nonempty chains for finite type and the successive-factor index range for
composition chains. The current unit preserves those predicates unchanged.

## Generality and proof boundary

Renard's Chapter III setting is complex representations of a t.d. group, with
the t.d. convention of II.1.1, printed page 30 / PDF36. The current target
deliberately generalizes to every coefficient field and topological group.
The rationale is algebraic: invariant submodules and their quotients inherit
smoothness, and their order is the submodule order of the actual group-algebra
module. Proving the existence assertions at this generality remains required.

No local compactness, total disconnectedness, countability, finite dimension,
admissibility, algebraic closedness or characteristic restriction is imposed.
No topology is supplied on the representation carrier. No Grothendieck, AB6,
finiteness-comparison or Hecke-equivalence premise is assumed: any use of such
results must be justified for the actual smooth category in the later proof.

The published `Langlands.SmoothRep.exists_irreducible_subquotient` in
`Langlands.Representation.Smooth.ConstituentSupport` assumes
`A.HasFiniteLength`. It is a reuse lead for that restricted case; the first
conjunct here has no finiteness hypothesis. The generic categorical
`SimpleQuotient` and finite-length results are also reuse leads with their
actual hypotheses and comparisons retained.

This file contains one proposition definition and no proof of it.
Independent statement review and publication must precede an exact-target
proof task. The Hecke-module equivalence and the rest of Chapter III retain
their separate obligations.

Prepared environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`.
