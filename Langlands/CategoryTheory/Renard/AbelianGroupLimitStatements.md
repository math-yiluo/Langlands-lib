# Renard A.IV.2: concrete products and direct sums of abelian groups

Authors: Worker 709 and Worker 937.

This statement unit uses the existing Cartesian product, `DirectSum`,
single-coordinate inclusions and coordinate embedding. It states their
categorical universal properties and identifies the direct sum with the
finite-support subgroup of the full product. It also states that for a
finite index type the full product with its canonical inclusions is a
coproduct. The declarations are statements only.

Module: `Langlands.CategoryTheory.Renard.AbelianGroupLimitStatements`.
Namespace: `Langlands.Renard.AbelianGroupLimit`.
All five declarations are closed `Prop`-valued definitions.

## Source and provenance

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The example starts at the end of A.IV.2, printed page 257 / one-based
PDF263, and continues in the first paragraph of printed page 258 /
PDF264. It states that every family of abelian groups has the Cartesian
product with pointwise operations and coordinate projections as product;
that its coproduct is the direct sum; that for finite indices this is
the full product with the single-coordinate inclusions; and that for
infinite indices it is the subgroup of functions with finitely many
nonzero coordinates, with the same inclusions. PDF263–265 were read
in full during the source audit; PDF263–264 were reread when authoring
and again before submission. The printed projections read
`p_i : ∏ G_i → G`; the target is evidently the factor `G_i`, which is
how the Lean fan reads them.

The supplementary author errata for the older 2010 edition are registered
as `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
Their PDF18–19 were checked in the Appendix A audit and reread before
submission. They contain no correction to this product/direct-sum
example; the nearby entry for old p.298, l.6 replaces "limilte" by
"colimite" in the preceding inductive-limit sentence, and the 2026 text
already reads "colimite". The 2026 original governs. The published note `notes/renard/appendix-a-corrections.md`
explains the general limit/colimit arrow errors; the present unit uses
actual Mathlib fans, cofans and their universal properties.

The four named propositions, their ordered conjunction, the use of
`Nonempty` for data-valued universality, and the explicit injective
coordinate-map/range formulation are internal packaging of this example.
The coordinate comparison is stated for every index type: its finite case
is valid too. This is a derived uniform strengthening of the source's
infinite-index description. The universe lifting is also internal
packaging, explained below.

## Universes and concrete data

Every component binds `I : Type uI` and
`G : I → AddCommGrpCat.{uG}` internally, with independent universes
`uI` and `uG`. The finite-product component alone adds `[Finite I]`.
No decidable-equality, nonempty-index or finiteness assumption occurs
in the other components.

The actual product carrier `∀ i, G i` and actual direct-sum carrier
`DirectSum I (fun i => G i)` lie in `Type (max uI uG)`. For the categorical
universal properties the diagram therefore has factors

```lean
H i = AddCommGrpCat.of (ULift.{uI} (G i))
```

in `AddCommGrpCat.{max uI uG}`. This avoids restricting the index universe
to the group universe. Each factor is carried to or from its original
group by the actual `AddEquiv.ulift : ULift.{uI} (G i) ≃+ G i`.
Products and direct sums themselves keep their original raw carriers;
the coordinate comparison is between those carriers.

Pointwise abelian-group operations come from the existing Pi instance.
The direct-sum group instance is Mathlib's existing `DirectSum` instance,
implemented on dependent finitely supported functions. All categorical
arrows are actual bundled additive homomorphisms through
`AddCommGrpCat.ofHom`. No substitute groups, category structures,
functors or assumed universal witnesses are introduced.

Single-coordinate maps use classical index equality internally. This is
an implementation choice in the proposition body and supplies no
`DecidableEq I` premise to a theorem using the target. In the Lean file
the three affected bodies are written `by classical; exact ...`; the
tactic block only provides these classical decidable-equality instances,
and the elaborated definitions are definitionally equal (checked by
`rfl`) to the same terms written under `open Classical in`. Both
`DirectSum.of` and `AddMonoidHom.single` in the third component use the
same classical instance.

## The four components

`CartesianProductStatement.{uI,uG}` defines the actual fan with vertex
`AddCommGrpCat.of (∀ i, G i)`. Its leg to `H i` first evaluates coordinate
`i` with `Pi.evalAddMonoidHom`, then lifts that coordinate using the
inverse of `AddEquiv.ulift`. The conclusion is `Nonempty (IsLimit p)`
for this fan. It therefore asserts the product universal property in
`AddCommGrpCat.{max uI uG}`: for every abelian group `A` there and every
family of homomorphisms `f i : A ⟶ H i`, there is a unique homomorphism
`A ⟶ AddCommGrpCat.of (∀ i, G i)` whose composite with each leg is
`f i`.

`DirectSumCoproductStatement.{uI,uG}` defines the actual cofan with vertex
`AddCommGrpCat.of (DirectSum I (fun i => G i))`. Its leg from `H i` first
lowers by `AddEquiv.ulift`, then applies `DirectSum.of`. The conclusion
is `Nonempty (IsColimit c)` for this cofan, asserting the coproduct
universal property: for every abelian group `A` in
`AddCommGrpCat.{max uI uG}` and every family `f i : H i ⟶ A`, there is a
unique homomorphism from the direct sum to `A` whose precomposite with
each leg is `f i`.

`FiniteSupportComparisonStatement.{uI,uG}` uses the existing homomorphism

```lean
e = DirectSum.coeFnAddMonoidHom (fun i => G i)
```

from the direct sum into the full product. It is the conjunction of:

- `Function.Injective e`;
- for every full-product element `x`,
  `x ∈ Set.range e ↔ Set.Finite {i | x i ≠ 0}`;
- for every index `i`,
  `e.comp (DirectSum.of (fun i => G i) i) =
    AddMonoidHom.single (fun i => G i) i`.

Since `e` is an additive homomorphism between abelian groups, its image
is the actual subgroup of the product given by finite support.
Injectivity and the exact image statement identify the direct sum with
that subgroup, and the last equality identifies the inclusions.
No claim is made that the image is proper for every infinite family:
for example, infinitely many trivial factors do not force properness.

`FiniteProductCoproductStatement.{uI,uG}` uses `[Finite I]` and the actual
full-product vertex, with leg from `H i` given by `AddEquiv.ulift`
followed by `AddMonoidHom.single`. Its conclusion
`Nonempty (IsColimit c)` states the source's finite-index coproduct
description. It requires no chosen enumeration or `Fintype I` input.

`AbelianGroupLimitStatements.{uI,uG}` is exactly the right-associated
conjunction in this order:

```lean
CartesianProductStatement.{uI,uG} ∧
  DirectSumCoproductStatement.{uI,uG} ∧
    FiniteSupportComparisonStatement.{uI,uG} ∧
      FiniteProductCoproductStatement.{uI,uG}
```

All inputs and all concrete fan/cofan data are bound inside the
components. Empty, finite and infinite families are retained where
applicable. The file contains no proof of any component.

## Verification

All checks used approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` and the present Lean file. They
are development checks: they supply neither independent acceptance nor a
proof.

- Worker 709's aggregate check `9f146950-fa1a-4ef3-8667-f98948ec697d`
  and full-definition check `68363382-5216-44b5-b3de-1219d42c7b0a`
  passed with zero errors and warnings.
- Worker 937's aggregate check `df102d2d-48f4-48b6-a109-27687dd3bb52`
  passed with zero errors and warnings. Its inspection reports a
  `Prop`-valued definition with level parameters `[uI, uG]` and only the
  axioms `propext`, `Classical.choice` and `Quot.sound`.
- Worker 937's probe `366c8fdb-1ca7-423e-bb50-be1f56f55751` printed all
  five definitions with `pp.universes` and `pp.funBinderTypes`. It checked
  by `rfl` that each component equals the corresponding contract term
  written out directly, with the explicit diagram
  `fun i => AddCommGrpCat.of.{max uI uG} (ULift.{uI} (G i))` and classical
  index equality. It also checked that the aggregate is the
  right-associated conjunction, and instantiated the aggregate at the
  unrelated levels `{3, 5}` and `{5, 0}`.

## Scope and reuse

The construction data come from Mathlib's
`Algebra/Category/Grp/Biproducts.lean`, `Algebra/DirectSum/Basic.lean`,
`Algebra/Group/Pi/Lemmas.lean` and `Algebra/Group/ULift.lean`, inspected
at the pinned project Mathlib version. These are reuse routes for the
eventual proof. This statement unit makes no claim that a proof of the
closed aggregate has been published.

The next source paragraph, the concrete filtered-colimit quotient and
its eventual-vanishing consequence, remains a separate unit. General
cone/cocone comparisons, elementary limit diagrams, ordered systems,
subobject intersections/unions and products of original nonunital
modules also retain their existing owners and scope. This unit does
not complete A.IV, Appendix A or the whole-book program.
