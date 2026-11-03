# Finite-Galois effective descent for affine group schemes

Author: Worker 1442.

This module states effective descent and compatible-morphism descent for actual
possibly noncommutative affine group schemes. It defines three propositions; it
supplies no proof of these propositions. The main target is
`Langlands.GroupScheme.AffineGroupSchemeFiniteGaloisDescentStatement.{u}`.
It is the conjunction of the object and homomorphism components described below,
with the same arbitrary universe `u` in both.

## Fields, affineness and actual group schemes

Both components quantify over all `k L : Type u`, instances `Field k`, `Field L`,
and `Algebra k L`, followed by `FiniteDimensional k L` and `IsGalois k L`.
Thus `L/k` is finite, normal and separable. The characteristic is arbitrary and
`k` may be imperfect. There is no perfectness, smoothness, reducedness, finite
presentation or finite-type premise on a group scheme.

In each component the base morphism is the actual scheme morphism

```text
p : Spec L ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k L)).
```

Here and below `Spec L` abbreviates `Spec (CommRingCat.of L)` in prose.
`GroupScheme S` is the published category `Grp (Over S)`. Its objects carry
actual multiplication, unit and inverse morphisms, and its homomorphisms
preserve these operations. `baseChange p` is the actual scheme-pullback functor
lifted to these group objects. No commutativity of the group law is assumed.

Affineness is expressed by `IsAffineHom G.X.hom`, where `G.X.hom` is the
structure morphism of the underlying scheme to its field spectrum. Because
the base is affine, this is equivalent to affineness of `G.X.left`.
The scheme and its structure morphism are part of the actual group object;
there is no abstract coordinate-algebra substitute in the formal target.

## Object effectivity

`AffineGroupSchemeFiniteGaloisObjectDescentStatement` quantifies, after the
field data, over every `H : GroupScheme (Spec L)`, its affineness premise, and
every `datum : Descent.Datum p H`. Its conclusion is exactly

```text
∃ solution : Descent.Solution datum, IsAffineHom solution.obj.X.hom.
```

The imported `Descent.Datum` contains an actual isomorphism from the first
pullback of `H` to the second over `Spec L ×_(Spec k) Spec L`, with its
triple-overlap cocycle. The pullback comparisons and first-to-second convention
are those of the published `Langlands.GroupScheme.Descent.Data` pair.

`Descent.Solution datum` has the separate fields

```text
obj        : GroupScheme (Spec k)
iso        : (baseChange p).obj obj ≅ H
compatible : Descent.Compatible (Descent.canonicalDatum p obj) datum iso.hom.
```

Consequently the existential conclusion supplies an actual affine group scheme
`C := solution.obj` over `Spec k` and an actual group-scheme isomorphism
`p*C ≅ H` respecting the supplied datum. Neither a descended object, a solution,
a chosen invariant Hopf algebra nor any equivalent effectivity premise is an
input. The affineness conclusion is explicit because the general imported
`Solution` structure has no affineness field.

## Compatible homomorphisms

`AffineGroupSchemeFiniteGaloisHomDescentStatement` quantifies, after the field
data, over every pair `C D : GroupScheme (Spec k)`, an affineness premise for
each, and every actual homomorphism `f : p*C ⟶ p*D`. Its only further premise is

```text
Descent.Compatible (Descent.canonicalDatum p C) (Descent.canonicalDatum p D) f.
```

It concludes

```text
∃! g : C ⟶ D, (baseChange p).map g = f.
```

This means existence of a homomorphism over `k` recovering `f` under actual base
change, and equality of every other homomorphism with the same base change to
that witness. Uniqueness concerns actual homomorphisms in `Grp (Over (Spec k))`.
The imported `canonicalDatum_compatible` already proves that base change of
any homomorphism respects these canonical data.

For `dC := Descent.canonicalDatum p C` and `dD := Descent.canonicalDatum p D`,
the compatibility premise is the actual overlap equation

```text
(baseChange (Descent.fst p)).map f ≫ dD.overlap.hom =
  dC.overlap.hom ≫ (baseChange (Descent.snd p)).map f.
```

All terms are actual group-scheme morphisms over the double overlap. Equality
there retains the represented group functor on every test scheme over that
base, including nonreduced tests. It is not a condition checked only on
field-valued points. This distinction also applies to the solution's
compatibility field and is necessary for nonsmooth and nonreduced groups.

## Original sources and derived packaging

The source is J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of
Finite Type over a Field* (2017), Appendix A.64 and its continuation, printed
pp.580–581 / PDF pp.596–597; A.66, printed p.581 / PDF p.597; and A.81, printed
p.585 / PDF p.601. Registered source: `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
These original passages were read. The complete retained official errata
snapshot of 2026-11-02 was also read: source
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
It gives no correction to A.64, A.66 or A.81.

A.64 gives the equivalence between `k`-vector spaces and `L`-vector spaces with
continuous semilinear Galois action, without a dimension restriction on those
vector spaces. Its continuation explicitly extends the equivalence to Hopf
algebras with compatible semilinear action. In the finite Galois case the
Galois group is finite, so the continuity condition adds no restriction.
A.66 gives existence and uniqueness of descended compatible morphisms in its
stated setting of algebraic schemes, with separated target. A.81 supplies the
Čech datum and canonical datum used by the imported definition module.

The present target is derived group-object packaging, with arbitrary affine
coordinate algebras; it is not a claim that the printed algebraic-scheme scope
of A.66 or A.81 already has these exact quantifiers. The derivation of the
intended statement is as follows. For finite Galois `L/k`, the usual splitting
`L ⊗[k] L ≅ ∏_(γ ∈ Gal(L/k)) L` identifies affine Čech descent data with
semilinear Galois data on the coordinate algebra. The cocycle gives the action
law. An affine group scheme corresponds contravariantly to a commutative Hopf
algebra; the group need not be commutative, since its Hopf coproduct need not
be cocommutative. A datum of group-scheme isomorphisms respects all the Hopf
structure maps. The tensor-compatible vector-space descent of A.64 therefore
descends the algebra multiplication and unit, coproduct, counit and antipode.
Faithfulness reflects the Hopf identities. Taking its spectrum gives the
descended affine group and the compatible pullback isomorphism.

For compatible morphisms, the dual Hopf-algebra map descends by full
faithfulness of the same semilinear equivalence. Its compatibility with the
Hopf operations is reflected by faithful scalar extension, giving the unique
actual group-scheme homomorphism in the second component. These algebraic
arguments allow arbitrary-dimensional coordinate algebras and arbitrary
characteristic. They justify the extended affine scope and its use over
imperfect fields; no finite-generation or smoothness argument is required.

This paragraph explains mathematical provenance, not an implemented Lean
proof. Both effectivity and compatible-morphism descent remain proof
obligations for the main proposition. The module adds only this new
Lean/Markdown pair, and makes no changes to
`SimplyConnected.CoverExistenceStatement` or any pair it imports. Constructing
cover data and descending semisimplicity, simple connectedness or
central-isogeny properties remain separate obligations.
