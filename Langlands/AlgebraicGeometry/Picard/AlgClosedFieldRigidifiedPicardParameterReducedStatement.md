# Reducedness of a universal rigidified Picard parameter over an algebraically closed field

`Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardParameterReducedStatement`
is a universe-polymorphic proposition definition (`def … : Prop`). It is a
statement target. The module states it but does not prove it, and adds no
axiom.

## Statement

Fix an algebraically closed field `k : Type u` in an arbitrary universe `u`,
and write

```text
S = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)).
```

The proposition quantifies over every existing `A : AbelianScheme S`, every
parameter scheme `P : Over S`, and every actual rigidified family
`L : RigidifiedFamily A P` on `A ×_S P`, rigidified along the unit section. It
asserts that if

```text
RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L
```

and `LocallyOfFiniteType P.hom`, then `IsReduced P.left`. In words: over an
algebraically closed field, a locally finite type scheme that carries a
universal rigidified line bundle for an abelian scheme is reduced.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldRigidifiedPicardParameterReducedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
      LocallyOfFiniteType P.hom → IsReduced P.left
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard`. The module imports
`Langlands.AlgebraicGeometry.Picard.RelativePicardZero`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. With `pp.fieldNotation false`,
`pp.proofs true` and `pp.funBinderTypes true`, `#print` in the pinned
environment reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardParameterReducedStatement.{u} : Prop :=
∀ (k : Type u) [inst : Field k] [IsAlgClosed k]
  (A : Langlands.AbelianScheme (CategoryTheory.Functor.obj AlgebraicGeometry.Scheme.Spec (Opposite.op ↧k)))
  (P : CategoryTheory.Over (CategoryTheory.Functor.obj AlgebraicGeometry.Scheme.Spec (Opposite.op ↧k)))
  (L : Langlands.AbelianScheme.RigidifiedFamily A P),
  Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.IsUniversal
      (CategoryTheory.Over.hom
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
      (Langlands.AbelianScheme.unitSection A)
      (Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardParameterReducedStatement._proof_1 k A) L →
    AlgebraicGeometry.LocallyOfFiniteType (CategoryTheory.Over.hom P) →
      AlgebraicGeometry.IsReduced (CategoryTheory.Over.left P)
```

Here `↧k` is `CommRingCat.of k`, and `_proof_1 k A` is the auxiliary proof
term that Lean abstracts from `unitSection_comp A`. A private check confirmed
by `rfl` that the conclusion is Mathlib's scheme class
`AlgebraicGeometry.IsReduced`, not the ring-theoretic `IsReduced`.

## The reused definitions

Nothing is redefined here. No new mathematical object is introduced.

- `AbelianScheme S` is the Library's abelian scheme: a commutative group
  scheme over `S` whose structure morphism is smooth, proper and has
  geometrically connected fibres.
- `unitSection A : S ⟶ A.X.left` is the unit section, and
  `unitSection_comp A` is the proof that it is a section of `A.X.hom`.
  `RigidifiedFamily A T` is the existing category of line bundles on
  `A ×_S T` rigidified along the unit section. All three come from
  `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`.
- `RigidifiedLineBundle.IsUniversal … L` is the existing universal property
  of the full rigidified class functor. For every test object `T : Over S`,
  the map from `T ⟶ P` to isomorphism classes of rigidified families on
  `A ×_S T`, given by pulling back `L`, is bijective. It quantifies over every
  scheme over `S`, including nonreduced ones such as the dual numbers over
  `k`. It is not restricted to geometric points or to the `Pic⁰` subfunctor.
- `LocallyOfFiniteType P.hom` is Mathlib's
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `IsReduced P.left` is Mathlib's `AlgebraicGeometry.IsReduced`: every ring of
  sections of the structure sheaf of `P.left` is reduced.
- `IsAlgClosed k` is Mathlib's `IsAlgClosed`.

## Exactly what is and is not assumed

The hypotheses are those of the published arbitrary-field statement
`FieldRigidifiedPicardParameterGeometricallyReducedStatement`, plus
`IsAlgClosed k`. The conclusion is reducedness of `P.left` instead of
geometric reducedness of `P.hom`. That module is not imported, and neither
statement is used to state the other.

The proposition assumes local finite type of `P.hom` and nothing else about
`P`. It does not assume that `P` is of finite type, quasi-compact,
separated, proper or connected. It does not assume a group law or
group-object structure on `P`. It does not assume a polarization of `A`,
an ample line bundle, an existence or representability theorem, a bound on
tangent spaces or on `H¹(A, O_A)`, or any reducedness or smoothness. It
asserts no existence of `P` or `L`: it says only what holds for every pair
`(P, L)` that is universal.

## Provenance

This proposition is derived. It has no verbatim counterpart in the source.
The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`
(PDF page = printed page + 4).

- Chapter VI §3, printed p.95 (PDF p.99). For an abelian variety `X` over a
  field `k`, the source *admits* from the general theory that `Pic_{X/k}`
  is a group scheme with projective connected components. It notes that
  `Pic_{X/k}` also represents the functor `P_{X/k,0}` of line bundles
  rigidified along the zero section.
- Theorem (6.18), printed p.96 (PDF p.100). For an abelian variety `X` over
  a field `k`, the source proves that `Pic⁰_{X/k}` is reduced, hence an
  abelian variety, and that `dim Pic⁰_{X/k} = dim X = dim_k H¹(X, O_X)`.
  Its proof takes an ample line bundle `L` on `X` (not the family `L`
  above). It cites Lemma (2.17) for the fact that `φ_L` has kernel `K(L)`,
  and uses that `K(L)` is a finite group scheme (Lemma (2.19), printed
  p.23, PDF p.27) to get `dim Pic⁰_{X/k} ≥ dim X`. It combines this with
  Corollary (6.6), printed p.90 (PDF p.94), which identifies the tangent
  space at the identity with `H¹(X, O_X)`, and Proposition (6.15), printed
  p.94 (PDF p.98), which gives `dim_k H¹(X, O_X) ≤ dim X`. The theorem
  concerns the identity component `Pic⁰_{X/k}`. It does not state
  smoothness or reducedness of the full Picard scheme.
- Proposition (3.17), printed pp.38–39 (PDF pp.42–43). Let `G` be a group
  scheme locally of finite type over a field `k`. Part (i) says that the
  identity component `G⁰` is an open and closed subgroup scheme. Part (ii)
  says these are equivalent: (a1) `G ⊗_k K` is reduced for some perfect
  field `K ⊇ k`; (a2) `O_{G,e} ⊗_k K` is reduced for some perfect `K ⊇ k`;
  (b1) `G` is smooth over `k`; (b2) `G⁰` is smooth over `k`; (b3) `G` is
  smooth at the origin. The proof of (ii) reduces to the case where `k` is
  algebraically closed and `G` is reduced at the origin. The translations of
  `G` then show that `G` is reduced.

Combining these over an algebraically closed (hence perfect) field `k`:
(6.18) makes `Pic⁰_{X/k}` reduced. Since `Pic⁰_{X/k}` is an open subscheme
containing the origin, the local ring of `Pic_{X/k}` at the origin is
reduced. This is (a2) with `K = k`. Proposition (3.17)(ii) then shows that
the whole group scheme `Pic_{X/k}` is smooth, and in particular reduced.
This reducedness of the full group scheme is the conclusion stated here,
for an arbitrary parameter `P`. The source's admitted representability is
replaced by the hypothesis that the actual family `L` on `A ×_S P` is
universal for all test schemes.

Theorem (6.18) and Proposition (3.17) are proved in the source; the proof
of (6.18) works with the Picard scheme whose existence §3 admits. The Lean
declaration here is only a stated proposition, not a proved theorem.
Proving it is a separate exact-target task, after this statement is
published.

## Remarks on a proof

Classifying the `k`-points of `P` alone does not suffice for this statement.
Reducedness is a property of the nilpotent structure of `P`, which the
`k`-points do not see. A proof must use the universal property on
nonreduced test schemes. For example, with `T` the spectrum of the dual
numbers over `k`, universality identifies the maps `T ⟶ P` with the
isomorphism classes of rigidified families on `A ×_S T`. This is how the
tangent space of `P` at the trivial parameter can be compared with
`H¹(A, O_A)`.

Likewise, the group structure on `P` that the source's translation
argument needs is not a hypothesis here. It must first be built from the
tensor product of rigidified families through the universal property. The
Library module
`Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalGroupObject` does
this in `universalCommGrpObj`, conditional on seven named Library
propositions that it takes as explicit arguments. This module does not
import it.

The planned route compares the tangent space at the trivial parameter with
actual `H¹(A, O_A)` and bounds its dimension using (6.15). It obtains the
opposite local-dimension bound from an ample line bundle `M` on `A` whose
group scheme `K(M)` is finite (Lemmas (2.17) and (2.19)). It then uses
regularity and translations. Each of these inputs must be proved and
published as its own unit before it is used. This module imports none of
them and assumes none of their unproved propositions.

## Intended use

This is the algebraically closed core of the published arbitrary-field
statement `FieldRigidifiedPicardParameterGeometricallyReducedStatement`
(proof task `9cd303c4-a699-432a-8e44-0c6446ebc0df`). That task's final
assembly also needs inputs not stated here, such as passing from an
arbitrary field to an algebraic closure and descending reducedness back.

Worker 1001 wrote the Lean statement and this explanation, checked the
cited source passages and the reused declarations, and compiled the module
in the pinned environment.
