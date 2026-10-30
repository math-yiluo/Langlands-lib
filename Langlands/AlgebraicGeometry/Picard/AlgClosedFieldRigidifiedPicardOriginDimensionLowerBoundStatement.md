# A local-dimension lower bound at the origin of a universal rigidified Picard parameter

`Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement`
is a universe-polymorphic proposition definition (`def … : Prop`). It is a
statement target. The module states it but does not prove it, and adds no
axiom.

## Statement

Fix an algebraically closed field `k : Type u` in an arbitrary universe `u`,
and write `S = Spec (CommRingCat.of k)`. The proposition quantifies over

- every abelian scheme `A : AbelianScheme S`;
- every parameter scheme `P : Over S` and every actual rigidified family
  `U : RigidifiedFamily A P` on `A ×_S P`, rigidified along the unit
  section, together with a proof `hU` that `U` is universal in the
  all-test-scheme sense
  `RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) U`;
- every natural number `g`.

It asserts: if `P.hom` is locally of finite type and `A` has relative
dimension `g`, then for every line bundle `L` on `A.X.left` such that only
finitely many `k`-rational points `x` of `A` satisfy `t_x^*L ≅ L`,

```text
(g : WithBot ℕ∞) ≤ ringKrullDim (P.left.presheaf.stalk (fullPicardOriginPoint k A U hU)).
```

In words: over an algebraically closed field, if some line bundle on `A` is
preserved by only finitely many rational translations, then the local ring
of the parameter scheme `P` at its origin has Krull dimension at least the
relative dimension of `A`.

This is a conditional statement. It does not assert that such an `L`
exists, and it does not assert that any universal pair `(P, U)` exists.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (A : AbelianScheme (Spec (CommRingCat.of k)))
    (P : Over (Spec (CommRingCat.of k))) (U : RigidifiedFamily A P)
    (hU : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A)
      (unitSection_comp A) U)
    (g : ℕ),
    LocallyOfFiniteType P.hom → A.HasRelativeDimension g →
      ∀ (L : LineBundle A.X.left),
        Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X //
          Nonempty ((LineBundle.pullback
            (GroupScheme.translation A.toGrp x).left).obj L ≅ L)} →
        (g : WithBot ℕ∞) ≤
          ringKrullDim (P.left.presheaf.stalk (fullPicardOriginPoint k A U hU))
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory AlgebraicGeometry` before the namespace and
`open Langlands.AlgebraicGeometry.Picard` inside it. The body is exactly
the one in the task objective. The module imports
`Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent`,
`Mathlib.AlgebraicGeometry.Properties` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`.

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiles the
module with no errors or warnings and reports
`statement_returns_prop: true`. The only axioms are `propext`,
`Classical.choice` and `Quot.sound`. With `pp.fieldNotation false`,
`pp.proofs true` and `pp.funBinderTypes true`, `#print` reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u} : Prop :=
∀ (k : Type u) [inst : Field k] [IsAlgClosed k] (A : Langlands.AbelianScheme (AlgebraicGeometry.Spec ↧k))
  (P : CategoryTheory.Over (AlgebraicGeometry.Spec ↧k)) (U : Langlands.AbelianScheme.RigidifiedFamily A P)
  (hU :
    Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.IsUniversal
      (CategoryTheory.Over.hom
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))
      (Langlands.AbelianScheme.unitSection A)
      (Langlands.AbelianScheme.AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement._proof_1 k A) U)
  (g : ℕ),
  AlgebraicGeometry.LocallyOfFiniteType (CategoryTheory.Over.hom P) →
    Langlands.AbelianScheme.HasRelativeDimension A g →
      ∀
        (L :
          Langlands.AlgebraicGeometry.Picard.LineBundle
            (CategoryTheory.Over.left
              (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))),
        Finite
            { x :
              CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec ↧k)) ⟶
                CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) //
              Nonempty
                (CategoryTheory.Functor.obj
                    (Langlands.AlgebraicGeometry.Picard.LineBundle.pullback
                      (CategoryTheory.Over.Hom.left
                        (Langlands.GroupScheme.translation
                          (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) x)))
                    L ≅
                  L) } →
          ↑g ≤
            ringKrullDim
              ↑(TopCat.Presheaf.stalk
                  (AlgebraicGeometry.PresheafedSpace.presheaf
                    (AlgebraicGeometry.SheafedSpace.toPresheafedSpace
                      (AlgebraicGeometry.LocallyRingedSpace.toSheafedSpace
                        (AlgebraicGeometry.Scheme.toLocallyRingedSpace (CategoryTheory.Over.left P)))))
                  (Langlands.AbelianScheme.fullPicardOriginPoint k A U hU))
```

Here `↧k` is `CommRingCat.of k`, and `_proof_1 k A` is the auxiliary proof
term that Lean abstracts from `unitSection_comp A`. `AlgebraicGeometry.Spec ↧k`
is definitionally the `Scheme.Spec.obj (Opposite.op ↧k)` used by
`fullPicardOriginPoint`, and the module elaborates without any cast.

## The reused definitions

Nothing is redefined here. No new mathematical object, dimension carrier or
structure is introduced.

- `AbelianScheme S` is the Library's abelian scheme: a commutative group
  scheme over `S` whose structure morphism is smooth, proper and has
  geometrically connected fibres. `A.X` is its underlying object over `S`,
  and `A.X.left` the underlying scheme.
- `unitSection A`, `unitSection_comp A` and `RigidifiedFamily A T` come from
  `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`. A
  `RigidifiedFamily A T` is a line bundle on `A ×_S T` with a rigidification
  along the unit section.
- `RigidifiedLineBundle.IsUniversal … U` is the existing universal property
  of the full rigidified class functor. For every test object `T : Over S`,
  pulling back `U` gives a bijection from `T ⟶ P` to isomorphism classes of
  rigidified families on `A ×_S T`. It quantifies over all schemes over `S`
  and is not restricted to the `Pic⁰` subfunctor.
- `fullPicardOriginPoint k A U hU : P.left`, from
  `Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent`, is the
  image of the unique point `IsLocalRing.closedPoint k` of `Spec k` under the
  underlying morphism of the published section
  `RigidifiedLineBundle.trivialParameter`. That section classifies the
  trivial rigidified family. The origin point is the point of `P` that
  classifies the trivial line bundle. No identity-component open is assumed
  or constructed.
- `A.HasRelativeDimension g` is the Library abbreviation for Mathlib's
  `SmoothOfRelativeDimension g A.X.hom`: locally on the source, `A.X.hom` is
  standard smooth of relative dimension `g`. This is the specified
  geometric relative dimension `g` of `A`.
- `LocallyOfFiniteType P.hom` is Mathlib's
  `AlgebraicGeometry.LocallyOfFiniteType`.
- A section `x : Over.mk (𝟙 (Spec k)) ⟶ A.X` is a morphism over `Spec k` from
  `Spec k` to `A.X`, that is, a `k`-rational point of `A`.
- `GroupScheme.translation A.toGrp x` is the published translation built
  from the actual group law; on `T`-points it sends `y` to `x_T * y`.
  `LineBundle.pullback` is the actual module pullback restricted to line
  bundles. The isomorphism `… ≅ L` is an isomorphism of the underlying sheaves
  of modules.
- `Finite` is Mathlib's proposition class: the subtype of rational points
  `x` with `t_x^*L ≅ L` is finite. No `Fintype` structure or enumeration is
  chosen.
- `P.left.presheaf.stalk p` is the actual stalk of the structure sheaf of
  `P.left` at `p`, a commutative ring. `ringKrullDim R : WithBot ℕ∞` is
  Mathlib's Krull dimension of `R`, the supremum of lengths of chains of
  prime ideals. The natural number `g` is coerced into `WithBot ℕ∞`.

The finiteness premise uses the same condition as the published
`AlgClosedFieldAmpleTranslationStabilizerFiniteStatement`, with field `k` in
place of `K`. That module is not imported.

## Exactly what is and is not assumed

The hypotheses are: `k` is algebraically closed, `(P, U)` is universal,
`P.hom` is locally of finite type, `A` has relative dimension `g`, and the
rational translation stabilizer of the given ordinary line bundle `L` is
finite.

The proposition does not assume that `L` is ample, rigidified or symmetric,
and it chooses no inverse of `L`. It does not assume a dual scheme, a
Picard-zero membership condition, a group law or group-object structure on
`P`, a finite subgroup scheme such as `K(L)`, reducedness of anything, a
tangent-space or cohomology bound, or scheme-theoretic finiteness of any
morphism. It does not assume that `P` is of finite type, quasi-compact,
separated or connected. A group law on `P` is a mathematical consequence of
`hU`, as explained in the next section, but it is not a hypothesis and the
statement does not refer to it.

The premise has content. If `g ≥ 1` and `L` is trivial, every rational point
preserves `L`, and there are infinitely many of them because `k` is
algebraically closed. Source Lemma (2.19) gives the premise for ample `L`,
but this module neither proves nor asserts that an ample bundle exists or
that its stabilizer is finite. For `g = 0` the conclusion holds for any
nonzero ring, and the stalk is a local ring, hence nonzero.

## Why a local-ring conclusion

The conclusion is the Krull dimension of the actual local ring
`𝒪_{P,0}` at the published origin point `0 = fullPicardOriginPoint k A U hU`.
Mathlib's `ringKrullDim_stalk_eq_coheight` (in
`Mathlib.AlgebraicGeometry.Properties`) identifies it with the coheight of
the origin in the specialization order of `P.left`. So the bound is about
the irreducible closed subsets of `P` that pass through the origin.

**Relation to a global bound.** For an arbitrary scheme with a chosen point,
a bound on the local ring at that point implies the same bound on the
dimension of the scheme, because the Krull dimension of a stalk is at most
the dimension of the scheme. A global bound alone says nothing about a
particular point of an arbitrary scheme. Under the hypotheses of this
proposition, however, the local and global bounds are mathematically
equivalent, for the following reasons.

- The hypothesis `hU` says that `P` represents, on all test schemes, the
  functor of rigidified line-bundle classes on `A ×_S T`. That functor takes
  values in commutative groups under the tensor product. By the Yoneda
  lemma, `P` is therefore a commutative group scheme over `k`. Its identity
  section classifies the trivial class, so it is `trivialParameter` and its
  image point is the origin `0`. Source §3 (printed p.95, PDF p.99) treats
  `Pic_{X/k}` in the same way, as the group scheme representing `P_{X/k,0}`.
- `P` is locally of finite type over the algebraically closed field `k`, so
  every connected component of `P` has a rational point. Translation by that
  point is an automorphism of `P` that carries the identity component `P⁰`
  onto the component. The identity component is open, irreducible and of
  finite type. These are source Proposition (3.17)(i) and (iii), whose proof
  identifies the components with `P⁰` by translations (printed pp.38–39,
  PDF pp.42–43).
- Hence every component of `P` has the dimension of `P⁰`. The origin is a
  closed point of the irreducible finite type `k`-scheme `P⁰`, and `P⁰` is
  open in `P`, so this dimension equals `dim 𝒪_{P,0}`.

So `dim P = dim P⁰ = dim 𝒪_{P,0}`, and the global bound of the source,
`dim Pic⁰_{X/k} ≥ dim X`, is the same condition as the conclusion here. In
particular, no component of `P` away from the origin can have a different
dimension.

**What the local form provides.** The proposition states the bound directly
at the stalk that the later argument uses, so a consumer can apply it
without first formalizing the comparison above. That comparison needs the
group law on `P`, the identification of its identity with the origin, the
description of the components as translates of the identity component,
irreducibility of the identity component, and the equality of local and
global dimension for it. The Library supplies the first two.
`Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalGroupObject`
constructs `universalCommGrpObj : CommGrpObj P` from a universal family. It
takes seven named Library propositions as explicit arguments, all of which
now have published proofs: `pullbackTensorComparisonIsIso`,
`pullbackTensorUnitCoherence`, `explicitPullbackTensorAssociativity`,
`tensorMonoidalLeftUnitorComparison`, `pullbackTensorSymmetry` and
`pullbackTensorComposition` in `Langlands.Scheme.Modules`, and
`Langlands.AlgebraicGeometry.Picard.locallyFreeRankOneIffTensorInvertible`.
The lemma `one_eq_trivialParameter` of that module identifies the identity
section with `trivialParameter`, whose image point is
`fullPicardOriginPoint k A U hU`. The present module does not import that
construction. Nothing
here states or uses the homogeneity of `P` or the comparison of its local and
global dimensions.

The local form is what the later reducedness argument consumes. Over `k`,
the local ring `𝒪_{P,0}` is noetherian, so its Krull dimension is at most
the dimension of its tangent space `𝔪/𝔪²`. If that tangent space has
dimension at most `g` (source (6.6) and (6.15)), the present bound makes the
two equal. Then `𝒪_{P,0}` is regular, and in particular reduced. Both bounds
concern the same local ring, so they combine directly. A bound on the
dimension of `P` or `P⁰` could be used in the same way only after the
comparison above has been formalized.

## Provenance

This proposition is derived. It has no verbatim counterpart in the source.
The conditional form over an algebraically closed field is an internal
extraction of the dimension argument in the source, not a transcription of a
named theorem. The registered original is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`
(PDF page = printed page + 4). The library has no errata note for this
source. The following passages were reread for this statement.

- Theorem (6.18), printed p.96 (PDF p.100). For an abelian variety `X` over
  a field `k`, `Pic⁰_{X/k}` is reduced, hence an abelian variety, and
  `dim Pic⁰_{X/k} = dim X = dim_k H¹(X, O_X)`. The first step of the proof
  reads: "Let `L` be an ample line bundle on `X`. By Lemma (2.17), `ϕ_L` has
  kernel `K(L)`. Since `K(L)` is a finite group scheme it follows that
  `dim(Pic⁰_{X/k}) ≥ dim(X)`." The rest of the proof combines this with
  (6.6) and (6.15).
- Chapter VI §3, printed p.95 (PDF p.99). The source admits that
  `Pic_{X/k}` is a group scheme representing the functor `P_{X/k,0}` of line
  bundles rigidified along the zero section. Viewing the Mumford bundle
  `Λ(L)` as a family parametrised by the second factor, it defines
  `ϕ_L : X → Pic_{X/k}` as the unique morphism with
  `(id_X × ϕ_L)^*P ≅ Λ(L)`. On points, `ϕ_L(x) = [t_x^*L ⊗ L^{-1}]`.
- Definition (2.15), printed p.22 (PDF p.26). The Mumford bundle on `X × X`
  is `Λ(L) = m^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}`. Its restriction to the fibres
  `{x} × X` and `X × {x}` is `t_x^*L ⊗ L^{-1}`.
- Definition (2.16), printed p.22 (PDF p.26). `K(L) ⊆ X` is the maximal
  closed subscheme over which `Λ(L)` is the pullback of a line bundle from
  `K(L)`.
- Lemma (2.17)(i), printed p.23 (PDF p.27). A `T`-valued point `x` factors
  through `K(L)` if and only if `t_x^*L_T ⊗ L_T^{-1}` is the pullback of a
  line bundle on `T`.
- Proposition (3.17) and its proof, printed pp.38–39 (PDF pp.42–43). For a
  group scheme `G` locally of finite type over a field, the identity
  component `G⁰` is an open and closed subgroup scheme that is geometrically
  irreducible, and every connected component of `G` is irreducible and of
  finite type. The proof of (iii) identifies each component with `G⁰` by a
  translation, after extending to a field over which the component has a
  rational point. This passage is used only in the explanation of local and
  global dimension above, not in the statement.

The extraction makes three changes.

1. **The finite kernel becomes a finite rational stabilizer.** With
   `T = Spec k`, line bundles on `T` are trivial, so by Lemma (2.17)(i) the
   rational points of `K(L)` are the rational points `x` with `t_x^*L ≅ L`.
   This is the subtype in the premise. Over an algebraically closed field the
   closed points of the finite type scheme `K(L)` are rational, so
   finiteness of this subtype amounts to finiteness of `K(L)`. This is why `k`
   is assumed algebraically closed. The Lean statement uses neither `K(L)`
   nor this equivalence. The source obtains finiteness from ampleness by
   Lemma (2.19); the statement takes finiteness itself as the premise and
   does not mention ampleness.
2. **`Pic⁰_{X/k}` becomes the actual parameter.** The source's admitted
   Picard scheme is replaced by an arbitrary locally finite type `P` with an
   actual universal family `U`, and its zero by the published origin point.
3. **`dim Pic⁰_{X/k}` becomes a local dimension.** The global dimension of
   the identity component is replaced by the Krull dimension of the actual
   local ring at the origin. Under the present hypotheses the two are equal,
   as explained above. The local form names the exact ring that the later
   tangent-space argument uses.

The source proves Theorem (6.18), using the Picard scheme whose existence §3
admits. The Lean declaration here is only a stated proposition, not a
proved theorem. Its proof is a separate successor task, after this statement
is accepted and published.

## Remarks on a later proof

The following route was proposed by Worker 432. It is not a formal proof,
and nothing here claims that it has been carried out.

Rigidify `L` using triviality of line bundles over `Spec k` and choose an
ordinary inverse by published results. Build the parameter-first Mumford
family with `Langlands.AbelianScheme.mumfordBundle` and classify it into `P`
with `RigidifiedLineBundle.classifyFamily`. This gives a morphism
`φ : A.X.left → P.left`. By `Langlands.AbelianScheme.mumfordZeroParameterIso`
its restriction at the source origin is trivial, so `φ` sends the origin of
`A` to `fullPicardOriginPoint k A U hU`. By
`Langlands.AbelianScheme.fieldMumfordPointComparison`, the restriction at a
field-valued point is described by a translation difference. So the rational points of the fibre of
`φ` over the origin lie in the finite stabilizer. Over an algebraically
closed field the closed points of this finite type fibre are rational, so
the fibre is finite and `φ` is quasi-finite at the source origin. The local
dimension inequality for `φ`, together with `dim 𝒪_{A,0} = g`, then gives the
bound. Any missing substantial comparison or dimension theorem must be
split into its own unit before it is used. The route needs neither
additivity of the Mumford map nor a finite kernel group scheme.

## Boundaries and intended use

This unit states only a conditional local-dimension bound. It is an
independently stated, planned input for the geometric-reducedness proof task
`9cd303c4-a699-432a-8e44-0c6446ebc0df`, but it does not depend on that task,
on the identity-component smoothness proof
`e689d392-8896-4255-835c-4beab40a2d45` or on the chosen-dual smoothness proof
`4ef972f8-8ae6-4f1a-b440-857530de2ca6`.

The finite-stabilizer proof `d37659ae-d0c6-464f-9fb7-17a4685cf349`, the
ample-existence proof `a43c8316-5f2d-44a1-ac62-75f4fb902aa1`, ambient
representability `9d039bac-24d3-4106-869b-bd98894b444d`, field existence
`f38215ec-58a9-488f-8fd0-305952a3db2b` and the smooth-family comparison
`b879dd05-2261-4214-a0d1-57cdb62b5634` are paused. This unit does none of
their work. A later application that discharges the premise from an ample
bundle needs the corresponding theorems to be independently proved and
published first.

Worker 1001 wrote the Lean statement and this explanation, reread the cited
source passages and checked the reused declarations, and compiled the module
in the pinned environment. Worker 432 supplied the specification of the
binders and conclusion, and the proposed proof route.
