# Constancy of geometric Picard-zero families on connected components of a universal field Picard parameter

`Langlands.AbelianScheme.FieldPicardZeroComponentConstancyStatement.{u}` is a
proposition definition. It states a constancy property and proves nothing.

## The statement

Fix an arbitrary field `k : Type u` in an arbitrary universe `u`, and write

```text
S = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)).
```

### Hypotheses

The statement quantifies over the existing data `A : AbelianScheme S`, a
parameter `P : Over S` and an actual rigidified family
`L : RigidifiedFamily A P`, that is, a line bundle on the relative space of `A`
over `P` with a rigidification along the unit section. It assumes

- `LocallyOfFiniteType P.hom`, and
- the full universal property

  ```text
  RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L
  ```

  from `Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle`: for
  every test scheme `T` over `S`, pulling `L` back along morphisms `T ⟶ P`
  over `S` is a bijection onto the isomorphism classes of rigidified line
  bundles on the relative space over `T`. Test schemes are not restricted to
  fields.

These are exactly the hypotheses on `(k, A, P, L)` of the published
`FieldPicardZeroGeometricComponentComparisonStatement`. There the universality
proof is named `hL`, because `fullPicardOriginPoint` takes it as an argument;
here it is an anonymous hypothesis, because no origin point occurs. The field
`k` need not be perfect or algebraically closed.

`LocallyOfFiniteType P.hom` is kept so that the hypotheses agree with that
comparison statement and with the two published openness statements. No
consequence of it, such as openness of connected components, is asserted.

### Conclusion

The statement then quantifies over a point `x : P.left` and two geometric
points

```text
s₀ : Spec (CommRingCat.of K₀) ⟶ P.left,
s₁ : Spec (CommRingCat.of K₁) ⟶ P.left,
```

where `K₀ K₁ : Type u` are algebraically closed fields in the universe of `k`.
They may be different fields, and nothing relates `s₀` to `s₁` except the
hypotheses below. If

```text
Set.range s₀ ⊆ connectedComponent x  and  Set.range s₁ ⊆ connectedComponent x,
```

then

```text
IsPicardZeroFamily A
  ((RigidifiedLineBundle.relativePullback A.X.hom
    (unitSection A) (unitSection_comp A)
    (Over.homMk s₀ rfl : Over.mk (s₀ ≫ P.hom) ⟶ P)).obj L)
```

implies the same statement with `s₁` in place of `s₀`.

`connectedComponent` is Mathlib's topological connected component of `x` in
the underlying space of `P.left`. Since `Spec K₀` and `Spec K₁` each have
exactly one point, the range hypotheses say that the images of the two
geometric points lie in the connected component of `x`. As every connected
component is the connected component of each of its points, `x` only names a
component: the hypotheses say that the two images lie in one common connected
component of `P.left`.

The composites `s₀ ≫ P.hom` and `s₁ ≫ P.hom` are the structure morphisms of
the two spectra over `k`, and `Over.homMk s₀ rfl` and `Over.homMk s₁ rfl` view
`s₀` and `s₁` as morphisms over `S`. No separately chosen field homomorphism
`k → K₀` or `k → K₁` is involved.

`RigidifiedLineBundle.relativePullback` is the actual rigidified pullback of
the supplied family `L`, not a chosen representative of its class.
`IsPicardZeroFamily`, from `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`,
moves the underlying line bundle of the pulled-back family to the base change
of `A` to `Spec Kᵢ` with `familyLineBundle`, and applies
`IsGeometricallyPicardZero` there. That predicate requires, for every
algebraically closed field `K' : Type u` and every morphism `Spec K' ⟶ Spec Kᵢ`,
that the fibre bundle on the further base change to `Spec K'` be isomorphic to
its translate by every `K'`-point. So all further geometric fibres of the
pulled-back family are tested. The condition is not replaced by translation
invariance of a single representative bundle, by membership in an abstract
subgroup of classes, or by any new predicate.

Because the statement holds for all ordered pairs `(s₀, s₁)`, exchanging the
two points gives the converse implication. Hence, for each connected component
of `P.left`, either every geometric point over an algebraically closed field in
`Type u` whose image lies in that component pulls `L` back to a family
satisfying `IsPicardZeroFamily`, or no such geometric point does.

## What the statement does not assert

This is a statement only. The module contains no theorem.

- It does not say which connected components carry the Picard-zero condition.
  It does not mention `fullPicardOriginPoint`, and it does not assert either
  direction of `FieldPicardZeroGeometricComponentComparisonStatement`.
- It asserts no openness or closedness of a connected component or of a
  Picard-zero locus, provides no open subset satisfying
  `IsFullPicardIdentityComponentOpen`, and does not involve
  `IsPicardZeroOpenLocus`.
- It assumes no group law on `P`, projectivity, ambient existence, smoothness,
  openness, base-change or field-extension comparison, or dual-scheme
  existence.
- It compares only whether the condition holds at the two points. It does not
  assert that the two pulled-back families, or their homomorphisms `ϕ`, are
  related in any other way.

## Imports and dependency direction

The module imports only `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`,
which provides `RigidifiedFamily`, `unitSection`, `unitSection_comp` and
`IsPicardZeroFamily` and imports the module defining
`RigidifiedLineBundle.IsUniversal` and `RigidifiedLineBundle.relativePullback`,
and Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, which provides
`LocallyOfFiniteType`. It imports no openness statement, neither
`FieldPicardIdentityComponent` nor
`FieldPicardZeroGeometricComponentComparisonStatement`, and no ambient or
existence statement.

This statement precedes `FieldPicardZeroGeometricComponentComparisonStatement`
and both openness statements, `FieldPicardZeroGeometricOpenLocusStatement`
and `FieldPicardZeroOpenLocusStatement`. Its eventual proof and that proof's
prerequisites must not use any of these three statements, a result that starts
from a supplied Picard-zero open locus and identifies it with a connected
component, or an assumed `IsPicardZeroOpenLocus` for the supplied universal
family.

## Intended use

It is a prerequisite for the direction "image in the origin component implies
Picard-zero" of `FieldPicardZeroGeometricComponentComparisonStatement`. There,
take `x` to be `fullPicardOriginPoint k A L hL` and `s₀` to be a geometric
point over an algebraic closure of `k` that factors through the published
section `RigidifiedLineBundle.trivialParameter`. The family pulled back along
`s₀` is then isomorphic to the trivial family, which satisfies
`IsPicardZeroFamily` by `isPicardZeroFamily_trivial`. That argument is not part
of this module.

## Original source and derived interface

The registered original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Printed page numbers are four less than PDF page numbers.

- Paragraph (6.2), printed p.88 (PDF p.92), defines the functor of line
  bundles rigidified along a section, with pullback along base morphisms, and
  the universal property of a representing Poincaré bundle. The hypothesis
  `IsUniversal` is the Library form of that universal property.
- Chapter VI §3, printed p.95 (PDF p.99), notes that `Pic_{X/k}` represents
  this rigidified functor, with a rigidified Poincaré bundle, and that on
  points `ϕ_L` is `x ↦ [t_x^*L ⊗ L⁻¹]`. So `ϕ_L = 0` expresses translation
  invariance of `L`.
- Printed p.104 (PDF p.108) defines the homomorphism of `k`-group schemes
  `ϕ : Pic_{X/k} → Hom(X, X^t)`, `L ↦ ϕ_L`, and states Lemma (7.15): for a
  connected `k`-scheme `T` and a line bundle `L` on `X_T`, `ϕ_{L_s} = ϕ_{L_t}`
  for any two `k`-valued points `s, t ∈ T(k)`; in particular
  `Pic⁰_{X/k} ⊂ Ker(ϕ)`. Its proof uses the Poincaré bundle, (7.11), (7.12)
  and the fact that `ϕ`, being a homomorphism, is constant on the connected
  components of `Pic_{X/k}`.
- Proposition (7.14), printed p.103 (PDF p.107), shows that `Hom(X, Y)` is
  represented by an étale commutative `k`-group scheme for abelian varieties
  `X` and `Y` over `k`.

The present declaration is a derived strengthening of Lemma (7.15), not a
quotation of it. Lemma (7.15) compares two `k`-valued points of one connected
`k`-scheme. Here the two points are geometric points over two possibly
different algebraically closed fields, of a connected component of the
parameter of an arbitrary supplied universal pair `(P, L)` rather than of
`Pic_{X/k}` with its group structure. The compared property is the actual
pulled-back family's `IsPicardZeroFamily`, which tests all further geometric
fibres. Only the vanishing of `ϕ` is compared, not equality of `ϕ` at the two
points: for points over different fields, those values do not lie in a common
set of points of `Hom(X, X^t)`.

Classically the statement is expected for the following reason. This is not
formalized and is recorded only to explain the derivation. By (6.2) and
Chapter VI §3, a universal pair identifies `P` with `Pic_{X/k}` and `L` with
the Poincaré bundle, and `ϕ` becomes a morphism `P → Hom(X, X^t)`. By (7.14)
the target is étale over `k`, so its underlying space is discrete and the
`k`-rational zero point is open and closed. Its preimage in `P` is therefore
open and closed, and contains or misses each connected component. For an
algebraically closed field `K` and a geometric point `s` over `K`, the
pulled-back bundle has `ϕ = 0` exactly when every further geometric fibre is
translation invariant, which is what `IsPicardZeroFamily` tests. This is the
argument of (7.15) with the open and closed zero locus of `ϕ` in place of
equality at two `k`-points. A proof in the Library must supply the
identification with the rigidified Picard functor, the passage between
different algebraically closed fields, and any group law, Hom-scheme, rigidity
or seesaw argument it uses as proved prerequisites. None of them is a
hypothesis of the statement.
