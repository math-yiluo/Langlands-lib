# A Mumford classifier detecting geometric Picard-zero pullbacks on a universal rigidified parameter

`Langlands.AbelianScheme.UniversalMumfordClassifierStatement.{u}` is a
proposition definition. The module states this proposition and does not prove
it; it contains no theorem. A separate exact proof task is to follow once the
statement is accepted.

## The statement

### Data and hypotheses

The statement quantifies over

- an arbitrary scheme `S : Scheme.{u}` in an arbitrary universe `u`;
- an abelian scheme `A : AbelianScheme S`;
- a parameter `P : Over S`, that is, a scheme `P.left` with a morphism
  `P.hom : P.left ⟶ S`;
- an actual rigidified family `L : RigidifiedFamily A P`, from
  `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`: a line bundle on the
  relative space of `A` over `P` together with a rigidification along the
  section induced by the unit section `unitSection A : S ⟶ A.X.left`;
- a proof

  ```text
  hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L
  ```

  of the full universal property from
  `Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle`: for every
  test scheme `T : Over S`, the map sending a morphism `T ⟶ P` over `S` to the
  isomorphism class of the actual rigidified pullback of `L` is a bijection
  onto the isomorphism classes of rigidified line bundles on the relative space
  of `A` over `T`. Test schemes are arbitrary; they are not restricted to
  fields, to reduced schemes or to schemes of finite type. The proof is named
  because the conclusion uses `trivialParameter`, which takes it as an
  argument.

No further hypothesis is made: there is no assumption on `S`, no group law,
separatedness, finiteness, smoothness or projectivity assumption on `P`, and no
existence or dual-scheme hypothesis.

### Notation

Write

```text
A_P = (baseChange P.hom).obj A,
e   = (RigidifiedLineBundle.trivialParameter A.X.hom (unitSection A)
        (unitSection_comp A) L hL).left : S ⟶ P.left.
```

`A_P` is the actual base change of `A` along `P.hom`. Its total space
`A_P.X.left` is the scheme pullback `A ×_S P`, and its structure morphism
`A_P.X.hom : A ×_S P ⟶ P.left` is the second projection.
`unitSection A_P : P.left ⟶ A ×_S P` is its unit section.

`trivialParameter`, from
`Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality`, is the morphism
`Over.mk (𝟙 S) ⟶ P` that `hL` assigns to the canonical trivial rigidified
family over `S` itself. Its underlying morphism `e` is therefore a section of
`P.hom`: the point of `P` classifying the trivial family.

### Conclusion

The statement asserts that there exists a scheme morphism

```text
Ψ : A_P.X.left ⟶ P.left        (that is, Ψ : A ×_S P ⟶ P)
```

with the following three properties.

1. `Ψ ≫ P.hom = A_P.X.hom ≫ P.hom`. Regard `A ×_S P` as a scheme over `S`
   through its projection to `P` followed by `P.hom`. Then `Ψ` is a morphism
   over `S`. It is not required to be a morphism over `P`: a point `(x, q)` may
   be sent to a point of `P` other than `q`, as long as both lie over the same
   point of `S`.

2. `unitSection A_P ≫ Ψ = P.hom ≫ e`. On the unit section `{0} × P` of `A_P`,
   `Ψ` is the composite of `P.hom` and the trivial parameter: a point `(0, q)`
   goes to the trivial parameter over the image of `q` in `S`.

3. For every test scheme `T : Over S` and every morphism `p : T ⟶ P` over `S`,

   ```text
   IsPicardZeroFamily A
     ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
       (unitSection_comp A) p).obj L)
   ```

   holds if and only if, for every algebraically closed field `K : Type u`,
   every morphism `t : Spec (CommRingCat.of K) ⟶ T.left` and every morphism
   `y : Spec (CommRingCat.of K) ⟶ A_P.X.left` with

   ```text
   y ≫ A_P.X.hom = t ≫ p.left,
   ```

   one has

   ```text
   y ≫ Ψ = t ≫ T.hom ≫ e.
   ```

In condition 3, `t` is a geometric point of `T.left` over an arbitrary
algebraically closed field in the same universe `u`, and `y` is a geometric
point of `A ×_S P` over the same field whose image in `P` is the geometric point
`t ≫ p.left`. By the universal property of the fibre product, such a `y` is the
same as a `K`-point of `A` lying over the image of `t` in `S`, that is, a
`K`-point of the geometric fibre of `A` at that point. The right-hand side
`t ≫ T.hom ≫ e` is the trivial parameter at the image of `t` in `S`. Since
`p.left ≫ P.hom = T.hom`, both sides of the equation lie over that point of
`S`, as condition 1 requires. The quantifiers range over all algebraically
closed fields `K : Type u`, all geometric points `t` of `T.left` and all such
geometric points `y`. The criterion is not restricted to a single field, to
`T` being the spectrum of a field, or to points of `T` alone.

On the left-hand side, `RigidifiedLineBundle.relativePullback … p` is the
actual rigidified pullback functor along `p`, applied to the supplied family
`L`, and not a chosen representative of its class. `IsPicardZeroFamily` is the
unchanged predicate of `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`.
It moves the underlying line bundle of the pulled-back family to the base
change `(baseChange T.hom).obj A` with `familyLineBundle` and applies
`IsGeometricallyPicardZero`. That predicate requires, for every algebraically
closed field `K' : Type u` and every `s : Spec (CommRingCat.of K') ⟶ T.left`,
that the restriction of the bundle to the base change of `A_T` to `Spec K'` be
isomorphic to its translate by every section of that base change over
`Spec K'`. So all geometric fibres of the pulled-back family are tested. No
replacement Picard-zero predicate is introduced.

## Interpretation and derived provenance

The statement is derived, not a quotation. The intended `Ψ` is the classifying
morphism of the rigidified Mumford family of the base change `A_P`; the
statement records only the three properties above.

Let `L_P` be the universal family moved to a line bundle on `A_P`, rigidified
along the unit section of `A_P`. Its Mumford bundle

```text
Λ(L_P) = m^*L_P ⊗ p₁^*L_P⁻¹ ⊗ p₂^*L_P⁻¹   on  A_P ×_P A_P,
```

with its rigidification along the unit section of one factor, is a rigidified
family of line bundles on `A` parametrized by the other factor, the
`S`-scheme `A ×_S P`. The universal property `hL` assigns to it a morphism
`A ×_S P ⟶ P` over `S`; this is the intended `Ψ`, and condition 1 expresses
that it is a morphism over `S`. On a geometric point `y = (x, q)`, with `x` a
`K`-point of `A` and `q` a `K`-point of `P` over the same point of `S`, the
family restricts to the Mumford bundle of `L_q`, the pullback of `L` along `q`,
restricted to the fibre over `x`. Hence

```text
Ψ(x, q) = ϕ_{L_q}(x) = [t_x^*L_q ⊗ L_q⁻¹].
```

Condition 2 corresponds to `ϕ_{L_q}(0) = 0`: the Mumford bundle is trivial over
the unit section. Condition 3 says that the pulled-back family `p^*L` is
geometrically Picard zero exactly when `ϕ` vanishes on every further geometric
point. For a geometric point `t` of `T` with `q = t ≫ p.left`, the fibre of
`p^*L` at `t` is `L_q`. Translation invariance of `L_q` by a `K`-point `x`,
`t_x^*L_q ≅ L_q`, is the vanishing `ϕ_{L_q}(x) = 0`, that is, `Ψ(x, q) = e`.

This identification of `Ψ` with the Mumford classifier explains the
derivation. It is not part of the proposition, which neither mentions the
Mumford bundle nor asserts that every `Ψ` satisfying 1–3 arises in this way.

### Original source

The registered original is Edixhoven, van der Geer and Moonen (EVM below),
*Abelian Varieties*, preliminary draft, source ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. Printed
page numbers are four less than PDF page numbers. No errata note for this
source exists in the Library.

- Definition (2.15), printed p.22 (PDF p.26), defines the Mumford line bundle
  `Λ(L) := m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹` on `X × X` for a line bundle `L` on an
  abelian variety `X`. It notes that the restriction of `Λ(L)` to `{x} × X` and
  to `X × {x}` is `t_x^*L ⊗ L⁻¹`, and that `Λ(L)` is trivial on `{0} × X` and
  on `X × {0}`.
- Paragraph (6.2), printed p.88 (PDF p.92), defines the functor `P_{X/S,ε}` of
  line bundles rigidified along a section, with pullback along base morphisms,
  and the universal property of a representing Poincaré bundle. The hypothesis
  `IsUniversal` is the Library form of that universal property.
- Chapter VI §3, printed p.95 (PDF p.99), notes that `Pic_{X/k}` represents
  the rigidified functor, with a rigidified Poincaré bundle `P`. It views
  `Λ(L)` as a family of line bundles on `X^{(1)} = X × {0}` parametrized by
  `X^{(2)} = {0} × X`, and obtains `ϕ_L : X → Pic_{X/k}`, the unique morphism
  with `(id_X × ϕ_L)^*P ≅ Λ(L)`. On points, `ϕ_L` is `x ↦ [t_x^*L ⊗ L⁻¹]`.
- Chapter VII §3, printed p.101 (PDF p.105), extends this to a `k`-scheme `T`
  and a line bundle `L` on `X_T`. The relative Mumford bundle `Λ(L)` on
  `X_T ×_T X_T`, viewed as a family parametrized by the second factor, gives
  `ϕ_L : X_T → Pic_{X_T/T} = Pic_{X/k} ×_k T`.
- Lemma (7.11) and the discussion after it, printed p.102 (PDF p.106), state
  that `ϕ_L` depends only on the class of `L` and is compatible with base
  change on `T`, so that the fibre of `ϕ_L` over a point `t ∈ T` is `ϕ_{L_t}`.
  They define `K(L) := Ker(ϕ_L)` and note that `ϕ_L = 0` exactly when `Λ(L)` is
  trivial over `X_T`.

The present proposition differs from these passages in the following ways.
EVM work over a field `k`, with `Pic_{X/k}` and its group structure. Here the
base `S` is an arbitrary scheme, and `(P, L)` is an arbitrary supplied
universal pair with no group law, existence or separatedness assumed.
Applied to the universal family itself (`T = Pic_{X/k}`, `L = P`), EVM's
relative `ϕ` followed by the projection to `Pic_{X/k}` is a morphism
`X × Pic_{X/k} ⟶ Pic_{X/k}`; `Ψ` is the analogue of this morphism for
`A ×_S P`. Instead of the scheme-theoretic vanishing `ϕ_L = 0`, condition 3
compares the vanishing of `Ψ` at geometric points with the Library predicate
`IsPicardZeroFamily`, which tests translation invariance on all geometric
fibres. This comparison is internal to the project. It combines the description
of `ϕ_L` on points (Chapter VI §3) with the base-change compatibility (7.11).
The Library interfaces relevant to a proof are listed in the context of the
statement task. They include `mumfordBundle`, `mumfordZeroParameterIso`,
`classifyFamily`, `classifyFamily_pullback`, `classifyFamily_trivial`, the
family base-change equivalence, `FieldMumfordPoint.carrierIso` and
`picardZeroGeometricDetection`. None of them is used or asserted here.

## What the statement does not assert

- It makes no openness, closedness or constructibility claim about the locus
  in `A ×_S P` or in `P` where `Ψ` takes the trivial parameter, or about any
  Picard-zero locus in `P`.
- It makes no claim about connected components of `P` or of `A ×_S P`.
- It asserts no group law on `P`, and it does not assert that `Ψ` is a
  homomorphism.
- It asserts no separatedness of `P`.
- It does not assert that `Ψ` is unique, or that `Ψ` is the classifying
  morphism of the Mumford family. Only the existence of some `Ψ` with
  properties 1–3 is claimed.
- Condition 3 tests only geometric points. It asserts no scheme-theoretic
  equality of `Ψ` with the trivial parameter on a fibre or on a subscheme.
- It does not assert that a universal pair `(P, L)` exists for any `A`.

## Imports and dependency direction

The module imports

- `Langlands.AlgebraicGeometry.Picard.RelativePicardZero`, which provides
  `RigidifiedFamily`, `unitSection`, `unitSection_comp` and
  `IsPicardZeroFamily`, and whose imports provide `AbelianScheme.baseChange`,
  `RigidifiedLineBundle.IsUniversal` and
  `RigidifiedLineBundle.relativePullback`;
- `Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality`, which
  provides `RigidifiedLineBundle.trivialParameter`;
- Mathlib's `Mathlib.FieldTheory.IsAlgClosed.Basic`, which provides
  `IsAlgClosed`.

All imported published pairs are unchanged. Neither import depends on
`FieldPicardZeroComponentConstancyStatement`,
`FieldPicardZeroGeometricComponentComparisonStatement`,
`FieldPicardZeroGeometricOpenLocusStatement`,
`FieldPicardZeroOpenLocusStatement` or the module `OpenLocus` defining
`IsPicardZeroOpenLocus`.

This statement precedes `FieldPicardZeroComponentConstancyStatement`, and
therefore also the comparison statement and the two openness statements named
above. Its eventual proof and that proof's prerequisites must not use any of
these four statements, a result that starts from a supplied open Picard-zero
locus and identifies it with a connected component, or an assumed
`IsPicardZeroOpenLocus`.

## Intended use

The statement is a prerequisite of the proof of
`FieldPicardZeroComponentConstancyStatement` in exact proof task
`58fe8476-5045-4662-9a48-c3b2a2616489`. In that planned proof, the set of points
of `P` over which `Ψ` maps the whole fibre of `A_P` to the trivial parameter is
to be shown open and closed in separate focused statement and proof tasks.
Condition 3 is then to identify the geometric points of `P` that pull `L` back
to a Picard-zero family with the geometric points whose image lies in that
set. Those steps are not part of this module.
