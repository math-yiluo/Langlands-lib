# Renard A.III.2: representability and left universal problems

This pair states the final remark and corollary of Appendix A.III.2 in
David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026. The remark starts on printed p.254 /
one-based PDF260; its proof and the corollary occupy printed p.255 /
PDF261, immediately before A.III.3. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The namespace is `Langlands.Renard.RepresentabilityUniversal`. Every
declaration is a closed `Prop`-valued definition. This pair supplies
statements; proofs remain separate obligations.

## Actual data and universe conventions

The pair uses Mathlib's actual categories, functors, natural
transformations, natural isomorphisms, `Functor.RepresentableBy` data and
`CostructuredArrow.IsUniversal` data. It introduces no replacement
interfaces. A costructured arrow for `S : A ⥤ B` and `Y : B` consists
of an object `X : A` and an arrow `j : S.obj X ⟶ Y`.
`CostructuredArrow.IsUniversal` means that this object is terminal in
the costructured-arrow category. Thus its existence is exactly the left
universal property

```text
for every Z : A and f : S.obj Z ⟶ Y,
there exists a unique g : Z ⟶ X with S.map g ≫ j = f.
```

Mathlib's terminality is data, so the statements use `Nonempty` to
express existence of those data as a proposition.

The value universe `w`, category morphism universes `vA`, `vB` and
category object universes `uA`, `uB` are independent. For a presheaf
`F : Cᵒᵖ ⥤ Type w` on `C : Type uA` with `[Category.{vA} C]`,
the lifted Yoneda presheaf `uliftYoneda.{w}.obj X` has values
`ULift.{w} (Z ⟶ X)`, and `F ⋙ uliftFunctor.{vA}` has values
`ULift.{vA} (F.obj (op Z))`. Both take values in
`Type (max w vA)`. These lifts only compare universe levels; their
`up` and `down` maps are inverse bijections. No relation between `w`
and `vA`, including an inequality, is assumed.

The Hom presheaf in the second clause already takes values in
`Type vB`. Mathlib's `RepresentableBy` supports a source with Hom
universe `vA` independently of that value universe, so this clause
requires no universe lifts. Every category, category structure, functor,
object and representation is bound inside its component. No
smallness, finiteness or nonemptiness hypothesis on a category is added.

## The three components

`YonedaUniversalStatement.{w,vA,uA}` binds the presheaf, an object `X`
and an arbitrary natural transformation

```text
ω : uliftYoneda.{w}.obj X ⟶ F ⋙ uliftFunctor.{vA}.
```

It asserts that `IsIso ω` is equivalent to existence of universal-arrow
data for the actual Yoneda costructured arrow with structure map `ω`.
In expanded form the right side says that every
`θ : uliftYoneda.{w}.obj Z ⟶ F ⋙ uliftFunctor.{vA}` factors uniquely as
`uliftYoneda.{w}.map f ≫ ω`, for `f : Z ⟶ X`. The left side says that
the chosen transformation itself is a natural isomorphism, exactly the
source's definition of representation by `(X, ω)`. It is a conclusion
of the equivalence, rather than an extra input assumption.

`HomPresheafUniversalStatement.{vA,vB,uA,uB}` binds arbitrary categories
`A` and `B`, a functor `F : A ⥤ B`, an object `Y : B`, an object
`X : A`, and actual representation data

```text
r : (F.op ⋙ yoneda.obj Y).RepresentableBy X.
```

The presheaf at `Z` is `F.obj Z ⟶ Y`, and its map along `g : Z ⟶ Z'`
is precomposition by `F.map g`. The data `r` contain natural
equivalences `(Z ⟶ X) ≃ (F.obj Z ⟶ Y)` and their inverse laws.
The conclusion is universal-arrow data for `F` with the explicit arrow

```text
j = r.homEquiv (𝟙 X) : F.obj X ⟶ Y.
```

Thus for every `f : F.obj Z ⟶ Y` there is a unique `g : Z ⟶ X`
with `F.map g ≫ j = f`. This is the sufficient condition asserted in
the second part of the source remark. An equivalence in the reverse
direction is not part of this component.

`CompatibleUniquenessStatement.{w,vA,uA}` binds two natural
isomorphisms `ω` and `ω'` representing the same lifted presheaf by
objects `X` and `X'`. It asserts

```text
∃! e : X ≅ X', uliftYoneda.{w}.map e.hom ≫ ω'.hom = ω.hom.
```

The unique witness is an actual object isomorphism, with its inverse
and both inverse identities. Uniqueness concerns isomorphisms that
respect the chosen representations. The source corollary suppresses
this compatibility, which is implicit in representing data and the
preceding universal property. Taken as uniqueness of all bare
isomorphisms, that wording would be false: a two-element set has both
the identity and the transposition as automorphisms. The explicit
compatibility is the interpretation used here; no assertion of
uniqueness of arbitrary bare isomorphisms is made.

`RepresentabilityUniversalStatements.{w,vA,vB,uA,uB}` is exactly the
conjunction of these three closed components in the displayed order.
The `Equiv`, `Iso`, natural-transformation and terminality types retain
their actual inverse, naturality and factorization laws.

## Provenance and proof boundary

The first component translates the first assertion of the final
remark, including both directions proved on PDF261. The second
translates the remark's Hom-presheaf assertion and its formula
`j = ω_X(id_X)`; Renard leaves this proof to the reader. The third
translates the following representing-object uniqueness corollary
with the compatibility required by the preceding universal-property
discussion. The explicit universe lifts, Mathlib representation data,
`Nonempty` wrappers and closed aggregate are internal formal
packaging of those source assertions.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
corrects nearby formulas on its PDF18–19, including identity evaluation
for `j` and factorization through the representing transformation.
The governing 2026 PDF260–261 already uses the corrected forms.
That older-edition check does not replace the governing original or
claim an exhaustive errata audit.

No proof of a component is supplied here. A future exact proof can
use Yoneda evaluation, the natural Hom equivalences of
`RepresentableBy`, and uniqueness of terminal costructured arrows.
The actual Lean proof and its route must be documented in the
separate proof pair. The core Yoneda theorem, A.III.1 universal-arrow
comparisons, A.III.3, and the rest of Appendix A retain their separate
owners and proof obligations.
