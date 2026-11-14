# Multiplicative-type groups split by a specified field extension

Author: Worker 3483.

This is a derived construction of a category on the Library's actual commutative
group schemes. It uses the already published multiplicative-type predicate,
diagonalizable groups, actual characters and character evaluation. It does not
use any pending character-functor or classification statement.

## Objects and morphisms

Let `k L : Type u` be fields with `Algebra k L`. No finite-dimensional,
separability, Galois, perfection or characteristic assumption is imposed.
`multiplicativeTypeSplitBy k L T` says that there are a finitely generated
abelian group `M : Type u` and an actual isomorphism of commutative group schemes

`T_L ≅ Diagonalizable.groupScheme L M`.

Here `T` is an actual commutative group scheme over `Spec k`, and `T_L` is its
scheme pullback along the canonical map `Spec L → Spec k`. The diagonalizable
model is the existing spectrum of the group algebra, with its represented group
law. The condition is existential and Prop-valued; no model is selected as part
of an object.

`SplitMultiplicativeType k L` is Mathlib's `ObjectProperty.FullSubcategory` on
this property. Its objects are actual groups satisfying this condition. A
morphism is any actual `k`-group-scheme homomorphism between the underlying
objects. There is no condition on a morphism concerning the witnesses of
splitting. Composition and identity come from `CommGroupScheme`; homomorphisms
have the existing additive notation for their pointwise multiplicative law.
`SplitMultiplicativeType.inclusion` is Mathlib's full and faithful inclusion,
which forgets the property.

The specified splitting extension is the difference from the existing
`IsMultiplicativeType` predicate: that predicate existentially quantifies over
the extension as well. The intrinsic law
`multiplicativeTypeSplitBy.isMultiplicativeType` simply supplies `L` as that
witness and forgets additive notation on the splitting isomorphism.
`multiplicativeTypeSplitBy.of_iso` composes the pulled-back isomorphism with a
given diagonalizable model. It proves invariance under actual isomorphisms.
This construction does not redefine multiplicative type or claim that an
arbitrary specified extension splits every multiplicative-type group.

## Actual character groups and finite generation

`DiagonalizableCharacter.evalCharacterAddHom` is the additive map sending
`m : M` to the already published character `t ↦ t(m)` of `D_L(M)`. Its additive
law follows by evaluation on every scheme over `Spec L`, using the actual
pointwise character law and multiplication of group characters.

`evalCharacterAddHom_bijective` applies the published
`DiagonalizableCharacter.NaturalUnits.existsUnique` to the family of values of
an actual character. Surjectivity follows by equality on all test schemes;
uniqueness proves injectivity. `evalCharacterEquiv` packages this as the
additive equivalence

`M ≃+ characterLattice (D_L(M))`.

These evaluation constructions work for every abelian `M`, without a finite
generation assumption. The ring `L` is a field in the bijectivity argument.
No equality of characters is inferred solely from rational points.

For an object split by `L`, a splitting isomorphism identifies its actual
`L`-characters with those of `D_L(M)`. Composing this identification with the
evaluation equivalence gives a surjective additive map from the finitely
generated `M` to the actual character group. This is the implemented proof of
`multiplicativeTypeSplitBy.character_fg`.

The corresponding instance for `T : SplitMultiplicativeType k L` supplies
finite generation of the actual `characterLattice T_L`.
`SplitMultiplicativeType.characterModule` packages precisely this group and
its canonical integer-module structure in Mathlib's existing
`FGModuleCat.{u} ℤ`; no replacement character group is introduced.

The models and character groups may have torsion, including characteristic
primary torsion. Smoothness, reducedness, connectedness and freeness are not
assumptions. Consequently the construction retains finite nonsmooth
diagonalizable factors.

## Provenance and scope

The registered source is J. S. Milne, *Algebraic Groups* (2017),
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The relevant original passages are:

- Section 12.b, printed p.230 / PDF p.246: the finite generation convention
  for the abstract commutative group defining `D(M)`.
- Lemma 12.4 and the following evaluation description, printed p.232 /
  PDF p.248: the full character group of `D(M)` is `M`, and `m` corresponds to
  evaluation at `m`. Remark 12.5 there explicitly retains torsion and
  potentially nonsmooth diagonalizable groups.
- Theorem 12.8 and Theorem 12.9(a), printed p.233 / PDF p.249:
  diagonalizable algebraic groups are the groups isomorphic to `D(M)`, and
  their character groups are finitely generated abelian groups.
- Definition 12.17, printed p.236 / PDF p.252: multiplicative type means
  becoming diagonalizable over some field extension.
- Section 12.g, Theorem 12.23 and the proof of Corollary 12.25, printed
  pp.239–240 / PDF pp.255–256: the character classification and its finite
  Galois splitting context.

The fixed-extension property and its full subcategory are internal packaging
of these definitions with a specified extension retained. The finite-generation
argument is a direct consequence of the published evaluation theorem and
splitting isomorphism. It does not invoke the classification theorem as a Lean
proof or assert that this is the entire category of multiplicative-type
groups over `k`.

The complete retained official 2017 errata snapshot dated 2 November 2026 was
read. None of its corrections affects these cited passages.

This unit constructs the category and its actual finitely generated character
modules. It does not construct a functor between this category and Galois
representations, a quasi-inverse, a categorical equivalence, absolute-Galois
continuity or exact-sequence compatibility. Those are separate obligations.
