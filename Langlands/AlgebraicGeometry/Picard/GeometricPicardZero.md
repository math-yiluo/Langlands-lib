# Translation invariance on geometric fibres

This module constructs section translations and a geometric-fibre Picard-zero
condition for actual line bundles on an abelian scheme. Schemes and fields use
Mathlib's universe `u`; a line bundle is the existing locally free rank-one
object in the scheme-module category.

## Section translations

For a group scheme `G` over `S`, a section is a slice morphism
`x : Over.mk (𝟙 S) ⟶ G.X`. The scheme over `S` represented by `Over.mk (𝟙 S)`
is terminal. `GroupScheme.translation G x` is the product of the constant map
`G.X → S → G.X` and the identity map in the actual group structure on
`G.X ⟶ G.X`. Thus it is the scheme morphism `y ↦ x · y`, using the given
group-scheme multiplication; it is not asserted to be a group homomorphism.
This definition does not require commutativity.

`points_translation` proves that precomposing with any test-scheme point
`y : T ⟶ G.X` gives `(T → S → G.X) * y`. Its proof uses compatibility of
precomposition with multiplication and uniqueness of the morphism to the
terminal slice object. `translation_one` follows by simplifying multiplication
by the identity section. Multiplicative notation here is inherited from
Mathlib's group objects; on an abelian scheme this is translation by addition.

`GroupScheme.IsTranslationInvariant G L` means that for every section `x`
there exists an isomorphism `translation(x)^* L ≅ L` of actual line bundles.
It tests sections over the current base; it does not quantify over further
base changes. The isomorphisms are expressed using `Nonempty`, so no chosen
family of isomorphisms or coherence between them is part of the predicate.

The lemma `isTranslationInvariant_of_iso` transports the predicate along
`e : L ≅ M`: it composes the pullback of `e.symm`, the given invariant
isomorphism for `L`, and `e`. Applying this construction in both directions
proves `isTranslationInvariant_iff_of_iso`. The structure line bundle satisfies
the predicate by the canonical `LineBundle.pullbackTrivialIso`.

## Geometric-fibre condition

For `A : AbelianScheme S`, a line bundle `L` on `A.X.left`, and a scheme map
`s : T ⟶ S`, `AbelianScheme.fibreLineBundle A L s` is the actual pullback of
`L` along the first projection `A ×_S T → A`. Its type is definitionally a
line bundle on `(AbelianScheme.baseChange s).obj A`. This uses the existing
abelian-scheme base change, whose total space has order `A ×_S T` and whose
structure map to `T` is the second projection.

`AbelianScheme.IsGeometricallyPicardZero A L` is a proposition: for every
field `K : Type u` with `IsAlgClosed K` and every map `s : Spec K ⟶ S`,
the line bundle `fibreLineBundle A L s` is translation invariant on the
actual base-changed abelian scheme `A_K`. Its sections over `Spec K` are
exactly the points tested in this condition. There is no projectivity or
noetherian hypothesis on the base in this definition.

`isGeometricallyPicardZero_of_iso` pulls the given line-bundle isomorphism
back to each geometric fibre and uses the preceding transport lemma.
`isGeometricallyPicardZero_iff_of_iso` applies it in both directions.
`isGeometricallyPicardZero_trivial` identifies the restriction of the structure
line bundle with the structure line bundle of each fibre, then transports its
translation invariance along the inverse of that identification.

## Provenance and scope

The registered source is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft, literature ID
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
On printed p.95 (PDF p.99), the point formula for the morphism associated to
a line bundle is `φ_L(x) = [t_x^* L ⊗ L⁻¹]`. Corollary (7.22), printed
p.106 (PDF p.110), identifies the kernel of `L ↦ φ_L` with `Pic⁰` over a
field. These passages motivate the translation-invariance criterion chosen
explicitly by item 3 of the parent task.

The module is a derived construction of that chosen fibre condition. It does
not formalize the source's comparison with an identity component or its
kernel theorem. It also does not yet construct a relative subfunctor, prove
preservation by arbitrary base change, supply tensor operations, or prove
representability. Those remain separate obligations. The elementary transport
and trivial-bundle proofs above use only the actual pullback functors and
isomorphisms already in the Library.
