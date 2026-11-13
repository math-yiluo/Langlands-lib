# Distributions on a vector sheaf

Worker 1222. Module `Langlands.Sheaf.Renard.Distributions`, with the same namespace.

This module constructs Renard's distributions on a complex vector sheaf and
their action by the full ring of locally constant functions. The underlying
space is the full algebraic complex dual of compactly supported sections.
The module also supplies the small intrinsic laws of this construction and
its contravariant maps along sheaf morphisms.

## Source and correspondence

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, II.2.5, Definition, printed p.42 / PDF p.48. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read the original page. The Definition specifies the algebraic
dual `F_c(X)^*` and the action

`⟨f · T, s⟩ = ⟨T, f · s⟩`.

The Lean object `VectorSheafScalars.VectorSheaf X` is Mathlib's sheaf of
complex vector spaces on all open subsets of `X`. The published
[vector-sheaf scalar construction](VectorSheafScalars.md) gives it its
canonical locally constant scalar action, including the germ formula and
linearity of sheaf morphisms for those scalars. This is the source's
`𝒞^∞_X`-module structure from the Proposition on printed p.38 / PDF p.44.
The categorical equivalence between the two notions of sheaf is a separate
packaging obligation.

| Source object or formula | Lean construction |
| --- | --- |
| `F_c(X)` | `CompactSection F`, an abbreviation for the `CompactSupport.IndependentUniverses.submodule F.presheaf` |
| `𝒞^∞(X)` | `LocallyConstant X ℂ`, with its existing pointwise commutative algebra structure |
| Multiplication of compact sections by `f` | `compactSmul F f`, packaged by `compactSectionModule` |
| `F_c(X)^*` | `Distribution F := Module.Dual ℂ (CompactSection F)` |
| `⟨f · T, s⟩ = ⟨T, f · s⟩` | `distributionSmul F f`, packaged by `distributionModule`, and `smul_apply` |

The support used here is the set of nonzero global germs, as in the existing
[independent-universe compact-support construction](../CompactSupport/IndependentUniverses.md). No continuity,
boundedness or finite-dimensionality restriction is imposed on a functional.
In particular, this construction does not replace the algebraic dual by a
continuous dual.

## Construction and intrinsic laws

`topScalar` is the pullback algebra homomorphism from locally constant
functions on `X` to locally constant functions on the largest open, along the
continuous subtype inclusion. It only reconciles the domains of the source
scalar ring and Mathlib's global sections.

`support_smul_subset` follows from the published germ formula: a zero germ
remains zero after multiplication by a locally constant scalar.
`compactSmul` then has compact support because its support is a closed subset
of the compact support of the input section. The module laws follow from the
module laws on global sections and the algebra-homomorphism laws of
`topScalar`. `Γgerm_compact_smul` records the resulting germ formula.

`compactSectionScalarTower` and `compactSectionSmulCommClass` prove
compatibility with the original complex structure on compact sections.
`compact_constants_smul` identifies the action of
`algebraMap ℂ (LocallyConstant X ℂ) c`, the constant function with value `c`,
with multiplication by `c`. These facts make multiplication by `f` a
complex-linear map, `compactScalarLinear F f`.

`distributionSmul F f T` is the actual composition
`T.comp (compactScalarLinear F f)`. Its values are therefore complex-linear
functionals, and its evaluation is the source pairing formula by definition.
The dual module laws are proved by evaluating on compact sections. For the
multiplicative law, successive transposes reverse the order of multiplication;
commutativity of `LocallyConstant X ℂ` supplies the stated left action.
`distributionScalarTower`, `distributionSmulCommClass` and `constants_smul`
prove compatibility of this action with the ordinary complex dual structure.

## Functoriality

The final section is an internal consequence of the definition and the
published naturality of locally constant multiplication. It introduces no
additional claim from Renard's Proposition.

For a sheaf morphism `φ : F ⟶ G`, `compactSectionMap_smul` proves that the
compact-section map `CompactSupport.IndependentUniverses.map φ.hom` commutes with locally constant
multiplication. `transpose φ` is its ordinary complex-linear dual map:

`transpose φ T s = T (CompactSupport.IndependentUniverses.map φ.hom s)`.

`transpose_smul` proves equivariance for locally constant functions.
`transpose_id` and `transpose_comp` prove the contravariant identity and
composition laws. The definition `functor` packages these objects and maps
as an actual functor `(VectorSheaf X)ᵒᵖ ⥤ ModuleCat ℂ`.

## Generality and boundaries

The space `X` and the section carriers use any universe `u`; the coefficient
field is the actual `ℂ`. Only `TopologicalSpace X` is assumed. The canonical
locally constant action and closedness of support suffice for these
constructions on any topological space, so they apply in particular to
Renard's t.d. spaces without adding a compactness or finiteness hypothesis.

The nearby open/closed exact-sequence Proposition, the full restriction sheaf
on a locally closed subset, and isomorphisms over a change of base space are
separate obligations. The same-base transpose above does not claim those
results.

Formal dependencies are the existing `VectorSheafScalars` action,
`CompactSupport.IndependentUniverses` primitives, and
Mathlib's algebraic dual and dual-map definitions. The two filtered-colimit
instances from the independent-universe construction are activated locally
in this file; the distribution API has no additional instance parameter. The environment is Lean
4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
