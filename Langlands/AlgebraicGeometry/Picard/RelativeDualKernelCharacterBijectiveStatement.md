# Relative Cartier kernel duality on every test scheme

Author: Worker 195.

`Langlands.AbelianScheme.RelativeDualKernelCharacterBijectiveStatement`
is a `Prop`-valued definition. For every base scheme `S`, every actual
isogeny `f : A → B` of abelian schemes over `S`, and every test `S`-scheme
`T`, it asserts bijectivity of the existing normalized map

```text
dualKernelPointCharacter ... T :
  (T → kernel(dual(f))) → Cartier.characters(kernel(f))(T).
```

Both kernels are scheme-theoretic kernels already in the Library. The dual
map is the actual `dualCommGroupSchemeMapFromEvaluation`, built from the
retained `HasDualScheme` witnesses, inverse Poincare bundles and displayed
tensor evaluation isomorphisms. The seven named tensor/Picard propositions
are precisely its constructor inputs. The character functor consists of
actual homomorphisms from the base-changed primal kernel to the
multiplicative group over `T`. No pairing, character map or output
isomorphism is supplied independently.

The isogeny premise is `IsIsogeny f`: the actual underlying morphism is
finite, flat and surjective. All base and test schemes remain arbitrary;
there is no noetherian, reducedness, field, separability, characteristic or
invertible-degree premise. In particular, the test quantifier includes
nonreduced schemes. The normalized map retains the existing convention of
the transported translation action divided by the trivial action.

The source context is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft built 2012-02-08, Proposition (7.4), printed
pp.99–100 / PDF pp.103–104, and Theorem (7.5), printed p.100 / PDF p.104.
Registered source: `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA256 `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
These pages were read directly. Proposition (7.4) treats character descent
over an arbitrary base with the requisite universal global-functions
condition, and states arbitrary-test base-change compatibility. Theorem
(7.5) applies the construction to isogenies of abelian varieties over a
field. The relative target here is a derived extension using the
Library's geometric-fibre definition of Picard zero; it is not claimed to
be the literal scope of Theorem (7.5).

There is a concrete route using published results: the existing
`trivialHomPullbackClassCharacter_bijective` works over every base.
The remaining Picard-zero membership can be tested at every algebraically
closed fibre of each parameter scheme. The actual pullback trivialization
and isogeny premise survive those base changes, so the existing
algebraically closed translation-invariance criterion applies. The
comparison `dualKernelPointCharacter_bijective_of_classification` then
combines membership with character classification for this exact beta.
This paragraph identifies a proof route; this statement file supplies no
proof. A separate proof task must establish the exact published
proposition, without adding hypotheses.

The conclusion is bijectivity of this specific normalized character on
all tests. Naturality and additivity have separate published proofs;
together they can package the conclusion as an isomorphism of group-valued
functors. This file does not assert existence or geometry of a dual,
that the dual of `f` is an isogeny, a chosen Cartier-dual representing
scheme, a rank formula, or perfectness of a nonprincipal polarization
pairing. No new axiom is introduced. No source-specific errata note was
found in project or Library `notes/errata` paths.
