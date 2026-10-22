# Rational invertibility with a uniform kernel annihilator

`Langlands.CommGroupScheme.IsogenyInverseStatement` is a proposition,
parameterized by the universe, with the following content. For every scheme
`S`, commutative group schemes `G` and `H` over `S`, and group-scheme
homomorphism `f : G ⟶ H`, assume:

1. The underlying scheme morphism of `f` is finite, flat, and surjective,
   expressed by the published `GroupScheme.IsIsogeny (groupHom f)`.
2. There exists one integer `n ≠ 0` such that multiplication by `n` on the
   actual scheme kernel of `f` is the zero group homomorphism.

Then the image of `f` under `Rationalization.inclusion` is an isomorphism.
Here rationalized Hom groups are the published tensor products
`ℚ ⊗[ℤ] (G ⟶ H)`, with their constructed composition. Thus the conclusion
asserts the existence of a two-sided inverse in that category.

The kernel is the published pullback of the group homomorphism along the
target unit. Its commutativity is inherited from `G`. In the kernel's
group of homomorphisms, `1` denotes the zero homomorphism in multiplicative
notation; the categorical identity is `𝟙`. Consequently the displayed
Lean equation `GroupScheme.multiplication (GroupScheme.kernel (groupHom f)) n = 1`
is precisely scheme-theoretic kernel annihilation, not an assertion merely
about geometric points.

The base is arbitrary. No field, noetherian, connected, or quasicompact
hypothesis is imposed on it, and no smoothness or properness is needed in
this conditional target. The single annihilating integer is global over
`S`. Componentwise integers without a common nonzero multiple do not
supply this hypothesis. No unrestricted rational invertibility assertion
over an arbitrary base is made.

## Provenance and intended argument

This is a derived statement, not a direct transcription of a field theorem.
Edixhoven, van der Geer, and Moonen, *Abelian Varieties*, preliminary draft,
Chapter V, Proposition (5.12), printed page 75 / PDF page 79, proves for
an isogeny of abelian varieties over a field that the degree annihilates
the kernel and that multiplication by that degree factors through an
isogeny in the other direction, with both composites equal to the
multiplication map. Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The present statement assumes a uniform kernel annihilator rather than
extending the source's degree argument to arbitrary bases.

For the general-base descent step, the Stacks Project, *Descent*,
version `ed88ff78` (compiled July 14, 2026), Lemma 13.7, Tag `023Q`,
printed/PDF page 41, states that fpqc coverings are universal effective
epimorphisms, equivalently that representable functors are fpqc sheaves.
Registered source: `stacks-descent-ed88ff78-2026`, SHA256
`28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`.

The mathematical argument motivating the target is as follows. A finite,
flat, surjective morphism is an fpqc cover. Annihilation of its group-scheme
kernel makes multiplication by `n` on `G` agree on the two projections
of its kernel pair. Descent of morphisms therefore produces a map
`g : H → G` over `S`. The same sheaf property, after base change and on
products, gives compatibility with the group laws and the identities
`g ∘ f = [n]_G` and `f ∘ g = [n]_H`. The tensor `(1/n) ⊗ g` is then a
two-sided inverse to `1 ⊗ f`. These are proof obligations for the
separate proof task; this file only defines their rational-invertibility
conclusion as a proposition.

The companion Lean file provides no proof of this proposition and assumes
no chosen quasi-inverse or descent map as input data.
