# Proof of the absolute Galois character anti-equivalence for field tori

`Langlands.GroupScheme.torusAbsoluteCharacterEquivalence` proves
`Langlands.GroupScheme.TorusAbsoluteCharacterEquivalenceStatement.{u}`.
For every field `k : Type u`, the theorem gives `IsEquivalence` for
`FieldTorus.characterFunctor k : (FieldTorus k)ᵒᵖ ⥤ FreeDiscreteGaloisModule.{u,u} k`.
The functor takes characters over the separable closure with their
canonical Galois action. Its maps are pullbacks along the base changes
of ground-field group-scheme homomorphisms.

Full faithfulness follows from `multiplicativeTypeAbsoluteEquivalence`
and the fully faithful inclusion of tori into groups of multiplicative
type. The opposite of this inclusion followed by the ambient character
functor is fully faithful. By `FieldTorus.characterFunctor_forget`, this
composite is also the torus character functor followed by the inclusion
of finite free modules, which is faithful. Lean uses
`Functor.FullyFaithful.ofCompFaithful` to obtain full faithfulness of
the torus character functor.

For essential surjectivity, the multiplicative-type equivalence supplies
a group whose absolute character module is equivariantly isomorphic to
the given finite free module. The underlying linear isomorphism
transports freeness to the character module. The private lemma
`isTorus_of_free_absolute_characters` applies
`MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed` to
the base-changed group, obtaining a model `D(M)` with `M` finitely
generated. Evaluation identifies `M` with the characters of `D(M)`.
Pullback along the group-scheme isomorphism gives an additive equivalence
from `M` to the actual absolute character lattice, so `M` is finite free
over `ℤ`. A finite integer basis splits `D(M)` as a product of copies
of `𝔾ₘ`. This witnesses the torus property for the original group. The
ambient equivariant isomorphism then lifts to the full subcategory of
finite free modules using `ObjectProperty.isoMk`.

This realizes the torus restriction in Milne, *Algebraic Groups*
(2017), §12.g and Theorem 12.23, printed pp. 239–240 (PDF pp. 255–256).
The splitting criterion for tori is Definition 12.14, printed p. 236
(PDF p. 252). The registered source is `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
