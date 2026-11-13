# Strict uniformizer sections of actual standard Levi split components

`Langlands.GroupScheme.CocharacterUniformizer.StandardLeviStrictImageStatement`
is a proposition about the existing actual group schemes and uniformizer sections.
This file states it and supplies no proof.

For an arbitrary nonarchimedean local field `F`, let `G` be connected reductive,
`i : T → G` a maximal split torus, `ν` a generic cocharacter, and `J` a subset of
the simple relative roots selected by `ν`. Let `j : L → G` be any closed actual
representative of `standardLevi i ν J`, and let `a : A → L` be any split component.
The statement applies to every supplied commutative group scheme morphism
`f : A → T` satisfying `groupHom f ≫ i = a ≫ j`.

The left side is the image in `T(F)` of the existing set
`CAstrict F A (restrictedSimpleCharacters i ν J f)`. Its points are exactly the
common-uniformizer values in `A(F)` whose norms under every restricted simple
character `f ≫ α`, for `α` outside `J`, are strictly below one. The character set
is the published `restrictedSimpleCharacters`, whose real images are the published
`restrictedSimpleRoots`; no new root predicate or cone is introduced.

The right side is the image, under the same common-uniformizer section of `T`,
of the existing `IsStandardCocharacter i ν J` predicate: integral cocharacters
with zero pairing on `J` and strictly positive pairing on every simple root
outside `J`. Equality identifies the two sets of actual points. It retains the
integral lattice, rather than inferring integral factorization from an equality
of real vector spaces.

## Provenance and scope

The registered source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.2.5, printed p.107 / PDF p.113, defines the common-uniformizer lifts and their
compatibility with split subtori. V.3.21, printed p.116 / PDF p.122, describes the
strict norm inequalities. V.3.23–V.3.24, printed p.117 / PDF p.123, uses their
intersection with the uniformizer lattice and then passes to the split-central
quotient. This statement is the derived actual-object comparison for the strict
pieces before passing to that quotient.

The proposed proof route uses integral split-component factorization: a standard
cocharacter becomes central in the actual standard Levi and therefore factors
through its split component. Conversely, centrality annihilates the selected
roots. The norm formula `|α(ξ(π))| = q^(-⟨α,ξ⟩)`, with `q > 1`, translates the
strict inequalities in both directions, and functoriality of evaluation identifies
the resulting actual points. These ingredients describe a proof obligation,
not a proof in this file.

The statement includes both field characteristics, non-split ambient groups,
possibly nonreduced relative root systems and rank zero. It requires the supplied
actual representative, split component and compatible map; it does not assert
their existence. It does not assert a decomposition of all rational points,
finite generation, freeness, or any quotient comparison. The strict-face quotient
construction and the final quotient decomposition remain separate obligations.
