# An irreducible inducing subquotient retaining the embedding

`Langlands.Parabolic.IrreducibleInducingSubquotientStatement` is a proposition
definition. It concerns every prime, every supplied p-adic field and
topological datum, every rank and standard upper block parabolic, with
independent field and carrier universes and carriers in `Type (max uF uV)`.

Let `π` be an actual irreducible smooth complex representation of `GL_n(F)`.
Assume that its normalized upper Jacquet module for a block shape `B` has finite
group-algebra length, and that there is a nonzero intertwiner from `π` to
normalized induction of an actual smooth Levi representation `σ`. The assertion
produces an actual irreducible smooth Levi representation `ρ` satisfying all of:

- `ρ` is a quotient of the whole normalized Jacquet module of `π`;
- `ρ` is an actual subquotient of `σ`;
- an injective intertwiner embeds `π` into normalized induction of `ρ`.

The inducing representation `σ` need not be irreducible, admissible or of
finite length. The assertion makes no classification or segment conclusion.
All induction uses the Library's standard upper parabolic, positive
half-modulus covariance and right translation; the Jacquet module uses the
matching inverse half modulus. A quotient is an actual surjective equivariant
linear map, a subquotient is the Library's actual invariant-submodule quotient
up to isomorphism, and the embedding is an actual injective equivariant map.

This is an internal generalization of the image argument in Chris Jantzen,
*On supports of induced representations for symplectic and odd-orthogonal
groups*, American Journal of Mathematics 119 (1997), Lemma 5.5, printed
pages 1226–1227, registered source `jantzen-1997-supports-classical`. That lemma
starts with an embedding into induction from a finer Levi and applies
induction in stages. The present assertion starts directly with a nonzero map
into induction from `B`, makes the finiteness needed for a simple quotient of
the adjunction image explicit, and retains the resulting whole-Jacquet quotient.
After induction in stages, the inner induction can be supplied as `σ`. The
statement does not assert an induction-in-stages comparison.

The intended proof takes the nonzero first-adjointness image of the given map,
chooses a simple quotient of that image, and applies first adjointness again.
This file defines the proposition and supplies no proof of it.
