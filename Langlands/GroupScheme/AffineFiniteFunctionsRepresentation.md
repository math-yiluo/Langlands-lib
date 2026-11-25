# Finite sets of functions captured by a representation

For an actual affine group scheme `Q` over an arbitrary field and a finite set `s` of its actual global functions, `finiteFunctionsRepresentation Q s` constructs one finite-dimensional actual representation of `Q` whose pullback on global functions contains `s` in its range. No finite-type, smoothness, reducedness, connectedness, or perfect-field hypothesis is required.

The returned `FiniteFunctionsRepresentation Q s` record has fields:

- `dimension : ℕ`;
- `hom : Q ⟶ GeneralLinear.groupScheme (Fin dimension) (CommRingCat.of k)`;
- `contains : ∀ x ∈ s, x ∈ Set.range hom.hom.hom.left.appTop.hom`.

This is an internal derived extension of the published corepresented linear embedding construction. Its finite-type hypothesis is needed only to choose generators of the entire coordinate algebra, while the published finite-subcomodule theorem applies to any supplied finite set. This module uses that distinction and does not claim that the resulting representation is faithful or a closed immersion.

First, `Corepresented.exists_representation_containing` takes any corepresentation of a group-valued algebra functor by an arbitrary algebra `B`, together with a finite subset of `B`. The published `Comodule.exists_matrix` produces a finite coefficient matrix whose entries linearly span this subset, with the actual coassociativity and counit identities obtained from the functor's group law. `Corepresented.LinearEmbedding.toGL` turns that matrix into a natural homomorphism to invertible matrices and then into an actual group-scheme homomorphism. Its classifying algebra map contains every matrix entry, by `GeneralLinear.classify_entry`; its range is a subalgebra and hence contains their linear span. The lemma retains both that range assertion and the exact equation identifying the scheme map with the spectrum of this classifying algebra map.

For an arbitrary affine `Q`, choose an actual relative affine presentation `Spec B ≅ Q.X`. Transfer the prescribed actual global functions to `B` using the presentation's actual `appTop` followed by `Scheme.ΓSpecIso`. Apply the corepresented construction and precompose the resulting homomorphism with `AffineCorepresentation.toModel`. Naturality of `ΓSpecIso` and the presentation's inverse laws identify its classifying algebra map with the actual global-function pullback, proving `contains`. The presentation and representation are chosen noncanonically; all maps in the record are actual group-scheme maps.

The construction retains the arbitrary universe `u` of the field, algebras and schemes. Its matrix index is `Fin dimension`, as in the existing general linear group interface. It introduces no axioms beyond the standard Lean axioms used by the imported mathematics.
