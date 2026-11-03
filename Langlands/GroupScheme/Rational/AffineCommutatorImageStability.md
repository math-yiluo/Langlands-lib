# Stability of the actual commutator scheme image

This internal construction supplies a rational origin and stability of the
concrete affine commutator image from `AffineCommutatorImage`. Its source
motivation is the invariant
image used in CGP, *Pseudo-reductive Groups*, second edition (2015),
Lemma 3.3.4, printed pp.108–109 / PDF pp.134–135.

The base is any commutative ring `R` in arbitrary universe `u`. The ambient
group `G` and the two input groups `H` and `K` are affine over `Spec R`,
and `i : H ⟶ G` and `j : K ⟶ G` are actual group-scheme homomorphisms.
`imageOrigin i j` is the product of the two rational identity points followed
by `imageFactor i j`. The theorem `imageOrigin_comp` proves that this point
maps to the actual identity morphism of `G`.

The proof of stability uses the actual scheme image and scheme-theoretic
dominance. `imageProjection_schematic` follows from the injectivity of the
image coordinate algebra into the tensor coordinate algebra: the induced
map on global sections has zero kernel, hence the scheme morphism has zero
ideal-sheaf kernel. Transport along the tensor presentation gives
`imageFactor_schematic`. The morphism `imageFactor` is also quasi-compact,
as proved by `imageFactor_quasiCompact`, since it is an affine spectrum
morphism transported along an isomorphism.

`imageInclusion_isStable` assumes an acting group scheme `S`, flat over
`Spec R`, and actual automorphic actions `b`, `c`, and `d` on `G`, `H`,
and `K`. The hypotheses on `i` and `j` say that these homomorphisms
intertwine the actions on every test scheme. The conclusion quantifies over
every `T` over `Spec R`, every `s : T ⟶ S.X`, and every
`v : T ⟶ imageScheme i j`: there exists `w : T ⟶ imageScheme i j`
whose composite into `G` is the translate of `v` by `s`.

To prove this, the product of `imageFactor` with the flat acting scheme
remains schematically dominant. Two-input commutator equivariance gives
factorization of the ambient action through the closed image after that
precomposition. If a morphism factors through a closed immersion after
schematically dominant precomposition, its ideal-sheaf kernel contains
the defining ideal of the closed immersion. The closed-immersion lifting
property therefore descends the factorization. Evaluating this descended
morphism proves the stated all-test conclusion.

The ring generality and descent argument are internal consequences of the
existing coordinate and scheme constructions. No group law on the image,
integrality, smooth generated subgroup, weight decomposition, or
semigroup commutator weight bound is asserted here.
