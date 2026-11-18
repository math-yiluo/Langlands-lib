# Actual integral fixed-frame automorphisms on framed representatives

`frameAutomorphismIso X a` extends an actual integral full-order automorphism
of the fixed frame along the stored residue map and restricts it to exactly
the actual source cover. Its forward and inverse maps are the existing
integral formal maps. Restriction preserves actual identity, composition and
inversion; coefficient extension gives the corresponding source equations.

`frameAct a X` precomposes the whole actual framing quasi-isogeny with the
inverse of that source automorphism. It retains exactly the target and residue
map. Its existing local kernel-rank height-zero certificate is transported by
the actual integral source isomorphism and actual target identity; cancelling
the target identity gives the stored framing formula. No numerical height is
assigned and no new height-compatibility premise is introduced.

The identity law and left multiplication law hold on actual framed
representatives. The latter uses ordinary functional multiplication in the
frame-automorphism group and the actual inverse-composition equation for its
rationalized source maps. `frameAutomorphismMulAction` packages these equations
as a group action; `frameAutomorphism_smul_eq` retains its exact construction.

The integral restriction lemmas have separate scalar, coefficient and acting
ring universes with arbitrary finite coordinate types. The framed construction
retains the local-field, central finite-dimensional division-algebra,
embedded-field, coefficient/residue-field and fixed height-certified-frame
hypotheses, with explicit Nilp universes {v,u}. Covers may be infinite.

This is internal inverse precomposition by actual integral full-order frame
automorphisms. Descent through original framed comparisons and naturality
under varying Nilp bases remain subsequent constructions. No matrix-group
identification, full Drinfeld product-group action, Frobenius/height formula,
representability or universal object is asserted.
