# Automorphisms of `D(X)` from automorphisms of `X`

Module `Langlands.GroupScheme.SplitExistence.TorusAut`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is the functoriality of `D(X)` in `X`,
written out on points.

## Declarations

- `precompChar w R`: precomposition of characters `Multiplicative X →* Rˣ` with an additive
  endomorphism `w` of `X`.
- `torusEndPoints k w T`: the induced endomorphism of the points of `D(X)` over a test scheme
  `T`. `torusPointsEquiv_torusEndPoints` computes it, and `torusEndPoints_naturality` says it is
  natural in `T`.
- `torusEnd k w`: the endomorphism of the group scheme `D(X)` attached to `w`, built with
  `homOfPoints`. `torusPointsEquiv_torusEnd` says it sends a point with character `χ` to the
  point with character `χ ∘ w`.
- `torusEnd_comp`: `torusEnd w' ≫ torusEnd w = torusEnd (w' ∘ w)`. `torusEnd_id`:
  `torusEnd id = 𝟙`.
- `torusAut k e : Tk k ≅ Tk k`: the automorphism of the commutative group scheme `D(X)` attached
  to an additive automorphism `e` of `X`. Its inverse is `torusEnd e⁻¹`.
- `groupHom_torusAut_hom`: the underlying group homomorphism of `torusAut e` is `torusEnd e`.
- `torusAut_inv_comp_charOf`: `(torusAut e)⁻¹ ≫ charOf x = charOf (e⁻¹ x)`, checked on points.
