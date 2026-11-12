# From shifted functions on points to a contradiction with geometric reductivity

Author: Worker 1502. Internal helper for the proof of
`AffineHomogeneousQuotientReductiveStatement`. It is derived from the Library's corepresented
models (`AffineCoordinates.groupSchemeIso`), its unipotent primitive-coordinate results
(`Unipotent.oneMemStable_of_isUnipotent`, `Unipotent.exists_nonzero_primitive_of_oneMemStable`,
`Unipotent.range_id_eq_bot_of_all_mem_constants`) and the integrality of smooth connected schemes
(`CharacterLatticeProof.isIntegral_of_smooth`). It does not follow a cited source.

## Evaluation lemmas (namespace `Langlands.GroupScheme.AdditiveShift`)

- `appTop_algSpec_map`, `evalAt_algSpec_map`: pulling back `(ΓSpecIso S).inv s` along
  `Spec` of an algebra map `f` gives `(ΓSpecIso S').inv (f s)`. In particular, evaluation at the
  point classified by `f` is `f` read in global sections.
- `evalAt_comp`: `evalAt (a ≫ x) b = a^*(evalAt x b)`.
- `evalAt_mul`: evaluation at `x * y` is the convolution `productMap (evalAt x) (evalAt y) ∘ Δ`,
  by `AffineLinearEmbedding.homEquiv_symm_mul`.
- `affineCls x` is the classifying algebra map of an affine point `x`. Lemmas: `affineCls_map`,
  `affineCls_comp` (naturality), `eq_algSpec_map_affineCls`, and `evalAt_affine`
  (`evalAt x = (ΓSpecIso S).inv ∘ affineCls x`).

## `isShift_of_points`

Let `j : N' ⟶ G'` be a homomorphism of corepresented groups with representing algebras `C'` and
`B`. Suppose `h : B` and `c : C'` satisfy, for every test scheme `T` and points `n` of `N'` and `x`
of `G'`, `evalAt ((n ≫ j) * x) h = evalAt x h + evalAt n c`. Then
`IsShift (affineCls j) c h 1`. The proof evaluates the identity at the universal pair of points
over `Spec (C' ⊗ B)`, classified by the two inclusions, and cancels the injective
`(ΓSpecIso (C' ⊗ B)).inv`.

## `false_of_shift_functions`

Hypotheses:

- `K` is algebraically closed and `ReductiveGeometricReductivityStatement` holds;
- `G` is pseudo-reductive;
- `N` is affine, smooth, connected and unipotent, and has a point `n ≠ 1` over some test scheme;
- `j : N ⟶ G` is any homomorphism;
- for every natural, additive function `χ` on the points of `N` there is a global function `f` on
  `G` with `f((n ≫ j) * x) = f(x) + χ(n)` on all points.

The conclusion is `False`.

Proof:

1. The nontrivial point makes some coordinate of the corepresented model `N'` nonconstant. This is
   the contrapositive of `range_id_eq_bot_of_all_mem_constants`, transported along the inverse
   isomorphism. Unipotence of `N'` and `exists_nonzero_primitive_of_oneMemStable` give a nonzero
   primitive coordinate `b`.
2. `χ(n) = evalAt (n ≫ eN⁻¹) b` is natural (`evalAt_comp`). It is additive by `evalAt_mul` and
   `Δ b = 1 ⊗ b + b ⊗ 1`. The hypothesis gives `f`, which is transported to the coordinate
   `hB = (ΓSpecIso B).hom (eG^* f)` of the model `G'` of `G`. With `j' = eN ≫ j ≫ eG⁻¹`,
   point identities for `G'` and `N'` follow, and `isShift_of_points` gives the tensor identity.
3. `C'` is a domain: `N` is integral, hence so is the isomorphic `N'.X.left = Spec C'`, and
   `ΓSpecIso` identifies `C'` with its global sections. The primitive `b` is not a scalar, because
   `ε(b) = 0` and `b ≠ 0`.
4. `false_of_isShift` applies to `G'`, which is geometrically reductive by
   `IsGeometricallyReductive.of_iso`.
