# Iterated invariant derivatives along lists of directions

Module `Langlands.Geometry.Manifold.SmoothGroupListDerivative`, namespace
`Langlands.Geometry.Manifold`, for a group `G` with charted space `E` (a real normed space) and,
from `contMDiff_listDirectionalDerivative` on, a Lie group structure of order `∞`.

## Declarations

- `listDirectionalDerivative w f`: for `w = [X₁, …, Xₖ]` this is
  `groupDirectionalValue Xₖ (⋯ (groupDirectionalValue X₁ f))`, defined by `List.foldl`; the head of
  the list is applied first. `listDirectionalDerivative_nil`, `listDirectionalDerivative_cons` and
  `listDirectionalDerivative_append_singleton` record the recursion.
- `listDirectionalDerivative_leftTranslation`: iterated derivatives commute with left translation
  `f ↦ (x ↦ f (a * x))`.
- `groupDirectionalValue_const`: the invariant derivative of a constant is `0`.
- `contMDiff_listDirectionalDerivative`: iterated derivatives of smooth functions are smooth.
- `listDirectionalDerivative_add`: additivity on smooth functions.
- `listDirectionalDerivative_add_const`: along a nonempty list, adding a constant to a smooth
  function does not change the iterated derivative.
- `contMDiff_mul_complex`: products of smooth complex functions are smooth.
- `groupDirectionalValue_mul`: the product rule
  `D_X (f h) g = D_X f g * h g + f g * D_X h g` for smooth `f`, `h`.
- `exists_bound_listDirectionalDerivative_mul`: let `f b`, `h b` be smooth functions indexed by
  `b : β`, let every iterated derivative of `f b` be bounded by `C_v * wt b x` and every iterated
  derivative of `h b` by a constant `C_v`, uniformly in `b` and `x`. Then every iterated derivative
  of `f b * h b` is bounded by a constant times `wt b x`.
- `exists_bound_listDirectionalDerivative_of_quasiInvariant`: let `s` be smooth, `S` and `C` subsets
  of `G` with `C` compact and `S · C = G`, and let `s (x * a) = s a + κ_x` for `x ∈ S`. Then every
  iterated derivative of `s` along a nonempty list is bounded.

## Proofs

The algebraic lemmas are inductions on the list, generalizing the function, from the Library's
`groupDirectionalValue_leftTranslation`, `groupDirectionalValue_add` and
`contMDiff_groupDirectionalValue` (module `SmoothGroupDifferential`); the derivative of a constant is
the derivative of `mvfderiv_const`. The product rule is the Leibniz rule for manifold derivatives
(`HasMFDerivAt.mul`) applied to `h ↦ f (g * h)` and `h ↦ h' (g * h)` at the identity.

For `exists_bound_listDirectionalDerivative_mul`, induction on the list with both functions
generalized: the empty list is the product of the two bounds; for `X :: w`, the product rule writes
`D_X (f h)` as `D_X f * h + f * D_X h`, additivity splits the remaining derivative `D_w`, and the
induction hypothesis applies to the pairs `(D_X f, h)` and `(f, D_X h)`, whose iterated derivatives
are iterated derivatives of `f` and `h`.

For `exists_bound_listDirectionalDerivative_of_quasiInvariant`, write `a = x * c` with `x ∈ S` and
`c ∈ C`. By left translation and `listDirectionalDerivative_add_const`, the iterated derivative of
`s` at `x * c` equals that of `y ↦ s y + κ_x`, hence that of `s`, at `c`. The iterated derivative is
continuous, hence bounded on the compact `C`.

## Provenance

The module is internal calculus on Lie groups. It provides the estimates for derivatives of
products and of Iwasawa height pairings used in the Library's proof of smoothness of intertwining
integrals, the smoothness aspect of Mœglin–Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), II.1.6 (i).
