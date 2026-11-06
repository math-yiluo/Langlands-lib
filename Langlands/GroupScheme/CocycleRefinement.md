# Refinement and fpqc reflection of cocycle triviality

This internal construction extends the actual natural cocycles in
`Langlands.GroupScheme.TorsorCocycle`. It is intended for arguments which enlarge
a finite Galois splitting field to obtain a conjugating element. It imposes no
field, reductivity, or perfectness hypothesis.

For a morphism `r : V ⟶ U` of schemes over a fixed base, `Cocycle.refine ξ r`
evaluates `ξ` after composing each of its two cover points with `r`. Its
naturality and cocycle identities follow from those of `ξ`. A trivializing
cochain on `U` pulls back by composition with `r`.

The converse theorem `Cocycle.IsTrivial.of_refine` assumes that the underlying
scheme map of `r` is an effective epimorphism and that the map on products
`r ⊗ₘ r` is an epimorphism. If `f` trivializes the refined cocycle, then `f`
agrees on any two points with the same image in `U`: the cocycle has value one
on equal arguments, so the coboundary formula forces equality of the values of
`f`. Effective descent constructs an actual morphism `g : U ⟶ G.X` with
`r ≫ g = f`. Epimorphy on products reflects its coboundary identity at the
universal pair of points of `U`; naturality then gives that identity on every
test scheme.

`Cocycle.effectiveEpi_tensorHom` checks the product hypothesis for an fpqc map.
It applies the existing stability of quasi-compact, flat, and surjective maps
under pullback to the product map. The resulting
`Cocycle.isTrivial_refine_iff` states the unconditional equivalence of the two
triviality propositions when `r` is fpqc.

The provenance is the elementary descent argument just described, implemented
using Mathlib's effective-epimorphism descent for fpqc scheme morphisms. The
product-map proof follows the existing argument in
`Langlands.GroupScheme.NormalQuotientGroup`, generalized here from quotient
projections to arbitrary cover refinements. This pair proves only the
refinement helper; it does not assert torus cohomology vanishing, reduction of
reductive cocycles to tori, existence of inner forms, or Steinberg
quasi-splitness.
