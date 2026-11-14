# Actual integral polarized automorphisms

`IsPolarizationPreservingAut ... lam f` is the equation
`f.hom ≫ lam ≫ dualA f.hom = lam` for an actual automorphism
`f : CategoryTheory.Aut A`, where `dualA` is
`dualAbelianSchemeMapFromEvaluation` on the supplied constructed dual.
In ordinary composition order this is `f^vee ∘ lam ∘ f = lam`.
`polarizedAutGroup ... lam` is the subgroup of these actual integral
automorphisms. It takes no supplied abstract automorphism group.
`mem_polarizedAutGroup_iff` exposes exactly that equation.

The definitions work over any `S : Scheme.{u}` and for any actual
dual-valued homomorphism `lam`. They do not themselves require that
`lam` is a polarization. The existing tensor preservation, composition,
unit coherence, associativity, unitor comparison, symmetry and Picard-zero
pullback prerequisites, chosen dual representability and geometry, and
inverse Poincare bundle with its evaluation remain explicit. All schemes
and bundles have the same universe as in the dual construction.

The subgroup laws are proved from the published identity and
composition laws for the actual contravariant dual. Multiplication in
`Aut A` has `(f * g).hom = g.hom ≫ f.hom`, so the multiplication proof
first uses preservation by `f`, then preservation by `g`. The inverse
proof composes the original equation with `f.inv` and its actual dual,
then cancels the two inverse pairs.

`polarizedAutRationalization` is the group homomorphism obtained by
restricting `Functor.mapAut A (rationalization S)` to this subgroup.
Its output is an automorphism of the actual rationalized abelian scheme,
that is, an invertible element of the existing rational Hom category.
The `_hom` and `_inv` lemmas identify its two maps with `homToHom0`
of the original integral homomorphism and its inverse.

`polarizedAutRationalization_preserves` proves the actual rational
dual-pullback equation with the rationalization of the same `lam`.
It requires the existing endpoint-specific `DualSchemeMapAdditivity`
used to construct rational dualization. Its proof applies the published
`rationalDualPullbackHom0_homToHom0` and then rationalizes the integral
preservation equation. `polarizedAutRationalization_multiplier_one`
expresses this as multiplier one using the existing
`IsRationalDualPullbackMultiple`. No Tate-pairing equation replaces the
actual geometric equation.

The source for the integral automorphism equation and group is
J. S. Milne, *Abelian Varieties* (1986 article, author corrected revision
January 2, 2022), Proposition 17.5 and its proof, printed/PDF p.37,
registered source `milne-abelian-varieties-1986-author-2022`.
The complete registered errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25` states that the retained
author version incorporates all listed corrections. The rationalization
bridge is an internal consequence of the Library's actual integral and
rational dual constructions. This module makes no claim that all
polarization-preserving rational self-isogenies form a finite group.
