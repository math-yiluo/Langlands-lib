# Homomorphism descent through an fpqc group-scheme quotient

This internal derived construction descends a group-scheme homomorphism
`f : H → G` through a specified quasi-compact, flat, surjective homomorphism
`q : H → Q` when `kernelι q ≫ f = 0`. The kernel is the full actual
scheme-theoretic kernel; no reducedness or smoothness is assumed.

The implementation divides two points with the same quotient image and
uses the actual kernel pullback to prove that their images under `f` agree.
This gives the relation required by Mathlib's `EffectiveEpi.desc` for the
underlying fpqc scheme morphism. Cancellation proves that the descended
morphism is over the base. The unit law follows by composition with `q`;
the multiplication law follows by cancelling the fpqc product `q × q`.
`FpqcHomDescent.hom` bundles the resulting group-scheme homomorphism,
`fac` proves its composite with `q` equals `f`, and `unique` proves its
uniqueness.

The base and all group schemes are arbitrary in the same universe. No
quotient is constructed: `q` and `Q` are inputs. This is derived from the
published kernel API and pinned Mathlib's fpqc effective epimorphism API.
The argument generalizes the descent of a kernel-annihilating multiplication
map in `Langlands.AbelianScheme.IsogenyInverse`; it also follows the relation
and cancellation pattern of `Langlands.GroupScheme.ActionDescent`.
