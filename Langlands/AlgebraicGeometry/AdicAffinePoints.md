# Affine points over an adically complete ring

This internal affine-scheme lemma supplies the point-limit step in the proof of
SGA 3, Exposé IX, Corollaire 7.3 (Gille–Polo recomposed edition, 2009, p.59,
margin p.72; registered source `sga3-expose-ix-gille-polo-2009`). It is also useful
independently of group schemes.

For a commutative ring `A` and ideal `I`, `quotientSpec I n` is
`Spec(A/I^(n+1))`, `quotientMap I n` is its map to `Spec A`, and `transition I n`
is its map to the next thickening. `reduction` and `transitionOver` express the
same maps in the category of schemes over `Spec A`. The transition triangles
commute.

For an affine scheme `X`, `adic_ext` proves that two maps `Spec A → X` are
equal if their restrictions to all these quotients agree, assuming only
`IsHausdorff I A`. Under `IsAdicComplete I A`, `exists_adic_lift` and
`existsUnique_adic_lift` prove that each compatible family of such maps has a
unique lift. The ideal is arbitrary; locality, noetherianity, and finite type
are not needed.

The proof identifies `X` with the spectrum of its global sections. It converts
the family of scheme maps to compatible ring homomorphisms, uses Mathlib's
`IsAdicComplete.StrictMono.liftRingHom` for the strictly increasing exponents
`n+1`, and converts back to schemes. Uniqueness uses
`IsHausdorff.StrictMono.funext'` on the coordinate ring maps.

`over_adic_ext` and `existsUnique_over_adic_lift` give the corresponding
statements for sections of an affine scheme over `Spec A`. The latter first
lifts the underlying maps, and then checks the triangle over `Spec A` on every
quotient by `adic_ext`. These results concern actual morphisms in the over
category, so they apply to compatible group-valued points without any choice
of coordinates in their conclusion. They do not assert effectivity for
homomorphisms whose source is a group of multiplicative type.
