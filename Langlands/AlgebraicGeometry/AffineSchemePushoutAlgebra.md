# Localization of a ring pullback

This module supplies internal algebra for the proof of
`Langlands.AlgebraicGeometry.AffineSchemePushoutStatement`. It uses Mathlib's
canonical subring `RingHom.pullback f g` of `B × C`, where a pair `(b,c)`
satisfies `f b = g c`.

For ring maps `f : B → D`, `g : C → D`, `f' : B' → D'`, and
`g' : C' → D'`, and algebra structures from each unprimed ring to its
primed ring, assume the two squares commute. `pullbackMap` is the induced
ring homomorphism from `f.pullback g` to `f'.pullback g'`; its two coordinate
lemmas identify it with the given algebra maps.

The associated theorem `isLocalization_pullback` takes a compatible element
`a = (aB,aC)` in the first pullback. If `B'`, `C'`, and `D'` are respectively
localizations away from `aB`, `aC`, and `f aB`, then the second pullback is a
localization of the first away from `a`, with algebra structure induced by
`pullbackMap`. The rings are arbitrary commutative rings in one universe;
neither `f` nor `g` is assumed surjective.

The implemented proof clears denominators in both coordinates of a pair
`z`. If the denominators have powers `m` and `n`, compatibility after
localization becomes an equality in `D'`. A further power `k` clears that
equality in `D`, giving the compatible numerator
`(aB^(k+n) * b, aC^(k+m) * c)` and denominator `a^(k+m+n)`.
For equality of two images, powers annihilating the two coordinate
differences are combined by addition. The image of `a` is a unit because
both its coordinates are units.

This is a derived elementary algebra construction, proved in the module.
It supports the structure-sheaf comparison in the affine pushout argument
of Stacks Project, Lemma 37.14.1 (Tag 0ET0); that source uses a
quasi-coherent sheaf argument instead of this denominator calculation.
