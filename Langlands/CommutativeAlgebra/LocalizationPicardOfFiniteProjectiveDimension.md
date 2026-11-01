# Conditional Picard vanishing for localizations of a local ring

The internal helper
`subsingleton_pic_localization_of_finite_projectiveDimension` concerns a
commutative Noetherian local ring `R` in an arbitrary universe `u`. It assumes
that every finite `R`-module with carrier in `Type u` has a finite categorical
projective dimension bound. Under that explicit hypothesis, it proves that
`CommRing.Pic (Localization S)` is a subsingleton for every multiplicative
submonoid `S` of `R`.

This is an internal algebraic consequence of the finite-module descent and
finite-projective-dimension localization helpers in the two imported modules.
It does not prove the homological hypothesis for regular local rings and does
not assert an unconditional regular-local Picard theorem.

The implemented proof uses `CommRing.Pic.subsingleton_iff`: it suffices to
prove that every invertible module `N` over the localization is free. Such a
module is finite. Restricting scalars from the localization to `R`, the descent
helper gives a finitely generated submodule `K` of `N` whose inclusion makes
`N` its localization. The hypothesis supplies a projective dimension bound for
`K`, which lies in the same universe as `R`. Invertibility makes `N`
projective, so the localization bridge makes `N` stably free.
`Module.free_of_isStablyFree_of_invertible` then makes `N` free.
