# Comparing normalization in the generic fibre and in the total fraction ring

Worker 594.

For a flat `S`-algebra `D`, its localization at the image of
the non-zero-divisors of `S` embeds in the total fraction ring of `D`.
Flatness ensures that these denominators act injectively on `D`. The
embedding comes from the universal property of localization, and its
injectivity follows from the injectivity of the structure maps from `D`.

When the generic localization is integrally closed, the same embedding
induces an equivalence of integral closures. The total fraction ring of
`D` is also the total fraction ring of the generic localization. Every
element integral over `D` is integral over the generic localization,
so it belongs to that localization. The preimage is integral over `D`
by injectivity of the embedding.

To prove integral closedness from normal local rings, the proof writes
an integral fraction as `b / s`. In each localization at a maximal ideal
it belongs to the local ring. If the ideal of multipliers `t` for which
`t * b` is divisible by `s` were proper, it would be contained in a
maximal ideal. Clearing the local denominator supplies a multiplier
outside that maximal ideal, a contradiction. This proves that `s`
divides `b` already in the original ring. The smooth case uses regularity
of stalks over a field and factoriality of regular local rings.

This is a derived algebra comparison for the affine form of Conrad's
Theorem A.2 in the appendix to Prasad–Yu, *On quasi-reductive group
schemes*, author preprint, p. 28. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
