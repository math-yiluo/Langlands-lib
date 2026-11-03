# Actual cotangent and Lie-kernel comparison: targets

These are unproved proposition definitions recording the bridge required in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §3.3,
printed p.107 / PDF p.133. The original identifies `Lie(G)` with the dual of
`I/I²` and explicitly uses `(s.f)(g) = f(s.g)`, so cotangent and Lie supports
have the same character labels. The precise kernel and derivation formulas below
are derived implementation obligations, not claims of published proofs.

`KernelCotangentDualityStatement` asks, for every commutative coefficient algebra,
for an `A`-linear equivalence from the existing actual identity kernel to the
`k`-linear maps from the actual augmentation cotangent to `A`. Its value on each
augmentation class is specified by `Lie.kernelDerivationEquiv` on the original
coordinate. This rules out an unrelated linear equivalence or abstract tangent
replacement. No finite-type or smoothness assumption is needed for this target.

`CotangentActionPairingStatement` asks for the equivalent duality with the
cotangent of the actual tensor-base-changed augmentation. It specifies its value
on every extended augmentation class using the same actual coordinate derivation.
For every original automorphic action and every acting `A`-point, the kernel
point obtained by acting with the constant dual-number lift must pair with a
cotangent class exactly as the original kernel point pairs with its coordinate
pullback. The target's `Y` is fixed by equality of actual scheme points; it is
not an arbitrary chosen linear action. This is a transpose pairing with direct
pullback and has no inverse acting point or inverse character.

`CotangentLieSupportStatement` asks that, for split torus actions on affine groups
locally of finite type, the constructed cotangent support equals the existing
`RelativeRoot.actionWeightSupport b ⊤`. It preserves that definition's actual
all-algebra Lie eigenvectors and span, including weight zero when present.
This is a support comparison, not an assertion that every dual of an individual
weight space is the entire corresponding cotangent space. Finite type is retained
at this source-comparison boundary; all field characteristics are allowed.

`CoordinateLieComparisonStatement` is the conjunction of these three exact proof
obligations. They remain open until proved in focused successor work. None is
assumed as a structure field of the coordinate construction, and none invokes
semigroup realization or the commutator conclusion.
