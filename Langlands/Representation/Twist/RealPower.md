# Real powers of positive characters and their representation twists

The module constructs the actual character `realPowerCharacter nu s` by applying
Mathlib's `NNReal.rpowMonoidHom` to units and then embedding positive real units
in complex units. Its value is the positive real power `nu(g)^s`, viewed in
the complex numbers. The input `nu` is an actual monoid homomorphism to
nonnegative real units, hence its values are strictly positive.

This is a derived generic construction for the norm twists used in Henniart
2002, section 2.5 (the twist convention on printed page 595) and section 2.8
(real exponents on printed page 596). It does not identify a
particular input with the residue-cardinality-normalized determinant absolute
value. That identification requires the actual local-field normalization and
general linear group constructions and is not made in this file.
The source is `henniart-2002-characterization`, fingerprint
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
The retained original is
`C:/Central-Library/Henniart--Une caracterisation de la correspondance de Langlands locale pour GL(n)--2002.pdf`;
the original pages 594--596 were read and its fingerprint checked.

The zero, unit, sum and negative exponent formulas follow from Mathlib's real
power laws. The input character's kernel lies in every real-power character's
kernel. For a group with separately continuous multiplication, an open input
kernel therefore gives an open output kernel by `Subgroup.isOpen_mono`.

`realPowerTwist` applies the scalar-twist construction on the original
complex module. Its displayed action formula, zero-twist identity, sum formula
and cancellation by the negative exponent are proved. The actual linear equivalence on intertwiner spaces and
transport of representation equivalences reuse the scalar-twist maps.
The smoothness equivalence is a specialization of the open-kernel
twist theorem. No topology or dimension assumption on either module is used.
Group and module universes are independent.

Exact project dependencies are the scalar twists
`Langlands.Representation.Twist.Definitions` and the smooth-twist proof
`Langlands.Representation.Twist.SmoothProof`, closing statement
`Langlands.TwistSmoothCompatibility`; the smoothness definitions
`Langlands.Representation.Smooth.Definitions` are transitive. The environment
is Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

For the dependency check, the exact scalar-twist source pair has
Lean hash `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`
and Markdown hash `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc`;
its publication is `3d5d019e3d023c64c9a71be49c55e1d2e47b5f41`.
The smooth-twist proof has Lean hash
`704914497f29af5abae486c96edead39aa8fa267efeae2d061016c36634cac90`
and Markdown hash `b5423ba5dfe57fe3f53686c01a19fb27df085454007505922a788e5666c8a1e4`;
its publication is `46286695a6510ca7bbbdf374984d46caeb0f43d0`.
Both were confirmed public and current at Library
`5bc58c2525e0499012801c80f17b6a9c04d57263`, with no missing or changed sources
or unavailable dependencies. Local imported source hashes agree exactly.
