# The inverse positive half-character

For a group `H`, the input `delta : H -> NNRealˣ` is a genuine multiplicative
character with strictly positive real values. The units condition excludes zero.
This is a positive-character parameter layer. In a geometric application, the
caller must identify `delta` with the relevant modulus character.

The construction first applies Mathlib's multiplicative nonnegative-real square
root and then embeds the result in the complex units. It takes the inverse of
this half-character. Its value at `h` is exactly
`(sqrt(delta(h)))^(-1)`, embedded in the complex numbers. Its square is
`delta(h)^(-1)`. The square root is the positive real square root, so there is
no choice of complex square-root branch or sign.

The inverse half-character has exactly the same kernel as `delta`: inversion
fixes the condition of being one, the real-to-complex embedding is injective,
and a nonnegative real square root is one exactly when its input is one.
Thus an open-kernel modulus supplies an open-kernel inverse half-character,
the smooth-character hypothesis consumed by the Jacquet twist construction.
No continuity of group operations is needed for this implication.

This is the explicit parameter-level implementation of the inverse-half-modulus
factor in Bernstein--Zelevinsky (1977), Section 1.8(b), printed page 444, and
Casselman, Chapter III (April 29, 2019), Section 3, page 4. It does not construct
or identify a GL parabolic modulus. That geometric instantiation is separate.

Original sources:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  Section 1.8(b), printed page 444 / PDF page 5. Original:
  `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
- `casselman-2019-jacquet-module`, SHA256
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
  Chapter III, revision April 29, 2019, Section 3, page 4. Original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

The parameter-level character construction and its kernel argument are derived
implementation, not a separately stated source theorem. There are no project
imports in this file. The exact environment is
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

The Mathlib audit found `NNReal.sqrtHom` in `Mathlib/Analysis/Real/Sqrt.lean`,
with multiplicativity and `sq_sqrt` already proved. `Units.map` lifts this
homomorphism to positive units. `NNReal.toRealHom` and `Complex.ofRealHom`
provide the scalar embedding. The homomorphism inverse supplies the inverse
half-character's action fields. Equality of kernels uses the exact square-root
and scalar-embedding identities. No analytic integral or topology on a
representation carrier enters this construction.
