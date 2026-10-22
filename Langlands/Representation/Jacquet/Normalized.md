# Normalized Jacquet action from a supplied modulus

The constructor `normalizedActionOfModulus` takes an actual complex group
representation, subgroups `N` and `M`, a proof that `M` normalizes `N`,
and a positive character `delta : M -> NNRealˣ`. Its carrier is the actual
quotient by the span of `rho(n)v - v`. Its action is

`m * [v] = (sqrt(delta(m)))^(-1) [rho(m)v]`.

The input is a supplied modulus parameter. The constructor does not identify
an arbitrary positive character with a particular group's Haar or parabolic
modulus. The GL parabolic application must supply that identification and its
open-kernel certificate. The separate `characterTwistedAction` interface
allows arbitrary characters and is explicitly generic.

The scalar used here is the genuine multiplicative complex unit character
constructed in `PositiveCharacter.lean`. Its square is the inverse of `delta`,
and its kernel equals the kernel of `delta`. Thus an open-kernel modulus
produces a smooth inverse-half-modulus character without any root choice.
If `rho` is smooth, restriction to `M`, quotient descent, and twisting prove
smoothness of the normalized action. The only topological typeclass required
by this implication is a topology on `G`; the subgroup topologies are induced.
There is no topology or dimensional restriction on the representation carrier.

The canonical quotient map has the same underlying surjective linear map.
For equivariance its source is the restriction to `M` twisted by the same
inverse-half character. Induced maps on normalized quotients preserve
identities and composition and commute with the quotient map. These proofs
specialize the intrinsic generic-twist laws.

The direction follows Bernstein--Zelevinsky (1977), Section 1.8(b), printed
page 444, which multiplies the quotient action by `mod_U(m)^(-1/2)`, and
Casselman, Chapter III (April 29, 2019), Section 3, page 4, which uses
`delta_P^(-1/2)`. Casselman's Section 1, page 1, defines the parabolic modulus
using the absolute determinant of the action on the unipotent Lie algebra.
The opposite positive-half factor belongs to the corresponding normalized
induction convention.

For Worker 23 and the GL geometry owner, the specialization interface is
`delta : M -> NNRealˣ` plus `IsOpen (delta.ker : Set M)`, with `delta` equal to
the positive modulus itself. Supply the full modulus, not its square root
and not its inverse: this module constructs the inverse half. The quotient
input uses `M <= Subgroup.normalizer N`. All carriers have independent
universes, making the unbundled constructors usable in a later `SmoothRep`
category wrapper.

Exactness, reciprocity, admissibility and classification are not assumptions
or consequences of this contribution. They remain separate theorem obligations.

The exact source tuples are `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
Section 1.8(b), printed page 444 / PDF page 5; and
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`,
Chapter III, revision April 29, 2019, Section 1 page 1 and Section 3 pages 3--4.
Their original paths are recorded in [PositiveCharacter.md](PositiveCharacter.md).
The source identification and the scalar formula were checked in the original
PDFs, including a visual check of Bernstein--Zelevinsky printed page 444.

This is a derived generic construction for later geometric specialization.
Its actual quotient, smoothness and scalar twisting dependencies are the six
exact version-1 artifacts listed in [SmoothTwist.md](SmoothTwist.md).
The modules `SmoothTwist`, `PositiveCharacter` and `Normalized` and all their
intrinsic laws belong to this one contribution. Only `Coinvariants` belongs
to the earlier quotient-action contribution.

The quotient-action artifact `6574bc6a-331d-4a8e-b089-969b377e4598`,
version 1, is independently accepted and published at commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, with effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
Its accepted files match the dependency used by this construction.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0, Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Native compilation checks the implemented constructions and their proofs.
Independent semantic review and current publication are required separately.
