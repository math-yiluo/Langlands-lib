# Cotangent surjectivity for a finite local algebra map

`Langlands.CommutativeAlgebra.FiniteLocalCotangentSurjectivityStatement` is
an internally derived proposition about augmented local algebras. It is stated
here, without a proof.

Let `K` be any field, and let `A` and `B` be commutative local `K`-algebras.
The underlying types of `K`, `A`, and `B` lie in independent universes `u`, `v`,
and `w`. Assume `B` is Noetherian. Let `r : B →ₐ[K] K` be an augmentation and
`f : A →ₐ[K] B` a homomorphism of `K`-algebras.

The proposition locally installs `f.toRingHom.toAlgebra` as the `A`-algebra
structure on `B`. Thus `a` acts on `b` as `f(a) * b`, and the premise
`Module.Finite A B` means finiteness for this actual action. It is not a
finiteness assumption for a separately supplied algebra structure.

Write `mA = ker(r.comp f)` and `mB = ker(r)`. Since an augmentation is a
`K`-algebra homomorphism, `r(algebraMap K B c) = c` for every `c : K`;
the same holds for `r.comp f` and the scalar map into `A`. Both augmentations
are therefore surjective. Their kernels are the maximal ideals of the local
rings, as expressed by Mathlib's `IsLocalRing.ker_eq_maximalIdeal`. They identify
the residue fields `A/mA` and `B/mB` with `K`. The equality
`r(f(a)) = (r.comp f)(a)` makes the residue-field map induced by `f` the
identity under these identifications. In particular, `f` carries the maximal
ideal of `A` into that of `B`, with preimage exactly the maximal ideal of `A`.
These facts follow from the given augmentations; they are not extra premises.

The second premise is surjectivity of the actual `K`-linear map
`Langlands.AlgebraicGeometry.augmentationCotangentMap r f`:

```text
mA / mA²  →  mB / mB².
```

This map sends the class of `a ∈ mA` to the class of `f(a) ∈ mB`. Its direction
is from the cotangent space of the source algebra `A` to that of the target
algebra `B`. It is the map constructed from `f` by the published module
`Langlands.AlgebraicGeometry.CotangentDualNumber` using `Ideal.mapCotangent`.
With the finiteness premise above, the asserted conclusion is
`Function.Surjective f`.

There is no restriction on characteristic, and neither algebra is required to
be reduced or of finite type over `K`. The field need not be algebraically
closed. Locality of both rings, Noetherianity of `B`, and finiteness of `B` as
an `A`-module through `f` remain explicit hypotheses. No supplied
surjectivity, residue-field, or closed-immersion certificate is used.

The formulation and initial checked draft are due to Worker 487; Worker 362
reused that draft and expanded this explanation for publication. This is an
internal supporting statement for the local closed-immersion lane of parent
task `246ddac8-b03d-4618-8bf3-1e1908ee0ad9`, rather than a transcription of an
external theorem. Its suggested derivation applies Nakayama over `B` to its
maximal ideal, then over `A` to the finite module `B` and the image of `f`.
That derivation is not implemented in this statement module. The module makes
no assertion about scheme morphisms and does not assume a scheme immersion
criterion, a very-ampleness criterion, or the existence of ample line bundles.
