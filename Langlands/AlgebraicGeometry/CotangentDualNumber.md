# Cotangent functionals and augmented dual-number maps

This internal algebra adapter works with commutative rings `K` and `A`, a
`K`-algebra structure on `A`, and an augmentation `r : A →ₐ[K] K`. The ring
universes are independent. Write `I = ker(r)`. No field, local-ring, finite-type,
or reducedness hypothesis is used.

`augmentationDifference r` is the `K`-linear map into `I` sending `a` to
`a - algebraMap K A (r a)`. Its composite with Mathlib's quotient map
`I → I.Cotangent = I/I²` is `augmentationCotangent r`. Both maps vanish on
constants; the difference map fixes elements of `I`, so the cotangent map on
`I` is the usual quotient map.

`augmentationCotangent_mul` proves the product rule

```text
d(a*b) = r(a) • d(b) + r(b) • d(a).
```

The proof subtracts the two representatives. Their difference is the product
`(a - r(a)) * (b - r(b))` in `I²`, with the displayed constants interpreted
through `algebraMap K A`. The quotient equality follows from Mathlib's
`Ideal.toCotangent_eq`.

For any `K`-linear functional `ell : I.Cotangent →ₗ[K] K`,
`cotangentDualNumberLift r ell` is the actual algebra homomorphism

```text
a ↦ (r(a), ell(d(a))) : A →ₐ[K] DualNumber K.
```

The product rule supplies multiplicativity. Projection to the first coordinate
recovers `r`. The lift equals the constant lift of `r` precisely when `ell = 0`:
one direction evaluates on elements of `I` and uses surjectivity of the cotangent
quotient map; the converse compares the two dual-number coordinates.

For a `K`-algebra map `f : B →ₐ[K] A`, the augmentation on `B` is `r.comp f`.
`augmentationCotangentMap r f` is Mathlib's induced map between the two
augmentation-kernel cotangent modules.
`augmentationCotangentMap_apply` proves that it carries `d(b)` to `d(f(b))`
by comparing their representatives.
`cotangentDualNumberLift_comp` then identifies the composite dual-number lift
with the lift of the composite cotangent functional.
Consequently, `cotangentDualNumberLift_comp_eq_constant_iff` says that
precomposing the lift with `f` gives the constant lift of `r.comp f` if and only
if `ell.comp (augmentationCotangentMap r f) = 0`.

This is a derived construction from Mathlib's `Ideal.Cotangent` quotient and
`DualNumber` algebra definitions. The Markdown describes the implemented
construction and proofs; no external theorem is being transcribed. It supplies
an algebraic ingredient for later tangent arguments, without asserting a
scheme-theoretic closed-immersion criterion.
