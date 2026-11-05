# Full adelic moderate growth for actual rational-invariant functions

Let `F` be any number field, `G` the existing actual affine group scheme,
and `rho` a specified matrix representation of positive dimension.
`HasAdelicModerateGrowth` requires a positive real constant and a real
exponent bounding the function at every actual adelic argument by the
corresponding power of `adelicSourceNorm`. This is the full local-product
condition of Getz–Hahn Definition 6.3.1, printed p.161, using (6.7)–(6.8).
It is imposed here on the existing continuous rational-invariant
function carrier; independence of a faithful closed embedding remains a
separate assertion.

`HasAdelicPolynomialGrowth` uses a nonnegative constant and natural
exponent for the dimension-scaled `adelicHeight`. The module proves that
these are equivalent. In one direction the exact source norm is the
scaled height divided by a positive dimension constant. Its real power
therefore differs by a fixed scalar. Since the scaled height is at least
one, a natural exponent greater than the given real exponent bounds the
same function. Conversely, its fixed scalar relation with the source norm
transfers a natural-power bound, enlarging the constant to make it
strictly positive. This proves the source quantifier correspondence,
including negative real exponents and zero functions.

The natural-power condition is closed under zero, addition and complex
scalar multiplication. Addition uses the maximum of the two natural
exponents and the lower bound one. Positive right translation is
preserved by the proved full-height submultiplicative bound.
`adelicGrowthSubrepresentation` is thus a subrepresentation of the
unchanged continuous ambient action, with membership exactly equivalent
to the real-exponent source condition.

`finitePlotSmoothAdelicGrowthSubrepresentation` intersects this space
with the existing infinite plot-smooth/common-open-finite-stabilizer
subrepresentation. This is full adelic growth, rather than separate
bounds with constants and exponents allowed to vary with each finite
slice.

The construction composes the actual norm unit, the original continuous
adelic function carrier and elementary real-power estimates from the
pinned Mathlib. It asserts no uniform bound for all enveloping
derivatives, compact or center finiteness, automatic square integrability,
embedding independence, or equality with the full automorphic-form
space. Comparisons with the earlier fixed-finite-slice growth conditions
need additional proofs.
