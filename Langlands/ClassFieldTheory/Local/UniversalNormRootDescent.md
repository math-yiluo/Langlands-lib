# Removing roots of unity using a universal-norm lift

This is a derived arithmetic support unit in arbitrary field universe `u`.
For a characteristic-zero field `K` and nonzero natural number `n`,
`rootOfUnityUnit K n` chooses a primitive unit of order `n` in the actual finite
intermediate field `radicalField K n 1`. That field is the splitting field
constructed in `KummerRadicalFields` by adjoining all roots of `X^n-1` in the
actual algebraic closure; its finite-dimensional instance is reused directly.

`exists_primitive_radicalUnit` supplies the choice. A primitive root exists in
the algebraic closure by Mathlib's enough-roots-of-unity theorem in
characteristic zero. Its power identity puts it in the root set of `X^n-1`,
and hence in the radical intermediate field. Injectivity of the field's
inclusion reflects primitivity. The primitive root is nonzero, so `Units.mk0`
turns it into a unit. `rootOfUnityUnit_primitive` records the resulting
primitive-root property for the field value of the chosen unit.

`prime_power_of_universal_lift` is a conditional bridge over an actual
`PadicField F`. For a prime `q` and a base unit `a`, it assumes the following
explicit lift: for every actual finite intermediate field `E/F.Carrier`,
there is a unit `b` in `E` with determinant norm `a`, and `b` belongs to every
norm subgroup of an actual finite abelian intermediate extension of `E`.
The theorem concludes that `a` is a `q`th power of a unit of `F.Carrier`.
The lift is an input here; this unit does not prove its existence.

The proof selects `E = radicalField F.Carrier q 1`, packages that same finite
intermediate field as a `PadicField`, and takes a universal-norm lift `b` to it.
This field contains the chosen primitive `q`th root. The proved theorem
`universalNorm_is_prime_power` therefore writes `b = c^q`. Applying the actual
determinant norm and its homomorphism power identity gives
`a = (normUnits F.Carrier E c)^q`. This argument requires neither a degree
coprimality calculation nor a claim that scalar inclusion preserves universal
norms.

The construction and bridge are derived from Mathlib's roots-of-unity API and
the preceding explicit Kummer support. Their mathematical context is Serre,
*Local Fields* (1979), XIV §2, the corollary to Proposition 7, printed page 209:
prime-order divisibility once roots of unity are in the field. The use of an
explicit universal-norm lift followed by the determinant norm is an internal
derivation, not a claim that Serre's corollary proves that lift. Independent
arithmetic and compactness arguments must discharge the lift before this
bridge yields unconditional prime divisibility or norm separation.
