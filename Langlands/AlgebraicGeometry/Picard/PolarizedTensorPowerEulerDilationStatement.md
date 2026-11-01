# Tensor-power and Euler dilation from an actual polarization

`PolarizedTensorPowerEulerDilationStatement` groups the categorical and
cohomological consequences of an actual isomorphism
`e : (Scheme.Modules.pullback f).obj M ≅ tensorPow M q`.
Here `X` is any scheme in universe `u`, `f : X ⟶ X` is any scheme
endomorphism, `M` is an actual module sheaf on `X`, and `q` is any natural
number. No line-bundle, positivity, finiteness, or ampleness hypothesis is
required for these consequences.

The first clause asserts the existence, for every natural `n`, of both
isomorphisms

```
tensorPow (f* M) n ≅ tensorPow M (q * n)
f* (tensorPow M n) ≅ tensorPow M (q * n).
```

The pullback and tensor powers here are the actual published functors and
right-associated sheaf tensor powers; the zeroth power is the structure
sheaf. Thus the assertion includes `q = 0` and `n = 0`.

For every field `K` in universe `u` and structure morphism
`s : X ⟶ Spec K`, the second clause states that the first pair of sheaves
has finite cohomology simultaneously and that their integer Euler
characteristics agree whenever these invariants are defined.
`HasFiniteCohomology` and `eulerCharacteristic` are the published definitions
using actual relative derived sections. The morphism `f` need not commute
with `s`: the cohomological assertions compare isomorphic sheaves on the
same scheme using the same `s`.

This is a derived internal statement. Its provenance is the published
`TensorPowerIsomorphisms` constructions `tensorPowIso` and
`tensorPowMulIso`, the general `actualPullbackTensorPowIso` in
`ClosedImmersionPullbackAmpleProof`, and the isomorphism invariance in
`EulerCharacteristicBasicProof`. In particular, it needs no new comparison
of pullback with tensor powers. It isolates the dilation step needed by the
polarized native-rank task; it does not assert Euler polynomiality or a
relation between Euler leading coefficients and the native rank.
