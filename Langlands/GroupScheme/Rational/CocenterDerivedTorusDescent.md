# Actual based cocenter descent from compatible derived tori

Author: Worker 1632.

This internal construction works over any field `k` and any field extension
`E/k`, both in arbitrary universe `u`. The actual maps `t : T → M`,
`j : M → G`, `d : D → M` and `q : M → Q` are defined over `k`.
The groups `G`, `M` and `D` are affine and locally of finite type, `M` is
connected reductive, `d` exhibits its full derived subgroup, and `q` is a
supplied commutative fppf quotient by the full actual range of `d`.

Over `E`, `T` and `Q` are split, the actual base change of `t` is a maximal
torus of `M_E`, and the actual base change of `t ≫ j` is closed in `G_E`.
A supplied split maximal torus `a : S → D_E` maps compatibly to `T_E` by
an actual homomorphism `φ`. Semisimplicity of `D_E` remains an explicit
input. Actual root data `P`, `R` and `U` describe the ambient torus in
`G_E`, the same torus in `M_E`, and `a` in `D_E`, respectively.
Only the ambient datum `P` has an explicitly finite root index and is
required to be reduced. Its indices lie in universe `u`; the other two
root-index universes are independent.

The same supplied integral coweight `ν` of `T_E` is fixed by the ordinary
cocharacter Galois action, and the actual `M_E` roots are precisely the
actual ambient roots with zero integral pairing against `ν`.
Scheme surjectivity of `D_E × T_E → M_E` and the torus property of the
entire scheme-theoretic intersection `T_E ×_{M_E} D_E` remain explicit
structural inputs.

`cocenterRootDescentOfDerivedTorus` constructs a genuine base `B` of `P`
with `CocenterRootDescentData` for the simple subset
`{p : B.support | P.root' p ν = 0}` and the actual descended map
`Additive.ofMul (t ≫ q) : T → Q`. It assumes neither a coroot-span equality
nor a description of the character pullback image.

The proof transports connected reductivity and the full derived-subgroup
predicate from `k` to `E` by the published field-extension theorems.
The supplied fppf quotient transports by actual base change and the
range-base-change identity. Functoriality identifies its torus restriction
with the actual base change of `t ≫ q`. The imported actual coweight
character comparison now proves injectivity and the exact character
image as the annihilator of all ambient zero-root coroots. Supplying
these two proved facts to `coweightCocenterRootDescent` constructs the
base and all pairing, simple-coroot and ordinary-Galois correction
identities. The correction fixes the entire actual pullback image.

The provenance is this composition of the imported proved constructions;
no literature theorem is transcribed. No algebraic closedness, perfection,
characteristic, simple connectedness or integral coroot-generation
hypothesis is added. Finiteness or Galoisness of `E/k` is unnecessary for
this construction. It does not construct the compatible tori or root data,
prove semisimplicity of `D_E`, discharge the product or intersection inputs,
or construct the fixed coweight and its actual root-zero geometry.
It therefore supplies a conditional component of the unchanged
unconditional Levi cocenter root-model target.
