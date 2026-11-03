# A compatible whole-torus centralizing cocharacter

Let `k : Type u` be any field, `B` a commutative group scheme over `Spec k`
whose underlying group scheme is a split torus, and `G` an affine group scheme
locally of finite type over `k`. Given an actual homomorphism `b : B.toGrp → G`
and a cocharacter `ν` of `B`, the definition
`compatibleCentralizingCocharacter hB b ν` chooses another cocharacter `η` of
the same torus with

```text
Z_G(η) = torusCentralizer b,
P_G(η) ≤ P_G(ν),
U_G(ν) ≤ U_G(η).
```

Here the ambient cocharacters denoted by `η` and `ν` are respectively
`groupHom η ≫ b` and `groupHom ν ≫ b`. The notation `Z_G`, `P_G`, and `U_G`
means exactly `Dynamic.centralizer`, `Dynamic.parabolic`, and
`Dynamic.unipotent`. The equality and both inclusions hold as subgroup functors
on every test scheme. The theorem
`compatibleCentralizingCocharacter_spec` records these three conclusions;
`IsSplitTorus.exists_compatible_cocharacter` proves their existence.

The map `b` need not be closed or injective, and the cocharacters may be zero.
There are no smoothness, connectedness, reductivity, positive-rank, perfectness,
or rational-point density assumptions. All fields and test algebras use the
arbitrary universe `u`.

The proof first chooses `τ = centralizingCocharacter hB b`, whose dynamic
centralizer equals the whole-torus centralizer. The image of `τ` commutes
with the image of `ν` because both factor through the commutative group scheme
`B`. The dominant-combination theorem `Dynamic.exists_dominant_inclusions`
therefore supplies a natural threshold `N`. For `η = N • ν + τ`, evaluation
on every test scheme gives `η(t) = ν(t^N) τ(t)`. Applying that theorem at the
threshold proves both advertised dynamic inclusions and
`Z_G(η) ≤ Z_G(ν)`.

For the remaining centralizer equality, fix any test point `g` of `Z_G(η)`.
The last inclusion places `g` in `Z_G(ν)`. The published integer submodule
`Dynamic.centralizingCocharacters b g` is closed under integer multiples and
subtraction, so it contains `η - N • ν = τ`. Thus `g` belongs to `Z_G(τ)`,
which is the whole-torus centralizer. The reverse inclusion follows from the
factorization of `η` through `B`. Choosing the resulting witness gives the
definition and its specification.

This is an internal consequence of the named coordinate-based cocharacter,
dominant-combination, and centralizing-submodule results. It does not
transcribe a separate literature statement. It supplies a compatible dynamic
refinement within a fixed split torus. Identifying a dynamic parabolic or
dynamic unipotent with rational geometric objects, constructing a rational
Levi, and proving the minimal-parabolic Levi centralizer statement remain
separate geometric obligations.
