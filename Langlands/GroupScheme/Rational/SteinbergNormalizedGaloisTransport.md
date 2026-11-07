# Subgroup, torus and affine laws for actual semilinear root transport

These are internal consequences of the Library's canonical descent, actual
character transport, vector coordinates and polynomial evaluation. No new
assertion from Steinberg or Borel–Springer is used. The fields `k` and `K` and
all schemes lie in an arbitrary universe `u`; neither perfectness nor infinitude
is assumed.

`descentPoint_inv` proves that canonical descent preserves inversion, by
injectivity of the ordinary base-change point comparison and its group law.
`descentPoint_comp_torusIso` takes an actual commutative group `T` over the
original base, an acting group `T'` after base change, and a supplied isomorphism
between `T'` and the base change of `T`. If the supplied inclusion square
commutes, descent of an included `T'` point is the inclusion of the descended
point transported back through that isomorphism. The proof uses the inverse
inclusion square and naturality with respect to the base-changed homomorphism.

`RelativeRoot.subgroup_changeTorus_eq` identifies the entire intrinsic root
subgroup functors when the acting group changes by a supplied isomorphism and
the inclusion square commutes. It specializes the existing subgroup-comap
transport identity to the identity ambient isomorphism and removes that
identity comap, retaining every scheme test.

`VectorGroup.charValue_galois_congr` expresses transport of a character after
an actual comparison of the acting commutative groups. Its explicit premise
identifies the second transported character with the Galois image of the
first. Applying the existing character-transport point theorem and taking
unit values gives the formula; cancellation of the comparison with its inverse
recovers the original character evaluation.

`VectorGroup.ScalarDescentCompatible` is a Prop-valued definition for two
standard additive-line homomorphisms `f` and `f'`. It requires canonical
descent of the `f'` point at every global scalar on every scheme test to
equal the `f` point at that same scalar on the changed-structure test.
Two generic lemmas take these homomorphisms and this scalar descent law
written explicitly; this equivalent spelling avoids expensive kernel reduction
when specializing the constructed morphisms. Keeping
these homomorphisms as parameters avoids expensive reduction of constructed
morphism projections in the kernel. `galoisTestPoint_of_scalar_descent`
precomposes the scalar descent law with `Lie.galoisTestIso.inv`; scalar-point
naturality and the identity underlying test scheme give the twisted affine
formula. `torus_equivariant_of_scalar_descent` additionally takes the actual
commuting inclusion square, transported-character identity, and all-test
torus equivariance of `f`. Injectivity of canonical descent, its multiplication
and inversion laws, and the two torus-comparison formulas prove the same
identity for `f'` with the transported character.

For an affine group `G` over `k`, a supplied split pinning `p` of its actual
`K`-base change, a supplied normalized simple-root map `x`, and a supplied
`k`-algebra automorphism `σ`, `galoisHom_galoisTestPoint` applies the generic
scalar descent result to the already constructed actual whole root transport
`x.galoisHom`. `galoisHom_affinePoint` then compares affine base change with
the twisted test and uses `coefficientCurve_evaluate`. Its polynomial
evaluation map explicitly has target `Lie.GaloisTestAlgebra σ A`: the
underlying ring is `A`, while its `K`-algebra structure is precomposed with
`σ`. This retains coefficient conjugation, including on nonreduced tests.

Given an actual descended acting group, its comparison with `p.torus`, the
commuting inclusion square, and an explicit identity carrying the original
root character to a specified simple-root character, `galoisHom_represents_root`
identifies the canonically transported whole root subgroup with that specified
root subgroup. It uses the change-of-torus identity and the existing Galois
subgroup transport theorem. `galoisHom_torus_equivariant` specializes the
generic equivariance result to `x.torus_equivariant` and the proved scalar
descent formula. Thus the torus identity holds for every scheme test and every
global scalar.

This contribution does not yet prove the transported derivative law or package
a normalized parametrization at the specified root. It does not construct a
Galois-compatible pinning or root-map family, prove orbit orthogonality,
construct a cross-section, or prove the parent quotient proposition. In
particular no exceptional even-type-A global section is asserted. The supporting semilinear-root-map module is imported from the published
Library.
