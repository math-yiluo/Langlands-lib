# Unconditional divisibility and finite-index containment of universal norms

`Langlands.LocalClassField.UniversalNormFiniteIndexContainment` states that,
for every prime, every actual p-adic field in an arbitrary carrier universe,
and every finite-index subgroup of its multiplicative group, that subgroup
contains the universal norm subgroup. The latter is the intersection of the
actual determinant-norm subgroups of finite abelian intermediate extensions
in the chosen algebraic closure. The definition and its proof impose no
additional arithmetic or topological hypothesis.

This is an internal derived consequence of `UniversalNormDivisibility` and
`NormExistenceUniversalLift`. The first module proves divisibility conditional
on global universal-norm lifting, downward directedness of the actual norm
family, and closedness in supplied topological data. The second proves all
three inputs. The present module composes these results and uses the field's
canonical topological data internally, so its exported conclusions require
no supplied topology.

`universalNorm_prime_root_mem` applies the proved inputs to the conditional
prime-root theorem. For every prime order and every universal norm, its
root is again a universal norm. `universalNorm_all_roots` applies the same
inputs to the conditional theorem for every positive natural order. In the
imported proof, compact power fibers and downward directed closed norm
subgroups give a simultaneous prime root, and induction on prime factors
gives the general root.

`universalNorm_le_finiteIndex F H` applies the general subgroup lemma to this
divisibility result. Given a universal norm, take a root of order `H.index`.
The index is nonzero because `H` has finite index. The power of that root
belongs to `H` by the finite quotient power identity, and equals the original
element. Every subgroup of this commutative multiplicative group is normal,
as required by that identity. Openness of `H` is not required.
`universalNormFiniteIndexContainment` packages this conclusion over all primes
and p-adic fields of the arbitrary carrier universe.

The underlying lifting result uses maximal abelian norm reduction and a finite
normal closure, then a compact norm fiber to lift to the intersection of all
upper norm groups. These inputs are proved in the imported supporting modules;
they are not premises of this module's theorems. No reciprocity map or norm
correspondence is assumed.

This module supplies finite-index containment. The host task's exact
unconditional separation theorem still requires its separately proved topology
separation result and final assembly.
