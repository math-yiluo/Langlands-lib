# Prime-power monodromy when prime torsion is fixed

`Langlands.AbelianScheme.Tate.PrimeLevelMonodromyPGroupStatement` concerns an
abelian scheme over a scheme with a geometric fibre functor. For a prime `p`
invertible on the base, it assumes that the fundamental group acts trivially
on the geometric `p`-torsion. For each exponent `n` with `p^n` invertible,
the image of the action on the `p^n`-torsion is a `p`-group. The theorem
`primeLevelMonodromyPGroup` proves this proposition.

The representation `levelMonodromyHom` packages the Library's action on
actual torsion points as a homomorphism to linear automorphisms over the
residue coefficient ring. The theorem `finite_levelMonodromyImage` gives
finiteness of its image, and `continuous_levelMonodromyToImage` gives
continuity for the discrete topology on that image. These follow from
finiteness of the points and continuity of evaluation at each point.

## Proof

For two positive torsion orders with the smaller order dividing the larger,
the smaller kernel includes into the larger kernel by its universal
property. Naturality of evaluation on the corresponding covers makes
the inclusion equivariant. At level `p^n` with `n > 0`, every point
annihilated by `p` comes from this inclusion of the prime level.
Level `p^0` has only its zero point.

Let `e` be an automorphism that fixes the points annihilated by `p`. The proof
uses induction to show that `e^(p^j)` fixes each point annihilated by `p^j`.
For the induction step, put `f = e^(p^j)` and let `x` be annihilated by
`p^(j+1)`. Then `f` fixes `p • x`, so the difference `d = f x - x`
is annihilated by `p`. Hence `f` fixes `d`. Iterating `f` on `x` adds `d`
once per iteration, so the `p`-th iterate fixes `x`. With `j = n` the
result gives the `p`-power order bound on every element of the image.

This is a finite-level form of the congruence group observation in SGA 7 I,
Exposé I, Variante 1.3, p. I-7. The source uses the kernel of reduction
on an integral \(\ell\)-adic lattice. The proof here uses the
annihilator filtration on the actual finite modules. The registered source
is `deligne-1972-sga7-i-expose-i-monodromie`, SHA-256
`b5a598de1362529cd2be9f71ba17a40e07bc36cef9431f0586caa317653957ce`.
