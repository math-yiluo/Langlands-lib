# The scalar-power torsion system of a formal module

Let `M` be a formal `O`-module law with finite coordinate type over a
commutative `O`-algebra `R`. For a scalar `π : O`, the term at `n` is the
Library's actual point functor of the kernel of `[π^n]` on `M`. The test
algebras are in the universe of `R`.

`torsionIncl` takes `m ≤ n` and includes `[π^m]`-torsion into `[π^n]`-torsion.
Its components are injective. `torsionTransition` goes from term `n` to
term `m` by multiplication by `π^(n-m)`. Both maps factor through the
existing point kernel, which gives naturality in the test algebra.
The scalar laws and the arithmetic of exponents give the identity and
composition equations for `torsionTower`, indexed by the opposite of
the natural numbers.

On each test algebra, the kernel of the transition from `m + n` to `m`
is the included `[π^n]`-torsion. Under `M.IsPiDivisible π`, every point of
the lower term of a transition lifts after an actual faithfully flat
finitely presented extension of its test algebra. The proof applies
scalar-power lifting on the formal module and uses the target torsion
equation to show that the lifted point lies in the required source term.
The divisibility condition already supplies actual finite locally free
models for the scalar-power kernels.

The construction is derived from the Library's point kernels and scalar
divisibility. For `π = p` and `n = 1`, the kernel and local lifting
calculations match the final torsion sequence in the proof of
Rapoport–Zink, *Period Spaces for p-divisible Groups*, Proposition 2.7,
printed p. 51 (PDF page 66), on an affine coordinated formal module.
The inverse system supplies the point-level transitions of the
`p`-power torsion used for Tate modules in Harris 1997, Appendix,
printed p. 115 (PDF page 41).
