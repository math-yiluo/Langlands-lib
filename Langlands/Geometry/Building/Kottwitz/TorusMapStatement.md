# Existence, independence and descent of the torus Kottwitz map

Source: Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 11.1.1 and its proof, printed pp. 421–422 (PDF pp. 452–453),
and the restriction convention in Chapter 11, printed p. 420 (PDF p. 451).
The November 2024 corrections leave these assertions unchanged.

The two Prop-valued declarations in `Langlands.Geometry.Building.Kottwitz`
state unconditional obligations over the actual norm-based definitions in
`TorusMap`. No proof of either declaration is supplied.

`TorusKottwitzExistenceStatement` quantifies over every nonarchimedean local
field `F`, every coefficient field `k` with the stated normal scalar tower
into `K = UnramifiedClosure F` and `E = SeparableClosure F`, and every actual
`k`-torus. It includes `k = K`, the precise domain of Proposition 11.1.1, and
`k = F` for descent. It asserts:

- There is exactly one homomorphism satisfying the norm square for every
  finite Galois splitting intermediate field `L/K`.
- The selected `torusKottwitz` satisfies that square and is surjective over `K`.
- For every such `L`, the actual relative norm on coefficient points is
  surjective, and a homomorphism satisfies the square for that single `L`
  if and only if it is the selected homomorphism.

The final clause explicitly states both independence of the splitting
extension and uniqueness from any one norm square; norm surjectivity is
also established in the source's proof. The coefficient-field formulation
is the same assertion for the actual base change `T_K`, transported through
canonical point and cocharacter comparisons. It adds no hypothesis on the
ramification, characteristic or splitness of the original torus, and does
not give any local-field instance to `K` or `L`.

`TorusKottwitzDescentStatement` quantifies over every actual `F`-torus. It
asserts `Gal(K/F)`-equivariance of the constructed `K`-point map, unique
existence of its invariant-valued restriction to `T(F)`, and the restriction
law for the selected `torusKottwitzRational`. The fixed target is the fixed
submodule of the integral inertia quotient under the actual residual
Galois action. These are the equivariance conclusion of Proposition 11.1.1
and its immediate restriction consequence, made explicit so the epsilon
construction has no assumed map or assumed kernel.

The normalized splitting-field valuation has its separate unconditional
existence/uniqueness statement. Neither that statement nor either Kottwitz
statement is used as a hypothesis here: these are the proof targets on
which the definitions' unconditional specifications depend.
