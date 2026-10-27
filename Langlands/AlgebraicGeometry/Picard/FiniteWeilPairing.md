# The actual product-scheme map underlying finite Weil evaluation

This internal unit constructs an actual morphism over the base scheme from
the existing intrinsic evaluation on torsion points. It imports
`FiniteWeilEvaluation` and `DualKernelCharacterNaturality`. Its inputs remain
the same quasi-separated base, abelian scheme, `HasDualScheme` witness,
seven explicit dual-constructor propositions, and actual inverse line bundle
with its tensor evaluation isomorphism. It adds no geometric assumption and
accepts no character, pairing or naturality law as data.

For any natural number `n`, the primal group is the existing scheme-theoretic
kernel of `[n]` on the abelian scheme. The dual group is the existing
scheme-theoretic `n`-torsion of `dualCommGroupSchemeFromEvaluation`.
The target `mu S n` is the actual multiplication kernel on the multiplicative
group over `S`. No finiteness or invertibility of `n` is needed here, and zero
is allowed.

`dualTorsionCharacter_restrict` proves that the particular character attached
to an actual dual-torsion point restricts in the existing Cartier character
presheaf. A dual-torsion point is composed with the inverse of
`relativeDualMultiplicationKernelIso`; associativity identifies restriction
of this composite with the composite of the restricted point. The imported
`dualKernelPointCharacter_restrict` then gives the required equation.

`finiteWeilValue_restrict` combines that character equation with the
published `Cartier.muEvaluation_restrict`. For every arrow `b : U → T`
over `S`, evaluation on `b ; x` and `b ; y` equals `b` followed by evaluation
on `x,y`. This holds on every test scheme, including nonreduced schemes.

`finiteWeilPairing n` evaluates `finiteWeilValue` on the two universal
projections of the product in `Over S`. Thus it is an actual scheme morphism
over `S` from the product of primal and dual torsion to `mu S n`.
The product in `Over S` is the product over the base, not a product of
abstract point sets. `finiteWeilPairing_points` uses the restriction theorem
and the two product projection equations to identify its value on every
pair of scheme-valued points with the already constructed intrinsic value.
`finiteWeilPairing_unique` tests a competing morphism on the universal pair
of projections, which proves uniqueness from this same evaluation formula.

`finiteWeilPairing_one_left` and `finiteWeilPairing_mul_left` transfer the
existing primal-variable homomorphism laws through that evaluation equation.
Their quantifiers range over all test schemes and all primal and dual
points. They do not yet assert a homomorphism law in the dual variable.

The provenance is internal: composition of the actual dual-kernel
naturality, the relative dual-multiplication kernel comparison, canonical
root-valued Cartier evaluation, and the universal property of the product.
The evaluation order and normalization remain `beta(y)(x)`, with no inversion
or choice of roots of unity. This supplies the actual scheme map and its
test-scheme naturality and primal-variable group laws. Dual-variable
additivity, Cartier duality and perfectness, polarization and alternation,
transition laws, monodromy and inverse-limit pairings remain separate
obligations.
