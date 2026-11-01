# Countably supported function algebras

Worker 6's construction, with interface additions and source checks by Worker 345,
is a derived prerequisite motivated by the negative assertion in Renard I.5.3,
printed p.27 / PDF33 of the French version dated 9 July 2026. The registered
source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passage has been read: it warns that the original regular module of a
complex idempotented algebra need not be projective, without specifying an
example there. This construction is an implementation prerequisite for an
explicit example, not an example attributed to the book.

For a commutative ring `R` and set-type `X`, `algebra R X` is the actual
nonunital subalgebra of functions `X → R` with countable nonzero support.
`mem_algebra` gives this exact membership predicate, and `support_countable`
records it for each element.
The subtype `Carrier R X` inherits pointwise addition, multiplication and
scalar multiplication. Countable-support closure follows by containment
in the union of the supports for addition, in the first support for
multiplication, and in the original support for scalar multiplication.
No unit is adjoined. The scalar tower and scalar-commutation structures
are inherited from the actual function algebra.
The named evaluation laws `zero_apply`, `add_apply`, `neg_apply`, `sub_apply`,
`mul_apply` and `smul_apply` are definitional equalities for these inherited
operations; in particular, scalar evaluation is multiplication by the original
coefficient in `R`. The inherited structures are `NonUnitalCommRing`,
`Module R`, `IsScalarTower R` and `SMulCommClass R`.

`indicator S hS` is the characteristic function of a countable subset,
with values one and zero. `indicatorIdempotent` verifies its pointwise
idempotence. `indicator_mul_eq` and `mul_indicator_eq` prove that it fixes on
both sides every function whose support is contained in `S`.
For a family indexed by any countable type
in an independent universe, the union of the supports is countable.
Its characteristic function is the common two-sided local unit in
`countable_local_units`. Applying this to any finite subset proves exactly
the published `IsIdempotented` condition in `isIdempotented`.

If `R` is nontrivial and `X` uncountable, `no_left_identity` proves that
there is no left identity element in this algebra. A hypothetical identity
must take value one at each point, by multiplying the characteristic
function of that singleton. Its support would be the entire uncountable
base, contrary to membership in the actual carrier. This is an intrinsic
structural property, not a proof of nonprojectivity.

The coefficient, base-set and countable-family universes are independent.
The function carrier lives in their coefficient/base maximum. The
construction includes zero rings, finite and empty bases; only the
no-identity conclusion requires nontriviality and uncountability. Its
specialization to `R = ℂ` supplies the complex nonunital algebra needed by
the source convention. No assertion of nonprojectivity, no free-summand
counterexample and no claim of independent acceptance is made here.
